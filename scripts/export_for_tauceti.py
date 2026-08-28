#!/usr/bin/env python3
"""Deterministic staging -> Tau Ceti export tool.

Copies a `ForTauCeti.*` staging cluster into a Tau Ceti checkout, applying
exactly one class of transformation: rewriting sibling module imports
`ForTauCeti.X` -> `TauCeti.X` and mapping the file path
`ForTauCeti/X.lean` -> `<tauceti>/TauCeti/X.lean`. Everything else —
declaration namespaces, provenance, copyright header, proof bodies — is copied
verbatim (declarations already carry their final `TauCeti`/`ContinuousLinearMap`
names, so no body rewrite is needed).

This is NOT a general Lean source-to-source rewriter. The only edits are on
`import` lines. The tool:

  * reads the extraction manifest (dev/tauceti/extraction-manifest.json);
  * refuses to export a module that still has a forbidden import
    (anything other than Mathlib / TauCeti after the rewrite);
  * refuses to overwrite a Tau Ceti file that is not a declared export target
    of the manifest (protecting unrelated Tau Ceti files);
  * supports `--check` (verify the Tau Ceti copy matches the transformed
    staging source) and `--write` (perform the copy);
  * reports every file and declaration name exported.

The Tau Ceti checkout is an explicit, optional input; this repository no longer
carries one as a submodule. `--check` may read the Lake package copy, but
`--write` demands an editable checkout the operator controls: Lake's package
directory is a cache, is not a Git working tree anyone should commit into, and
`lake update` may replace it without warning.

Usage:
    python3 scripts/export_for_tauceti.py --cluster approximation-number --check
    python3 scripts/export_for_tauceti.py --cluster approximation-number --write \
        --tauceti-root ~/code/TauCeti
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from _external_checkouts import MissingCheckout, tauceti_root  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "dev/tauceti/extraction-manifest.json"

#: Resolved in `main()`. Rebound by tests. There is no in-repository default: a
#: Tau Ceti checkout is an explicit optional input, not part of this repository.
TAUCETI_ROOT: pathlib.Path | None = None

IMPORT_RE = re.compile(r"^(\s*)((?:public\s+|private\s+|meta\s+)*import\s+)([A-Za-z0-9_.]+)(.*)$")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
    r"(def|theorem|lemma|abbrev|structure|instance|inductive|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)

ALLOWED_AFTER_REWRITE = ("Mathlib", "TauCeti")


def module_to_staging_path(module: str) -> pathlib.Path:
    assert module.startswith("ForTauCeti."), module
    return ROOT / (module.replace(".", "/") + ".lean")


def staging_module_to_target(module: str, final_module: str | None) -> tuple[str, pathlib.Path]:
    """Return (final_module_name, target_file_path)."""
    if final_module is None:
        final_module = "TauCeti." + module[len("ForTauCeti."):]
    assert final_module.startswith("TauCeti."), final_module
    rel = final_module.replace(".", "/") + ".lean"
    return final_module, TAUCETI_ROOT / rel


def rewrite_imports(text: str) -> tuple[str, list[str]]:
    """Rewrite `import ForTauCeti.X` -> `import TauCeti.X`. Return (new_text,
    forbidden_imports_remaining)."""
    out_lines = []
    forbidden: list[str] = []
    for line in text.splitlines():
        m = IMPORT_RE.match(line)
        if not m:
            out_lines.append(line)
            continue
        indent, kw, mod, rest = m.groups()
        if mod == "ForTauCeti" or mod.startswith("ForTauCeti."):
            mod = "TauCeti." + mod[len("ForTauCeti."):] if mod != "ForTauCeti" else "TauCeti"
        top = mod.split(".", 1)[0]
        if top not in ALLOWED_AFTER_REWRITE:
            forbidden.append(mod)
        out_lines.append(f"{indent}{kw}{mod}{rest}")
    trailing = "\n" if text.endswith("\n") else ""
    return "\n".join(out_lines) + trailing, forbidden


def declaration_names(text: str) -> list[str]:
    names = []
    for line in text.splitlines():
        m = DECL_RE.match(line)
        if m:
            names.append(m.group(2))
    return names


def load_manifest(path: pathlib.Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def final_module_for(manifest: dict, staging_module: str) -> str | None:
    for rec in manifest.get("records", []):
        if rec.get("staging_module") == staging_module:
            return rec.get("final_tauceti_module")
    return None


def cluster_staging_modules(manifest: dict, cluster: str | None) -> list[str]:
    mods: list[str] = []
    for c in manifest.get("clusters", []):
        if cluster is None or c.get("cluster") == cluster:
            mods.extend(c.get("staging_modules", []))
    return mods


def all_target_modules(manifest: dict) -> set[str]:
    out = set()
    for staging in cluster_staging_modules(manifest, None):
        final, _ = staging_module_to_target(staging, final_module_for(manifest, staging))
        out.add(final)
    return out


class Result:
    def __init__(self) -> None:
        self.ok = True
        self.lines: list[str] = []

    def log(self, msg: str) -> None:
        self.lines.append(msg)

    def fail(self, msg: str) -> None:
        self.ok = False
        self.lines.append("ERROR: " + msg)


def run(manifest: dict, cluster: str | None, write: bool) -> Result:
    res = Result()
    staging_modules = cluster_staging_modules(manifest, cluster)
    if not staging_modules:
        res.fail(f"no staging modules for cluster {cluster!r}")
        return res
    protected = all_target_modules(manifest)

    for staging in staging_modules:
        src = module_to_staging_path(staging)
        if not src.is_file():
            res.fail(f"{staging}: staging file missing ({src})")
            continue
        text = src.read_text(encoding="utf-8")
        new_text, forbidden = rewrite_imports(text)
        if forbidden:
            res.fail(f"{staging}: forbidden import(s) after rewrite: "
                     + ", ".join(forbidden))
            continue
        final, target = staging_module_to_target(
            staging, final_module_for(manifest, staging))
        decls = declaration_names(new_text)

        if write:
            if target.exists():
                existing = target.read_text(encoding="utf-8")
                if existing == new_text:
                    res.log(f"UNCHANGED {final} ({len(decls)} decls)")
                    continue
                if final not in protected:
                    res.fail(f"{final}: refusing to overwrite unrelated "
                             f"Tau Ceti file {target}")
                    continue
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(new_text, encoding="utf-8")
            res.log(f"WROTE {final} -> {target.relative_to(TAUCETI_ROOT)} "
                    f"({len(decls)} decls: {', '.join(decls[:6])}"
                    f"{'...' if len(decls) > 6 else ''})")
        else:
            if not target.exists():
                # A module we add rather than update is absent upstream by
                # definition, so absence is not drift.  `--write` creates it.
                res.log(f"NEW {final} ({len(decls)} decls) -> "
                        f"{target.relative_to(TAUCETI_ROOT)}")
                continue
            existing = target.read_text(encoding="utf-8")
            if existing == new_text:
                res.log(f"MATCH {final} ({len(decls)} decls)")
            else:
                res.fail(f"{final}: Tau Ceti copy differs from transformed "
                         f"staging source ({target})")
    return res


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cluster", default=None,
                    help="cluster name from the manifest (default: all)")
    ap.add_argument("--manifest", default=str(MANIFEST_PATH))
    ap.add_argument("--tauceti-root", default=None,
                    help="path to a Tau Ceti checkout (or set TAUCETI_ROOT); "
                         "--write requires an editable one")
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true",
                      help="verify Tau Ceti copies match staging sources")
    mode.add_argument("--write", action="store_true",
                      help="write transformed staging sources into Tau Ceti")
    args = ap.parse_args(argv)

    global TAUCETI_ROOT
    try:
        TAUCETI_ROOT = tauceti_root(
            args.tauceti_root, require_editable=args.write, required=True
        )
    except MissingCheckout as exc:
        print(f"export: FAILED\n{exc}", file=sys.stderr)
        return 1

    manifest = load_manifest(pathlib.Path(args.manifest))
    res = run(manifest, args.cluster, write=args.write)
    for line in res.lines:
        print(line)
    print("export:", "OK" if res.ok else "FAILED")
    return 0 if res.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
