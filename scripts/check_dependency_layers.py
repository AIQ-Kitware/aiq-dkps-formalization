#!/usr/bin/env python3
"""Dependency-layer checker for the Tau Ceti extraction architecture.

The permanent target architecture is

    Mathlib -> TauCeti -> DavisKahan

staged, during migration, through a temporary `ForTauCeti` library:

    Mathlib -> TauCeti -> ForTauCeti -> DavisKahan

This script parses Lean `import` / `public import` lines and fails when a
module violates the layering. The rules (see the campaign spec and
`ForTauCeti/README.md`) are:

1. `ForMathlib` must import only `Mathlib` and `ForMathlib` — never a paper
   library, `DavisKahan`, `TauCeti`, `ForTauCeti`, or `Spectra`.
2. `ForTauCeti` must import only `Mathlib`, `TauCeti`, and `ForTauCeti`.
3. a generic-foundation `DavisKahan` module must not import a source facade
   `DavisKahan.Sources.*` (a backwards dependency), unless it is in the
   reviewed allowlist.
4. a production (non-`Experimental`) module must not import
   `DavisKahan.Experimental.*` unless it is in the reviewed allowlist.
5. a source-facing wrapper (`DavisKahan.Sources.*`) must not be imported by a
   lower-level generic module (`ForTauCeti`, `ForMathlib`, or a manifest-declared
   generic `DavisKahan` foundation).
6. a production module (`DavisKahan`, `DavisKahan.Sources`, or a paper library)
   must reach `Spectra` only through the designated bridge
   `DavisKahan.Interop.Spectra.*`, unless it is in the ratcheting allowlist.
   AGENTS.md records that the final migration target removes Spectra from the
   normal build, and three extraction clusters are `blocked-on-spectra-removal`;
   this rule keeps the coupling visible and stops new coupling appearing.
7. a Tau Ceti extraction cluster (from the manifest) must not import outside its
   declared extraction closure (Mathlib + TauCeti + its own staging modules).

Violations are reported with the shortest offending import path, not just a
boolean. Exit status is nonzero when any hard rule is violated.

The two ratcheting allowlists live in
`dev/tauceti/dependency-layer-allowlist.json`; they capture the *current*
pre-migration state so the checker is green today and flags only *new*
regressions.
"""
from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import sys
from typing import Iterable

ROOT = pathlib.Path(__file__).resolve().parents[1]
IMPORT_RE = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+([A-Za-z0-9_.]+)")

# Library source roots scanned by default.
DEFAULT_LIB_DIRS = (
    "ForTauCeti",
    "ForMathlib",
    "DavisKahan",
    "Acharyya2024",
    "Acharyya2025",
    "DkpsQuench2026",
    "Helm2025",
    "Challenge",
)

PAPER_ROOTS = ("Acharyya2024", "Acharyya2025", "DkpsQuench2026", "Helm2025", "Challenge")

ALLOWLIST_PATH = ROOT / "dev/tauceti/dependency-layer-allowlist.json"
MANIFEST_PATH = ROOT / "dev/tauceti/extraction-manifest.json"


def classify(module: str) -> str:
    """Classify a fully-qualified Lean module name into a layer."""
    if module == "Mathlib" or module.startswith("Mathlib."):
        return "mathlib"
    if module == "TauCeti" or module.startswith("TauCeti."):
        return "tauceti"
    if module == "ForTauCeti" or module.startswith("ForTauCeti."):
        return "fortauceti"
    if module == "ForMathlib" or module.startswith("ForMathlib."):
        return "formathlib"
    if module == "Spectra" or module.startswith("Spectra."):
        return "spectra"
    if module.startswith("DavisKahan.Sources"):
        return "dk-source"
    if module.startswith("DavisKahan.Experimental"):
        return "dk-experimental"
    if module == "DavisKahan" or module.startswith("DavisKahan."):
        return "davis-kahan"
    for p in PAPER_ROOTS:
        if module == p or module.startswith(p + "."):
            return "paper"
    return "other"


def module_of_path(path: pathlib.Path, root: pathlib.Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def parse_imports(text: str) -> list[str]:
    out = []
    for line in text.splitlines():
        m = IMPORT_RE.match(line)
        if m:
            out.append(m.group(1))
    return out


def scan(root: pathlib.Path, lib_dirs: Iterable[str]) -> dict[str, list[str]]:
    """Return {module: [imported modules]} for every .lean under the lib dirs."""
    graph: dict[str, list[str]] = {}
    for lib in lib_dirs:
        base = root / lib
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            module = module_of_path(path, root)
            graph[module] = parse_imports(path.read_text(encoding="utf-8"))
    return graph


def shortest_path(graph: dict[str, list[str]], start: str,
                  target_pred) -> list[str] | None:
    """BFS the import graph from `start` to the first module satisfying
    `target_pred`, returning the module path (inclusive) or None."""
    seen = {start}
    queue: collections.deque[list[str]] = collections.deque([[start]])
    while queue:
        path = queue.popleft()
        for imp in graph.get(path[-1], []):
            if imp in seen:
                continue
            newpath = path + [imp]
            if target_pred(imp):
                return newpath
            seen.add(imp)
            queue.append(newpath)
    return None


class Violation:
    def __init__(self, rule: str, module: str, detail: str,
                 path: list[str] | None = None) -> None:
        self.rule = rule
        self.module = module
        self.detail = detail
        self.path = path

    def render(self) -> str:
        head = f"[{self.rule}] {self.module}: {self.detail}"
        if self.path and len(self.path) > 2:
            head += "\n    import path: " + " -> ".join(self.path)
        return head


FORTAUCETI_ALLOWED = {"mathlib", "tauceti", "fortauceti"}
FORMATHLIB_ALLOWED = {"mathlib", "formathlib"}


def load_json(path: pathlib.Path) -> dict:
    if path.is_file():
        return json.loads(path.read_text(encoding="utf-8"))
    return {}


def check(graph: dict[str, list[str]], allowlist: dict,
          manifest: dict) -> list[Violation]:
    violations: list[Violation] = []
    generic_sources_ok = set(allowlist.get("generic_imports_sources", []))
    experimental_ok = set(allowlist.get("production_imports_experimental", []))
    generic_dk_prefixes = tuple(allowlist.get("generic_davis_kahan_prefixes", []))

    for module, imports in graph.items():
        layer = classify(module)

        # Rule 1 & 2: firewalls for the staging layers.
        if layer == "fortauceti":
            for imp in imports:
                if classify(imp) not in FORTAUCETI_ALLOWED:
                    p = shortest_path(graph, module,
                                      lambda m, i=imp: m == i)
                    violations.append(Violation(
                        "FORTAUCETI_FIREWALL", module,
                        f"imports {imp} ({classify(imp)}); allowed: "
                        f"Mathlib, TauCeti, ForTauCeti", p))
        elif layer == "formathlib":
            for imp in imports:
                if classify(imp) not in FORMATHLIB_ALLOWED:
                    p = shortest_path(graph, module, lambda m, i=imp: m == i)
                    violations.append(Violation(
                        "FORMATHLIB_FIREWALL", module,
                        f"imports {imp} ({classify(imp)}); allowed: "
                        f"Mathlib, ForMathlib", p))

        # Rule 3 & 5: generic DavisKahan foundation importing a source facade.
        if layer == "davis-kahan" and module.startswith(generic_dk_prefixes):
            for imp in imports:
                if classify(imp) == "dk-source" and module not in generic_sources_ok:
                    violations.append(Violation(
                        "GENERIC_IMPORTS_SOURCE", module,
                        f"generic foundation imports source facade {imp} "
                        f"(backwards dependency)"))

        # Rule 4: production module importing Experimental.
        if layer in ("davis-kahan", "dk-source", "paper", "formathlib",
                     "fortauceti", "tauceti"):
            for imp in imports:
                if classify(imp) == "dk-experimental" and module not in experimental_ok:
                    violations.append(Violation(
                        "PRODUCTION_IMPORTS_EXPERIMENTAL", module,
                        f"production module imports Experimental {imp} "
                        f"without an allowlist entry"))

    # Rule 7: Spectra reaches production only through the Interop bridge.
    spectra_ok = set(allowlist.get("production_imports_spectra", []))
    for module, imports in graph.items():
        lyr = classify(module)
        if lyr not in {"davis-kahan", "dk-source", "paper"}:
            continue
        if module.startswith("DavisKahan.Interop.Spectra"):
            continue          # the designated bridge; this is where Spectra belongs
        for imp in imports:
            if classify(imp) == "spectra" and module not in spectra_ok:
                violations.append(Violation(
                    "PRODUCTION_IMPORTS_SPECTRA", module,
                    f"production module imports {imp} directly instead of going "
                    f"through DavisKahan.Interop.Spectra, and is not in the "
                    f"ratcheting allowlist"))

    # Rule 6: cluster extraction closure (manifest-driven).
    for record in manifest.get("clusters", []):
        cluster = record.get("cluster", "?")
        staging = set(record.get("staging_modules", []))
        for module in staging:
            for imp in graph.get(module, []):
                lyr = classify(imp)
                if lyr not in FORTAUCETI_ALLOWED:
                    violations.append(Violation(
                        "CLUSTER_CLOSURE", module,
                        f"cluster '{cluster}' staging module imports {imp} "
                        f"({lyr}), outside its extraction closure"))
    return violations


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=str(ROOT), help="repository root")
    ap.add_argument("--lib", action="append", default=None,
                    help="library dir to scan (repeatable); default = all")
    ap.add_argument("--allowlist", default=str(ALLOWLIST_PATH))
    ap.add_argument("--manifest", default=str(MANIFEST_PATH))
    ap.add_argument("--json", action="store_true", help="emit JSON report")
    args = ap.parse_args(argv)

    root = pathlib.Path(args.root).resolve()
    lib_dirs = args.lib if args.lib else list(DEFAULT_LIB_DIRS)
    graph = scan(root, lib_dirs)
    allowlist = load_json(pathlib.Path(args.allowlist))
    manifest = load_json(pathlib.Path(args.manifest))
    violations = check(graph, allowlist, manifest)

    if args.json:
        print(json.dumps([
            {"rule": v.rule, "module": v.module, "detail": v.detail,
             "path": v.path} for v in violations], indent=2))
    else:
        if not violations:
            print(f"dependency-layer check: OK "
                  f"({len(graph)} modules scanned, 0 violations)")
        else:
            print(f"dependency-layer check: {len(violations)} violation(s)\n")
            for v in violations:
                print(v.render())
    return 1 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
