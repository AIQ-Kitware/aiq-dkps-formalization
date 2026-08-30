#!/usr/bin/env python3
"""Produce a checkable Davis--Kahan 1970 compilation/audit certificate bundle.

The certificate separates two questions:

1. Does the pinned Lean toolchain compile the production library and resolve the
   declarations registered by the source census?
2. Do those compiled types actually match the mathematical claims in the paper?

This script answers (1), snapshots the checked-in distributable source
specification, and produces an audit packet that an independent reviewer can use
for (2).

Recommended compiler-evidence run:
    python3 scripts/certify_davis_kahan_1970.py --clean

Once every *stated result* has passed hostile semantic review, add
`--require-terminal`. The hard denominator is the compact formalization-result
inventory, not proof equations in the source-fidelity inventory and not the 49
organizational statement-map rows.

`--clean` removes only this repository's `.lake/build`; dependency caches remain
intact. `--clean-tauceti` additionally removes the Tau Ceti checkout's
`.lake/build`, when an explicit checkout is supplied.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tarfile
import time
from collections import defaultdict

from check_davis_kahan_1970_result_inventory import (
    completion_summary as formalization_result_completion_summary,
    discover_inventory as discover_result_inventory,
)

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from _external_checkouts import tauceti_root  # noqa: E402

try:
    from aiq_lean_tools.certification import (
        git_snapshot,
        sha256_file,
        source_tree_hash as package_source_tree_hash,
    )
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )

ROOT = pathlib.Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT / "build"
MAP_PATH = ROOT / "dev/davis-kahan-1970-statement-map.json"
CENSUS_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.json"
FORMALIZATION_PATH = ROOT / "formalization.yaml"
TEX_PATH = ROOT / "prose/distilled_literature/DavisKahan1970_part_III.tex"
SOURCE_MANIFEST_PATH = ROOT / "prose/distilled_literature/source_manifest.json"
SEMANTIC_REVIEW_PATH = ROOT / "dev/davis-kahan-1970-result-semantic-review-2026-08-12.md"
SEMANTIC_AUDIT_SURFACE_PATH = ROOT / "DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean"

HASH_EXTENSIONS = {".lean", ".py", ".yaml", ".yml", ".toml", ".json", ".tex", ".md"}
HASH_BASENAMES = {"lean-toolchain", "lake-manifest.json"}
WARNING_RE = re.compile(r"\bwarning:", re.IGNORECASE)
BEGIN_TOKEN = "DKCERT|BEGIN|"
END_TOKEN = "DKCERT|END|"


def now_utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")


def command_output(argv: list[str], cwd: pathlib.Path = ROOT) -> tuple[int, str]:
    try:
        done = subprocess.run(argv, cwd=cwd, text=True, capture_output=True, check=False)
    except FileNotFoundError as ex:
        return 127, str(ex)
    return done.returncode, (done.stdout + done.stderr).strip()


def git_info() -> dict:
    """The repository's Git state, plus the submodule status this bundle records."""
    snapshot = dict(git_snapshot(ROOT))
    snapshot["clean"] = snapshot.get("available", False) and not snapshot.get("dirty", True)
    # The certificate schema names the commit `head`; keep that spelling stable
    # for readers of already-published bundles.
    snapshot["head"] = snapshot.get("commit")
    rc, submodules = command_output(["git", "submodule", "status", "--recursive"])
    snapshot["submodule_status"] = submodules.splitlines() if rc == 0 and submodules else []
    return snapshot


def nested_git_info(path: pathlib.Path) -> dict:
    if not path.exists():
        return {"present": False}
    rc, head = command_output(["git", "rev-parse", "HEAD"], cwd=path)
    src, status = command_output(["git", "status", "--porcelain=v1", "--untracked-files=all"], cwd=path)
    return {
        "present": True,
        "is_git_checkout": rc == 0,
        "head": head if rc == 0 else None,
        "status_porcelain": status.splitlines() if src == 0 and status else [],
        "clean": src == 0 and not status,
    }


def source_file_list() -> list[pathlib.Path]:
    """Tracked + untracked source/config files that define this certification run."""
    rc, raw = command_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"]
    )
    if rc == 0:
        names = [x for x in raw.split("\0") if x]
        candidates = [ROOT / name for name in names]
    else:
        candidates = [p for p in ROOT.rglob("*") if p.is_file()]
    out: list[pathlib.Path] = []
    for path in candidates:
        try:
            rel = path.relative_to(ROOT)
        except ValueError:
            continue
        if not path.is_file():
            continue
        if any(part.startswith(".") and part not in {".mathlib-quality"} for part in rel.parts):
            continue
        if rel.parts and rel.parts[0] == "build":
            continue
        if path.suffix in HASH_EXTENSIONS or path.name in HASH_BASENAMES:
            out.append(path)
    return sorted(set(out), key=lambda p: str(p.relative_to(ROOT)))


def source_tree_hash() -> tuple[str, list[dict]]:
    """A stable digest of every file that defines this certification run."""
    return package_source_tree_hash(ROOT, source_file_list())


def tool_version(argv: list[str]) -> dict:
    rc, output = command_output(argv)
    return {"command": argv, "returncode": rc, "output": output}


def tee_command(label: str, argv: list[str], outdir: pathlib.Path) -> dict:
    log_name = f"{label}.log"
    log_path = outdir / "logs" / log_name
    log_path.parent.mkdir(parents=True, exist_ok=True)
    print(f"\n== {label}: {' '.join(argv)} ==", flush=True)
    start = time.monotonic()
    warning_count = 0
    try:
        process = subprocess.Popen(
            argv,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=1,
        )
    except FileNotFoundError as ex:
        log_path.write_text(str(ex) + "\n", encoding="utf-8")
        return {
            "label": label,
            "command": argv,
            "returncode": 127,
            "duration_seconds": 0.0,
            "warning_count": 0,
            "log": str(log_path.relative_to(outdir)),
        }
    assert process.stdout is not None
    with log_path.open("w", encoding="utf-8") as log:
        for line in process.stdout:
            print(line, end="")
            log.write(line)
            if WARNING_RE.search(line):
                warning_count += 1
    returncode = process.wait()
    elapsed = time.monotonic() - start
    print(f"== {label}: exit {returncode}, {elapsed:.1f}s, warnings {warning_count} ==", flush=True)
    return {
        "label": label,
        "command": argv,
        "returncode": returncode,
        "duration_seconds": round(elapsed, 3),
        "warning_count": warning_count,
        "log": str(log_path.relative_to(outdir)),
    }


def registered_census_declarations() -> tuple[list[str], dict[str, list[str]]]:
    """All declaration names registered by the census, deduplicated in census order."""
    data = json.loads(CENSUS_PATH.read_text(encoding="utf-8"))
    claims: dict[str, list[str]] = defaultdict(list)
    ordered: list[str] = []
    seen: set[str] = set()
    for item in data["items"]:
        for decl in item.get("lean_declarations", []):
            claims[decl].append(item["id"])
            if decl not in seen:
                ordered.append(decl)
                seen.add(decl)
    return ordered, dict(claims)


def write_signature_probe(path: pathlib.Path, declarations: list[str]) -> None:
    lines = [
        "import DavisKahan.All",
        "",
        "-- Generated by scripts/certify_davis_kahan_1970.py.",
        "-- The BEGIN/END markers make multiline #check output machine-parseable for every census-registered declaration.",
        "",
    ]
    for index, decl in enumerate(declarations):
        lines += [
            f'#eval IO.println "{BEGIN_TOKEN}{index}|{decl}"',
            f"#check @{decl}",
            f'#eval IO.println "{END_TOKEN}{index}"',
            "",
        ]
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_signature_log(
    text: str, declarations: list[str], claims: dict[str, list[str]]
) -> dict[str, dict]:
    by_index: dict[int, list[str]] = {}
    current: int | None = None
    for line in text.splitlines():
        if BEGIN_TOKEN in line:
            tail = line.split(BEGIN_TOKEN, 1)[1]
            index_text = tail.split("|", 1)[0]
            try:
                current = int(index_text)
            except ValueError:
                current = None
                continue
            by_index[current] = []
            continue
        if END_TOKEN in line:
            tail = line.split(END_TOKEN, 1)[1]
            try:
                end_index = int(tail.split()[0].split("|", 1)[0])
            except ValueError:
                end_index = current if current is not None else -1
            if current == end_index:
                current = None
            continue
        if current is not None:
            by_index.setdefault(current, []).append(line)

    out: dict[str, dict] = {}
    for index, decl in enumerate(declarations):
        raw = "\n".join(by_index.get(index, [])).strip()
        # `#check` always prints something on success.  Error diagnostics inside
        # the marker pair make this entry unresolved even if the process later
        # continues to subsequent checks.
        resolved = bool(raw) and re.search(r"(^|\n).*\berror(?:\(|:)", raw, re.IGNORECASE) is None
        out[decl] = {
            "resolved": resolved,
            "type": raw if resolved else "",
            "raw": raw,
            "claim_ids": claims.get(decl, []),
        }
    return out


def snapshot_inputs(outdir: pathlib.Path) -> dict[str, str]:
    paths = [
        MAP_PATH,
        CENSUS_PATH,
        TEX_PATH,
        FORMALIZATION_PATH,
        SOURCE_MANIFEST_PATH,
        ROOT / "lean-toolchain",
        ROOT / "lakefile.toml",
        ROOT / "lake-manifest.json",
        ROOT / "dev/davis-kahan-1970-independent-audit-prompt.md",
        SEMANTIC_REVIEW_PATH,
        SEMANTIC_AUDIT_SURFACE_PATH,
    ]
    statement_map = json.loads(MAP_PATH.read_text(encoding="utf-8"))
    fidelity_rel = statement_map.get("source_atom_inventory")
    if isinstance(fidelity_rel, str) and fidelity_rel.strip():
        paths.append(ROOT / fidelity_rel)
    result_inventory = discover_result_inventory()
    if result_inventory is not None and result_inventory.exists():
        paths.append(result_inventory)
    target = outdir / "inputs"
    target.mkdir(parents=True, exist_ok=True)
    hashes: dict[str, str] = {}
    for path in paths:
        if not path.exists():
            continue
        rel = path.relative_to(ROOT)
        # Flatten only the snapshot directory while retaining informative names.
        name = rel.as_posix().replace("/", "__")
        dest = target / name
        shutil.copy2(path, dest)
        hashes[rel.as_posix()] = sha256_file(path)
    return hashes


def census_completion_summary() -> dict:
    """Return result-level formalization terminality, not row/source-atom counts."""
    return formalization_result_completion_summary(require_terminal=False)


def write_bundle_readme(outdir: pathlib.Path, certificate: dict) -> None:
    text = f"""# Davis--Kahan 1970 compiler certificate bundle

Overall compiler-certificate status: **{certificate.get('overall_status', 'unknown')}**

Hostile-certified stated-result terminality: **{certificate.get('source_coverage', {}).get('source_coverage_terminal', 'unknown')}** ({certificate.get('source_coverage', {}).get('terminal_completion_obligations', '?')}/{certificate.get('source_coverage', {}).get('completion_obligations', '?')} formalization-result obligations terminal). The fine-grained source-fidelity inventory is audited separately and does not enlarge this theorem/result denominator.

This bundle certifies compilation/name-resolution evidence only. It does not certify semantic equivalence between the paper and the Lean theorem types. Use `statement-audit.md` with the independent audit prompt snapshot under `inputs/` for that review.

## Integrity

From this directory, verify all bundled files with:

```bash
sha256sum -c SHA256SUMS
```

## Key files

- `certificate.json`: toolchain, Git/source identity, command results, warning counts, and source-tree hash.
- `signatures.json`: compiler-printed types for every declaration registered by the Davis--Kahan source census.
- `statement-audit.md`: registered passages from the distributable source specification paired with the primary Lean theorem types and a result-by-result audit checklist.
- `inputs/dev__davis-kahan-1970-result-semantic-review-2026-08-12.md`: maintained hostile semantic review for all 29 counted results.
- `inputs/DavisKahan__Sources__DavisKahan1970__Audits__ResultSemanticSurface.lean`: compiler-checkable `#check` surface for the exact declarations selected by the result inventory and the strongest evidence delimiting any remaining red result.
- `logs/`: complete output of each certification command and the theorem-signature probe.
- `inputs/`: snapshots of the distributable source specification, source-fidelity inventory, formalization-result inventory when present, statement map, census, formalization metadata, and audit prompt.

`DavisKahan1970_part_III.tex` is both the readable transformative reconstruction and the mechanical statement-level semantic baseline. The certificate does not require or snapshot a private transcription.

For a final 100% audit, require `clean_root_build: true`, `source_tree_stable_during_certificate: true`, zero unresolved registered signatures, a successful `DavisKahan.All` build, and `source_coverage.source_coverage_terminal: true`. The latter is derived only from the compact stated-result inventory: every theorem/proposition/lemma/corollary/headline/standalone result must have an exact or formally refuted source-facing disposition, compiler evidence, and accepted semantic review. Intermediate proof identities remain source-fidelity material and are not formalization obligations. Running with `--require-terminal` makes that result-level gate hard.
"""
    (outdir / "README.md").write_text(text, encoding="utf-8")


def write_sha256s(outdir: pathlib.Path) -> pathlib.Path:
    sums = outdir / "SHA256SUMS"
    lines: list[str] = []
    for path in sorted(p for p in outdir.rglob("*") if p.is_file() and p != sums):
        lines.append(f"{sha256_file(path)}  {path.relative_to(outdir).as_posix()}")
    sums.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return sums


def make_bundle(outdir: pathlib.Path, head: str | None) -> pathlib.Path:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    short = (head or "nogit")[:12]
    archive = outdir.parent / f"davis-kahan-1970-certificate-{short}-{stamp}.tar.gz"
    with tarfile.open(archive, "w:gz") as tar:
        tar.add(outdir, arcname=outdir.name)
    return archive


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clean", action="store_true", help="remove root .lake/build before certification")
    parser.add_argument(
        "--clean-tauceti",
        action="store_true",
        help="also remove the Tau Ceti checkout's .lake/build before certification "
             "(requires --tauceti-root or TAUCETI_ROOT)",
    )
    parser.add_argument(
        "--tauceti-root",
        default=None,
        help="path to a Tau Ceti checkout for upstream provenance (or set TAUCETI_ROOT); "
             "omitted, the certificate simply records that none was supplied",
    )
    parser.add_argument(
        "--output-dir",
        type=pathlib.Path,
        default=BUILD_ROOT / "davis-kahan-1970-certificate",
    )
    parser.add_argument(
        "--allow-warnings",
        action="store_true",
        help="record ordinary-build warnings without making the certificate fail",
    )
    parser.add_argument(
        "--require-clean-git",
        action="store_true",
        help="fail certification if the working tree is dirty",
    )
    parser.add_argument(
        "--with-audits",
        action="store_true",
        help="also build DavisKahan.Audits.All (not part of the production build)",
    )
    parser.add_argument(
        "--require-terminal",
        action="store_true",
        help="also require every stated-result inventory obligation to be terminal; source-fidelity atoms and organizational rows are not the denominator",
    )
    args = parser.parse_args()

    outdir = args.output_dir
    if not outdir.is_absolute():
        outdir = ROOT / outdir
    if outdir.exists():
        shutil.rmtree(outdir)
    outdir.mkdir(parents=True)

    started = now_utc()
    git = git_info()
    tau_root = tauceti_root(args.tauceti_root)
    tau = nested_git_info(tau_root) if tau_root else {"present": False}
    source_before, source_entries_before = source_tree_hash()

    cleaned_root = False
    cleaned_tau = False
    if args.clean:
        target = ROOT / ".lake/build"
        if target.exists():
            shutil.rmtree(target)
        cleaned_root = True
    if args.clean_tauceti:
        if tau_root is None:
            print("--clean-tauceti needs a Tau Ceti checkout; pass --tauceti-root PATH "
                  "or set TAUCETI_ROOT.", file=sys.stderr)
            return 2
        target = tau_root / ".lake/build"
        if target.exists():
            shutil.rmtree(target)
        cleaned_tau = True

    statement_map_command = [sys.executable, "scripts/check_davis_kahan_1970_statement_map.py"]
    result_inventory_command = [sys.executable, "scripts/check_davis_kahan_1970_result_inventory.py"]
    if args.require_terminal:
        result_inventory_command.append("--require-terminal")
    # The generic gates are installed `aiq-lean` commands over policy files in
    # `dev/policy/`; only the Davis--Kahan-specific ones are repository scripts.
    commands: list[tuple[str, list[str]]] = [
        ("01-aggregate-check", [
            "aiq-lean", "source", "aggregates",
            "--base", "DavisKahan", "--library", "DavisKahan",
            "--skip-dir", "Experimental", "--skip-dir", "MathAhead", "--skip-dir", "Audits",
            "--root-import", "DavisKahan",
            "--header-file", "dev/policy/aggregate-header.txt", "--check",
        ]),
        ("02-library-structure", [sys.executable, "scripts/check_library_structure.py"]),
        ("02b-import-layers", ["aiq-lean", "imports", "check", "dev/policy/import-layers.yaml"]),
        ("03-namespace-policy", ["aiq-lean", "namespaces", "check", "dev/policy/namespaces.yaml"]),
        ("04-duplicate-qualified-names", [
            "aiq-lean", "source", "duplicates",
            "--prefix", "ForTauCeti", "--prefix", "DavisKahan",
            "--exclude-prefix", "DavisKahan.Experimental", "--check",
        ]),
        ("05-statement-map", statement_map_command),
        ("05b-formalization-result-inventory", result_inventory_command),
        ("06-distilled-literature-index", [sys.executable, "scripts/check_distilled_literature_index.py"]),
        ("07-production-build", ["lake", "build", "DavisKahan.All"]),
        ("07b-result-semantic-surface", ["lake", "env", "lean", str(SEMANTIC_AUDIT_SURFACE_PATH.relative_to(ROOT))]),
        # The census checker runs the declaration probe itself, so a separate
        # probe step would compile the same file twice.
        ("08-source-census", [sys.executable, "scripts/check_davis_kahan_1970_source_census.py"]),
        ("09-workspace-ledgers", ["aiq-lean", "workspace", "validate", "--static-declarations"]),
    ]
    if args.with_audits:
        commands.append(("10-diagnostic-audits", ["lake", "build", "DavisKahan.Audits.All"]))

    results: list[dict] = []
    for label, argv in commands:
        results.append(tee_command(label, argv, outdir))

    declarations, claims = registered_census_declarations()
    probe_path = outdir / "review-signatures.lean"
    write_signature_probe(probe_path, declarations)
    # The generated probe is under build/, which is ignored by Git but is a
    # perfectly ordinary Lean source file for `lake env lean`.
    probe_result = tee_command(
        "11-review-signature-probe",
        ["lake", "env", "lean", str(probe_path.relative_to(ROOT))],
        outdir,
    )
    results.append(probe_result)
    probe_log = outdir / probe_result["log"]
    signatures = parse_signature_log(probe_log.read_text(encoding="utf-8"), declarations, claims)
    unresolved_signatures = sorted(d for d, data in signatures.items() if not data["resolved"])
    signature_doc = {
        "schema_version": 1,
        "generated_at_utc": now_utc(),
        "probe_returncode": probe_result["returncode"],
        "total": len(signatures),
        "resolved": len(signatures) - len(unresolved_signatures),
        "unresolved": unresolved_signatures,
        "signatures": signatures,
    }
    (outdir / "signatures.json").write_text(
        json.dumps(signature_doc, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )

    source_after, source_entries_after = source_tree_hash()
    source_stable = source_before == source_after
    input_hashes = snapshot_inputs(outdir)

    build_result = next(x for x in results if x["label"] == "07-production-build")
    command_failures = [x["label"] for x in results if x["returncode"] != 0]
    build_warning_failure = build_result["warning_count"] > 0 and not args.allow_warnings
    dirty_failure = args.require_clean_git and not git["clean"]

    overall_pass = (
        not command_failures
        and not unresolved_signatures
        and source_stable
        and not build_warning_failure
        and not dirty_failure
    )
    source_coverage = census_completion_summary()

    certificate = {
        "schema_version": 1,
        "certificate_kind": "Davis-Kahan 1970 theorem-statement compilation certificate",
        "started_at_utc": started,
        "finished_at_utc": now_utc(),
        "overall_status": "PASS" if overall_pass else "FAIL",
        "semantic_fidelity_certified": False,
        "semantic_fidelity_note": (
            "This certificate proves compilation/name-resolution facts only. "
            "Independent mathematical review of source-vs-Lean statement fidelity is required."
        ),
        "source_coverage": source_coverage,
        "formalization_denominator": "stated_results_only",
        "terminality_required_for_this_run": args.require_terminal,
        "clean_root_build": cleaned_root,
        "clean_tauceti_build": cleaned_tau,
        "warnings_allowed": args.allow_warnings,
        "production_build_warning_count": build_result["warning_count"],
        "git": git,
        "external_tauceti": tau,
        "source_specification": {
            "path": str(TEX_PATH.relative_to(ROOT)),
            "sha256": sha256_file(TEX_PATH),
            "authority": "checked_in_transformative_source_specification",
            "private_transcription_required": False,
        },
        "source_tree_sha256": source_after,
        "source_tree_sha256_before_build": source_before,
        "source_tree_stable_during_certificate": source_stable,
        "source_file_count": len(source_entries_after),
        "source_tree_files": source_entries_after,
        "tools": {
            "python": {"executable": sys.executable, "version": sys.version},
            "lean": tool_version(["lake", "env", "lean", "--version"]),
            "lake": tool_version(["lake", "--version"]),
        },
        "input_hashes": input_hashes,
        "commands": results,
        "command_failures": command_failures,
        "signature_file": "signatures.json",
        "registered_signature_count": len(signatures),
        "registered_signature_unresolved": unresolved_signatures,
        "failure_reasons": [
            *(["one or more certification commands failed"] if command_failures else []),
            *(["one or more census-registered declarations did not produce a compiler type"] if unresolved_signatures else []),
            *(["source/config files changed while certification was running"] if not source_stable else []),
            *(["DavisKahan.All emitted warnings"] if build_warning_failure else []),
            *(["Git working tree was not clean"] if dirty_failure else []),
        ],
    }
    cert_path = outdir / "certificate.json"
    cert_path.write_text(json.dumps(certificate, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    renderer = ROOT / "scripts/render_davis_kahan_1970_audit_packet.py"
    audit_path = outdir / "statement-audit.md"
    render_result = tee_command(
        "12-render-audit-packet",
        [sys.executable, str(renderer.relative_to(ROOT)), "--certificate", str(cert_path.relative_to(ROOT)), "--output", str(audit_path.relative_to(ROOT))],
        outdir,
    )
    # Add renderer evidence to the certificate and rewrite it before checksums.
    certificate["commands"].append(render_result)
    if render_result["returncode"] != 0:
        certificate["overall_status"] = "FAIL"
        certificate["command_failures"].append(render_result["label"])
        certificate["failure_reasons"].append("audit packet renderer failed")
    cert_path.write_text(json.dumps(certificate, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    write_bundle_readme(outdir, certificate)

    write_sha256s(outdir)
    archive = make_bundle(outdir, git.get("head"))

    print("\nDavis--Kahan 1970 certificate summary")
    print(f"  status: {certificate['overall_status']}")
    print(f"  clean root build: {cleaned_root}")
    print(f"  production build warnings: {build_result['warning_count']}")
    print(f"  registered declaration signatures: {len(signatures) - len(unresolved_signatures)}/{len(signatures)}")
    print(f"  stated-result terminality: {source_coverage['terminal_completion_obligations']}/{source_coverage['completion_obligations']}")
    print(f"  source stable during run: {source_stable}")
    print(f"  certificate: {cert_path.relative_to(ROOT)}")
    print(f"  audit packet: {audit_path.relative_to(ROOT)}")
    print(f"  bundle: {archive.relative_to(ROOT)}")
    return 0 if certificate["overall_status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
