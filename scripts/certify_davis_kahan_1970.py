#!/usr/bin/env python3
"""Produce a checkable Davis--Kahan 1970 compilation/audit certificate bundle.

The certificate separates two questions:

1. Does the pinned Lean toolchain compile the production library and resolve the
   declarations registered by the source census?
2. Do those compiled types actually match the mathematical claims in the paper?

This script answers (1), snapshots the exact source claim register, and produces
an audit packet that an independent reviewer can use for (2).

Recommended compiler-evidence run:
    python3 scripts/certify_davis_kahan_1970.py --clean

Once every completion obligation is independently believed terminal, add
`--require-terminal` to make a nonterminal census row fail the certificate gate.

`--clean` removes only this repository's `.lake/build`; dependency caches remain
intact. `--clean-tauceti` additionally removes `external/TauCeti/.lake/build`.
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

ROOT = pathlib.Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT / "build"
MAP_PATH = ROOT / "dev/davis-kahan-1970-statement-map.json"
CENSUS_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.json"
FORMALIZATION_PATH = ROOT / "formalization.yaml"
TEX_PATH = ROOT / "prose/distilled_literature/DavisKahan1970_exact_source_register.tex"
EXPOSITION_PATH = ROOT / "prose/distilled_literature/DavisKahan1970_part_III.tex"
SOURCE_MANIFEST_PATH = ROOT / "prose/distilled_literature/source_manifest.json"

HASH_EXTENSIONS = {".lean", ".py", ".yaml", ".yml", ".toml", ".json", ".tex", ".md"}
HASH_BASENAMES = {"lean-toolchain", "lake-manifest.json"}
WARNING_RE = re.compile(r"\bwarning:", re.IGNORECASE)
BEGIN_TOKEN = "DKCERT|BEGIN|"
END_TOKEN = "DKCERT|END|"


def now_utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as file:
        for chunk in iter(lambda: file.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def command_output(argv: list[str], cwd: pathlib.Path = ROOT) -> tuple[int, str]:
    try:
        done = subprocess.run(argv, cwd=cwd, text=True, capture_output=True, check=False)
    except FileNotFoundError as ex:
        return 127, str(ex)
    return done.returncode, (done.stdout + done.stderr).strip()


def git_info() -> dict:
    head_rc, head = command_output(["git", "rev-parse", "HEAD"])
    branch_rc, branch = command_output(["git", "branch", "--show-current"])
    status_rc, status = command_output(["git", "status", "--porcelain=v1", "--untracked-files=all"])
    sub_rc, submodules = command_output(["git", "submodule", "status", "--recursive"])
    return {
        "available": head_rc == 0,
        "head": head if head_rc == 0 else None,
        "branch": branch if branch_rc == 0 else None,
        "status_porcelain": status.splitlines() if status_rc == 0 and status else [],
        "clean": status_rc == 0 and not status,
        "submodule_status": submodules.splitlines() if sub_rc == 0 and submodules else [],
    }


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
    entries: list[dict] = []
    aggregate = hashlib.sha256()
    for path in source_file_list():
        rel = path.relative_to(ROOT).as_posix()
        digest = sha256_file(path)
        entries.append({"path": rel, "sha256": digest, "bytes": path.stat().st_size})
        aggregate.update(rel.encode("utf-8"))
        aggregate.update(b"\0")
        aggregate.update(digest.encode("ascii"))
        aggregate.update(b"\n")
    return aggregate.hexdigest(), entries


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
        EXPOSITION_PATH,
        FORMALIZATION_PATH,
        SOURCE_MANIFEST_PATH,
        ROOT / "lean-toolchain",
        ROOT / "lakefile.toml",
        ROOT / "lake-manifest.json",
        ROOT / "dev/davis-kahan-1970-closure-audit-2026-08-12.md",
        ROOT / "dev/davis-kahan-1970-independent-audit-prompt.md",
    ]
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
    data = json.loads(CENSUS_PATH.read_text(encoding="utf-8"))
    items = data["items"]
    completion = [item for item in items if item.get("section") != "10"]
    terminal = [
        item for item in completion
        if item.get("verification") == "proved_in_build"
        and item.get("status") in {"compiled_exact", "refuted_as_transcribed"}
    ]
    nonterminal = [
        {
            "id": item.get("id"),
            "status": item.get("status"),
            "verification": item.get("verification"),
            "scope_gap": item.get("scope_gap"),
            "blocked_by": item.get("blocked_by", []),
        }
        for item in completion if item not in terminal
    ]
    return {
        "completion_obligations": len(completion),
        "terminal_completion_obligations": len(terminal),
        "source_coverage_terminal": len(terminal) == len(completion),
        "nonterminal_rows": nonterminal,
    }


def write_bundle_readme(outdir: pathlib.Path, certificate: dict) -> None:
    text = f"""# Davis--Kahan 1970 compiler certificate bundle

Overall compiler-certificate status: **{certificate.get('overall_status', 'unknown')}**

Tracked source-coverage terminality: **{certificate.get('source_coverage', {}).get('source_coverage_terminal', 'unknown')}** ({certificate.get('source_coverage', {}).get('terminal_completion_obligations', '?')}/{certificate.get('source_coverage', {}).get('completion_obligations', '?')} completion obligations currently terminal in the census).

This bundle certifies compilation/name-resolution evidence only. It does not certify semantic equivalence between the paper and the Lean theorem types. Use `statement-audit.md` with the independent audit prompt snapshot under `inputs/` for that review.

## Integrity

From this directory, verify all bundled files with:

```bash
sha256sum -c SHA256SUMS
```

## Key files

- `certificate.json`: toolchain, Git/source identity, command results, warning counts, and source-tree hash.
- `signatures.json`: compiler-printed types for every declaration registered by the Davis--Kahan source census.
- `statement-audit.md`: exact source excerpts paired with the primary Lean theorem types and a row-by-row audit checklist.
- `logs/`: complete output of each certification command and the theorem-signature probe.
- `inputs/`: snapshots of the readable mathematical exposition, exact source register, statement map, census, formalization metadata, and audit prompt. The private modernized transcription is never copied into the bundle.

The readable `DavisKahan1970_part_III.tex` snapshot is explanatory context for working through the mathematics. The exact-source register is the mechanical statement-level audit baseline; the certificate keeps these roles separate.

For a final 100% audit, require `clean_root_build: true`, `source_tree_stable_during_certificate: true`, zero unresolved registered signatures, a successful `DavisKahan.All` build, `source_coverage.source_coverage_terminal: true`, and then independently audit the mathematical statements row by row. Running the certificate with `--require-terminal` makes the maintained census terminality a hard gate; it still does not replace semantic review.
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
        help="also remove external/TauCeti/.lake/build before certification",
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
        "--transcription",
        type=pathlib.Path,
        help="optional private modernized transcription; verify the registered exact excerpts against it by SHA-256 and recorded line ranges without copying the private source into the certificate bundle",
    )
    parser.add_argument(
        "--with-audits",
        action="store_true",
        help="also build DavisKahan.Audits.All (not part of the production build)",
    )
    parser.add_argument(
        "--require-terminal",
        action="store_true",
        help="also require every non-Section-10 completion obligation to be compiled_exact or refuted_as_transcribed with proved_in_build verification",
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
    tau = nested_git_info(ROOT / "external/TauCeti")
    source_before, source_entries_before = source_tree_hash()

    cleaned_root = False
    cleaned_tau = False
    if args.clean:
        target = ROOT / ".lake/build"
        if target.exists():
            shutil.rmtree(target)
        cleaned_root = True
    if args.clean_tauceti:
        target = ROOT / "external/TauCeti/.lake/build"
        if target.exists():
            shutil.rmtree(target)
        cleaned_tau = True

    statement_map_command = [sys.executable, "scripts/check_davis_kahan_1970_statement_map.py"]
    if args.require_terminal:
        statement_map_command.append("--require-terminal")
    transcription_path: pathlib.Path | None = None
    transcription_sha256: str | None = None
    if args.transcription is not None:
        transcription_path = args.transcription.expanduser().resolve()
        if transcription_path.exists():
            transcription_sha256 = sha256_file(transcription_path)
        statement_map_command += ["--transcription", str(transcription_path)]

    commands: list[tuple[str, list[str]]] = [
        ("01-aggregate-check", [sys.executable, "scripts/generate_all_aggregates.py", "--check"]),
        ("02-library-structure", [sys.executable, "scripts/check_library_structure.py"]),
        ("03-namespace-policy", [sys.executable, "scripts/check_namespace_policy.py"]),
        ("04-duplicate-qualified-names", [sys.executable, "scripts/check_duplicate_qualified_names.py"]),
        ("05-statement-map", statement_map_command),
        ("06-distilled-literature-index", [sys.executable, "scripts/check_distilled_literature_index.py"]),
        ("07-production-build", ["lake", "build", "DavisKahan.All"]),
        ("08-source-census", [sys.executable, "scripts/check_davis_kahan_1970_source_census.py"]),
        ("09-census-declaration-probe", [sys.executable, "scripts/probe_census_declarations.py", "--verify"]),
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
        "terminality_required_for_this_run": args.require_terminal,
        "clean_root_build": cleaned_root,
        "clean_tauceti_build": cleaned_tau,
        "warnings_allowed": args.allow_warnings,
        "production_build_warning_count": build_result["warning_count"],
        "git": git,
        "external_tauceti": tau,
        "private_transcription_provenance": {
            "provided": transcription_path is not None,
            "path": str(transcription_path) if transcription_path is not None else None,
            "sha256": transcription_sha256,
            "copied_into_bundle": False,
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
    print(f"  tracked source terminality: {source_coverage['terminal_completion_obligations']}/{source_coverage['completion_obligations']}")
    print(f"  source stable during run: {source_stable}")
    print(f"  certificate: {cert_path.relative_to(ROOT)}")
    print(f"  audit packet: {audit_path.relative_to(ROOT)}")
    print(f"  bundle: {archive.relative_to(ROOT)}")
    return 0 if certificate["overall_status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
