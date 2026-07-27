#!/usr/bin/env python3
"""Refresh Tau Ceti PR-1 integration metadata without touching theorem-name lanes.

The approximation-number API and its submission package evolve on parallel
lanes. This tool deliberately preserves every ``source_declarations`` list in
``dev/tauceti/extraction-manifest.json``; signature-polish agents own those
name entries. It owns only repository-integration metadata:

* current Davis--Kahan and Tau Ceti revisions;
* the dependency-closed approximation-number export module list;
* the unified operator-modulus module path;
* the cluster's validation status; and
* the coordination-lane claim for this consistency-restoration pass.

The export module list is computed from actual ``ForTauCeti`` imports. This is
important because the convergence work split out dependencies such as
``BasisSpan``, ``SingularValues``, and the cardinal-lift helper after the July 24
six-file export. If the concurrent Section 5.1 lane moves rank plumbing into a
new ``RankCompLe`` module and imports it from ``Basic``, that module is included
automatically without this tool editing any declaration-name entry.

Typical use while another agent still owns declaration names::

    python3 scripts/refresh_tauceti_pr1_consistency.py --claim

After that lane has landed and committed its name changes::

    python3 scripts/refresh_tauceti_pr1_consistency.py --write
    python3 scripts/refresh_tauceti_pr1_consistency.py --check
    python3 scripts/export_for_tauceti.py --cluster approximation-number --write
    python3 scripts/export_for_tauceti.py --cluster approximation-number --check
"""
from __future__ import annotations

import argparse
import copy
import json
import pathlib
import re
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "dev/tauceti/extraction-manifest.json"
LANES_PATH = ROOT / "dev/LANES.md"

CLUSTER = "approximation-number"
OLD_MODULUS = (
    "ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.OperatorModulus"
)
NEW_MODULUS = "ForTauCeti.Analysis.InnerProductSpace.OperatorModulus"
NEW_FINAL_MODULUS = "TauCeti.Analysis.InnerProductSpace.OperatorModulus"
CLAIM_MARKER = "Tau Ceti PR-1 consistency restoration"
CLAIM_ROW = (
    "| jon (namek) | dev/tauceti/tauceti-pr1-approximation-numbers.md; "
    "dev/tauceti/migration-build-log-2026-07-24.md; "
    "dev/tauceti/extraction-cluster-classification.md; NEW "
    "dev/tauceti/pr1-consistency-restoration-2026-07-27.md; NEW "
    "scripts/refresh_tauceti_pr1_consistency.py and its test; "
    "dev/tauceti/extraction-manifest.json **non-name integration metadata only** "
    "(revisions, module paths, dependency-closed cluster membership, status; "
    "preserves every `source_declarations` entry); dev/LANES.md this row only. "
    "**Does NOT touch** any Lean theorem file, Section 5.1--5.4 signature work, "
    "the active agent's manifest name entries, comparator JSON, Challenge, "
    "or the Tau Ceti submodule pointer | **Tau Ceti PR-1 consistency "
    "restoration.** Reconcile packaging with the real-valued approximation-number "
    "API and unified `ContinuousLinearMap.modulus`; compute the actual transitive "
    "ForTauCeti export closure; mark July 24 validation historical; and make the "
    "fresh validation gates explicit. | 2026-07-27 | claimed |"
)

IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+"
    r"(ForTauCeti(?:\.[A-Za-z0-9_]+)+)\s*$",
    re.MULTILINE,
)


class ConsistencyError(RuntimeError):
    """Raised when the repository does not match the expected PR-1 shape."""


def _git_output(args: list[str], cwd: pathlib.Path) -> str:
    proc = subprocess.run(
        ["git", *args], cwd=cwd, text=True, capture_output=True, check=False
    )
    if proc.returncode != 0:
        raise ConsistencyError(
            f"git {' '.join(args)} failed in {cwd}: {proc.stderr.strip()}"
        )
    return proc.stdout.strip()


def observed_revisions() -> tuple[str, str]:
    """Return the current repository and Tau Ceti checkout revisions."""
    dk = _git_output(["rev-parse", "HEAD"], ROOT)
    tc_root = ROOT / "external/TauCeti"
    tc = _git_output(["rev-parse", "HEAD"], tc_root)
    return dk, tc


def load_manifest(path: pathlib.Path = MANIFEST_PATH) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _one(items: list[dict[str, Any]], key: str, value: str) -> dict[str, Any]:
    matches = [item for item in items if item.get(key) == value]
    if len(matches) != 1:
        raise ConsistencyError(
            f"expected exactly one object with {key}={value!r}, found {len(matches)}"
        )
    return matches[0]


def staging_path(module: str, root: pathlib.Path = ROOT) -> pathlib.Path:
    if not module.startswith("ForTauCeti."):
        raise ConsistencyError(f"not a ForTauCeti module: {module}")
    return root / pathlib.Path(*module.split(".")).with_suffix(".lean")


def direct_fortauceti_imports(
    module: str, root: pathlib.Path = ROOT
) -> list[str]:
    """Return direct ForTauCeti imports in source order."""
    path = staging_path(module, root)
    if not path.is_file():
        raise ConsistencyError(f"missing staging file: {path.relative_to(root)}")
    return IMPORT_RE.findall(path.read_text(encoding="utf-8"))


def dependency_closed_modules(
    seed_modules: list[str], root: pathlib.Path = ROOT
) -> list[str]:
    """Return a stable dependency-first closure of ForTauCeti imports."""
    ordered: list[str] = []
    permanent: set[str] = set()
    temporary: set[str] = set()

    def visit(module: str) -> None:
        if module in permanent:
            return
        if module in temporary:
            raise ConsistencyError(f"ForTauCeti import cycle involving {module}")
        temporary.add(module)
        for dependency in direct_fortauceti_imports(module, root):
            visit(dependency)
        temporary.remove(module)
        permanent.add(module)
        ordered.append(module)

    for module in seed_modules:
        visit(module)
    return ordered


def refresh_manifest(
    manifest: dict[str, Any],
    dk_commit: str,
    tc_commit: str,
    root: pathlib.Path = ROOT,
) -> dict[str, Any]:
    """Refresh non-name metadata while preserving declaration-name lists."""
    result = copy.deepcopy(manifest)
    before_names = [
        copy.deepcopy(record.get("source_declarations"))
        for record in result.get("records", [])
    ]

    result["davis_kahan_commit"] = dk_commit
    result["tauceti_submodule_commit"] = tc_commit

    cluster = _one(result.get("clusters", []), "cluster", CLUSTER)
    seeds = [
        NEW_MODULUS if module == OLD_MODULUS else module
        for module in cluster.get("staging_modules", [])
    ]
    if NEW_MODULUS not in seeds:
        raise ConsistencyError(
            f"{CLUSTER}: neither historical nor current operator-modulus module found"
        )
    if len(seeds) != len(set(seeds)):
        raise ConsistencyError(f"{CLUSTER}: duplicate seed modules after normalization")

    cluster["staging_modules"] = dependency_closed_modules(seeds, root)
    cluster["status"] = "staged-needs-current-validation"
    cluster["tauceti_population"] = (
        "Everything remains staged in ForTauCeti. The 2026-07-24 Tau Ceti "
        "throwaway export/build predates the real-valued approximation-number "
        "conversion, Courant--Fischer redesign, dependency splits, and unified "
        "operator-modulus API; it is historical evidence only. Re-export the "
        "dependency-closed module list computed from current imports and rerun "
        "strict Tau Ceti validation before submission."
    )

    records = result.get("records", [])
    modulus_candidates = [
        record
        for record in records
        if record.get("staging_module") in {OLD_MODULUS, NEW_MODULUS}
    ]
    if len(modulus_candidates) != 1:
        raise ConsistencyError(
            "expected exactly one operator-modulus extraction record, found "
            f"{len(modulus_candidates)}"
        )
    modulus = modulus_candidates[0]
    modulus["source_module"] = (
        "ForMathlib.Analysis.InnerProductSpace.OperatorAbsoluteValue; "
        "DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus"
    )
    modulus["current_namespace"] = "ContinuousLinearMap"
    modulus["staging_module"] = NEW_MODULUS
    modulus["final_tauceti_module"] = NEW_FINAL_MODULUS
    modulus["provenance_class"] = (
        "unified and generalized (former square operatorAbs and rectangular "
        "operator-modulus APIs)"
    )
    modulus["direct_dependencies"] = ["Mathlib"]
    modulus["status"] = "staged-needs-current-validation"

    after_names = [
        record.get("source_declarations") for record in result.get("records", [])
    ]
    if before_names != after_names:
        raise AssertionError("refresh_manifest modified source_declarations")
    return result


def refresh_lanes(text: str) -> str:
    """Insert the claim row once, preserving all concurrent claim text."""
    if CLAIM_MARKER in text:
        return text
    lines = text.splitlines()
    try:
        header = lines.index("|-------|---------|-------------|------|--------|")
    except ValueError as ex:
        raise ConsistencyError("could not find the dev/LANES.md claim table") from ex
    lines.insert(header + 1, CLAIM_ROW)
    return "\n".join(lines) + "\n"


def check_staging_files(manifest: dict[str, Any]) -> list[str]:
    """Return stale staging-path diagnostics for the PR-1 cluster."""
    cluster = _one(manifest.get("clusters", []), "cluster", CLUSTER)
    errors: list[str] = []
    for module in cluster.get("staging_modules", []):
        try:
            path = staging_path(module)
        except ConsistencyError as ex:
            errors.append(str(ex))
            continue
        if not path.is_file():
            errors.append(f"missing staging file: {path.relative_to(ROOT)}")
    return errors


def write_json(path: pathlib.Path, data: dict[str, Any]) -> None:
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def run(mode: str) -> int:
    if mode == "claim":
        old = LANES_PATH.read_text(encoding="utf-8")
        new = refresh_lanes(old)
        if new != old:
            LANES_PATH.write_text(new, encoding="utf-8")
            print("UPDATED dev/LANES.md: claimed consistency-restoration lane")
        else:
            print("OK dev/LANES.md: lane already claimed")
        return 0

    dk_commit, tc_commit = observed_revisions()
    old_manifest = load_manifest()
    expected_manifest = refresh_manifest(old_manifest, dk_commit, tc_commit)
    old_lanes = LANES_PATH.read_text(encoding="utf-8")
    expected_lanes = refresh_lanes(old_lanes)
    staging_errors = check_staging_files(expected_manifest)

    if mode == "write":
        write_json(MANIFEST_PATH, expected_manifest)
        if expected_lanes != old_lanes:
            LANES_PATH.write_text(expected_lanes, encoding="utf-8")
        cluster = _one(expected_manifest.get("clusters", []), "cluster", CLUSTER)
        print(f"UPDATED {MANIFEST_PATH.relative_to(ROOT)}")
        print(f"  Davis--Kahan revision: {dk_commit}")
        print(f"  Tau Ceti revision:     {tc_commit}")
        print(f"  modulus staging path:  {NEW_MODULUS}")
        print(f"  export closure:        {len(cluster['staging_modules'])} modules")
        for module in cluster["staging_modules"]:
            print(f"    {module}")
        for error in staging_errors:
            print(f"ERROR: {error}")
        return 1 if staging_errors else 0

    assert mode == "check"
    errors: list[str] = []
    if old_manifest != expected_manifest:
        errors.append(
            "extraction manifest metadata or dependency closure is stale; "
            "run this tool with --write"
        )
    if old_lanes != expected_lanes:
        errors.append("consistency-restoration lane is not claimed; run --claim")
    errors.extend(staging_errors)
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        print("Tau Ceti PR-1 consistency: FAILED")
        return 1
    print("Tau Ceti PR-1 consistency: OK")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--claim", action="store_true", help="claim the lane only")
    group.add_argument("--write", action="store_true", help="refresh metadata and claim")
    group.add_argument("--check", action="store_true", help="check current consistency")
    args = parser.parse_args(argv)
    mode = "claim" if args.claim else "write" if args.write else "check"
    try:
        return run(mode)
    except ConsistencyError as ex:
        print(f"ERROR: {ex}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
