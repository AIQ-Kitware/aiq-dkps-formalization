#!/usr/bin/env python3
"""Inventory incomplete Lean declarations by roadmap role and import reachability.

This is a textual admission inventory, not a compilation or trusted-dependency
checker.  Zero recorded terms does not mean that Lean accepts the source: an
unknown identifier, malformed declaration, or failed tactic can leave a module
uncompiled without appearing here.  Pair this tool with actual Lake/Lean exit
statuses and printed dependency information.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
from collections import Counter

try:
    from aiq_lean_tools.lean_source import ADMISSION_RE, scan_lean_project, strip_comments
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )

SOURCE_ROOTS = (
    "DavisKahan.Sources.DavisKahan1970.PartIIIManuscriptSurface",
    "DavisKahan.Sources.DavisKahan1970.GeneralSinTheta",
)
DEFAULT_ROOTS = ("DavisKahan",)

EXPLICIT_SUPERSEDED = {
    "DavisKahan/Experimental/InfiniteDimensional/Core/UnboundedSpectral.lean":
        "legacy cutoff facade bypassed by the direct Spectra engine",
}

ROADMAP_PATTERNS = (
    ("direct-rotation", ("DirectRotation",)),
    ("tan-theta", ("/TanTheta/", "TanTheta.lean")),
    ("double-angle", ("DoubleAngle",)),
    ("sharpness-equality", ("Sharpness",)),
    ("spectral-projection-foundation", ("Core/SpectralProjection.lean", "Core/OperatorAngle.lean", "Core/Forms.lean")),
    ("ideal-instances", ("Ideals/Symmetric.lean", "Ideals/Rectangular.lean", "Ideals/CompactAndSingular.lean")),
    ("sylvester-alternatives", ("Sylvester/Basic.lean", "Sylvester/Resolvent.lean")),
    ("continuation-branch", ("SinTheta/Continuation",)),
    ("finite-alternative", ("Experimental/FiniteDimensional",)),
)


def find_root() -> pathlib.Path:
    here = pathlib.Path.cwd().resolve()
    for candidate in (here, *here.parents):
        if (candidate / "lakefile.toml").exists() or (candidate / "lakefile.lean").exists():
            return candidate
    raise SystemExit("repository root not found")


#: The libraries whose debt this inventory covers.
SCOPE = ("DavisKahan", "Challenge")


def classify(path: str) -> tuple[str, str]:
    if path.startswith("Challenge/"):
        return "challenge", "intentional immutable exercise"
    if path in EXPLICIT_SUPERSEDED:
        return "superseded", EXPLICIT_SUPERSEDED[path]
    for label, patterns in ROADMAP_PATTERNS:
        if any(pattern in path for pattern in patterns):
            return label, "candidate work for the full-paper roadmap"
    return "unclassified", "requires theorem-level triage"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--write-json", type=pathlib.Path)
    args = parser.parse_args()

    root = find_root()
    index = scan_lean_project(root)
    modules = {
        module: path for module, path in index.modules.items()
        if any(module == top or module.startswith(top + ".") for top in SCOPE)
    }
    source_cone = index.import_closure(SOURCE_ROOTS)
    default_cone = index.import_closure(DEFAULT_ROOTS)

    records: list[dict[str, object]] = []
    for module, source in sorted(modules.items()):
        stripped = strip_comments(source.read_text(encoding="utf8", errors="replace"))
        locations = [
            number
            for number, line in enumerate(stripped.splitlines(), 1)
            if ADMISSION_RE.search(line)
        ]
        if not locations:
            continue
        rel = source.relative_to(root).as_posix()
        category, note = classify(rel)
        records.append({
            "module": module,
            "path": rel,
            "count": len(locations),
            "lines": locations,
            "category": category,
            "note": note,
            "import_reachable_from_full_part_iii": module in source_cone,
            "import_reachable_from_default_root": module in default_cone,
        })

    category_counts = Counter()
    for record in records:
        category_counts[str(record["category"])] += int(record["count"])
    result = {
        "schema_version": 1,
        "source_roots": SOURCE_ROOTS,
        "default_roots": DEFAULT_ROOTS,
        "total_occurrences": sum(int(record["count"]) for record in records),
        "file_count": len(records),
        "category_counts": dict(sorted(category_counts.items())),
        "records": records,
        "caution": "This counts textual unfinished terms only. It does not compile modules and cannot detect dangling references or failed proofs. Import reachability is not theorem dependency.",
    }

    if args.write_json:
        destination = args.write_json
        if not destination.is_absolute():
            destination = root / destination
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf8")
    if args.json or not args.write_json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"Incomplete-term inventory: {result['total_occurrences']} occurrences in {result['file_count']} files")
        for category, count in result["category_counts"].items():
            print(f"  {category}: {count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
