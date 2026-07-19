#!/usr/bin/env python3
"""Inventory incomplete Lean declarations by roadmap role and import reachability.

This is a planning tool, not a trusted-dependency checker. A file can contain
open declarations while a particular theorem in that file remains clean. Use
printed dependency information for theorem-level claims.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
from collections import Counter, deque

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_'.]+)\s*$", re.MULTILINE)
INCOMPLETE_RE = re.compile(r"\b(?:sorry|admit)\b")

SOURCE_ROOTS = (
    "DavisKahan.Sources.DavisKahan1970.FullPartIII",
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


def source_to_module(root: pathlib.Path, source: pathlib.Path) -> str:
    return source.relative_to(root).with_suffix("").as_posix().replace("/", ".")


def module_graph(root: pathlib.Path) -> tuple[dict[str, pathlib.Path], dict[str, list[str]]]:
    modules: dict[str, pathlib.Path] = {}
    for top in ("DavisKahan", "ForMathlib", "Challenge"):
        path = root / top
        if not path.exists():
            continue
        for source in path.rglob("*.lean"):
            modules[source_to_module(root, source)] = source
    graph: dict[str, list[str]] = {}
    for module, source in modules.items():
        graph[module] = [name for name in IMPORT_RE.findall(source.read_text(encoding="utf8")) if name in modules]
    return modules, graph


def reachable(graph: dict[str, list[str]], roots: tuple[str, ...]) -> set[str]:
    seen: set[str] = set()
    queue = deque(roots)
    while queue:
        item = queue.popleft()
        if item in seen:
            continue
        seen.add(item)
        queue.extend(graph.get(item, ()))
    return seen


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
    modules, graph = module_graph(root)
    source_cone = reachable(graph, SOURCE_ROOTS)
    default_cone = reachable(graph, DEFAULT_ROOTS)

    records: list[dict[str, object]] = []
    for module, source in sorted(modules.items()):
        lines = source.read_text(encoding="utf8").splitlines()
        locations = [number for number, line in enumerate(lines, 1) if INCOMPLETE_RE.search(line)]
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
        "caution": "Import reachability is not theorem dependency. Use the trusted dependency audit for endpoint claims.",
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
