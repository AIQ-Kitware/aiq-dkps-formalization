#!/usr/bin/env python3
"""Classify every DavisKahan/ForMathlib module by its admission closure.

The reorganization rule is that `Experimental` means exactly one thing: the
module contains an unresolved admission, or its import closure reaches one.
Everything else belongs in the production tree even if it is currently red.

This is a *planning* tool built from import edges and a textual admission scan.
It deliberately over-approximates: a module that imports an admitted module but
uses only that module's clean declarations is still reported as tainted here.
Splitting those mixed files is the point of the migration, and the
declaration-level `#print axioms` audits remain the trusted check.

Usage:
    python3 scripts/inventory_admission_closure.py [--json OUT] [--quiet]
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from collections import defaultdict, deque

ROOT = pathlib.Path(__file__).resolve().parents[1]
LIBS = ("DavisKahan", "ForMathlib")

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_'.]+)\s*$", re.MULTILINE)
# `sorry`/`admit` as real proof terms. Comments and docstrings are stripped
# first so a prose mention cannot be mistaken for an admission.
ADMISSION_RE = re.compile(r"(?<![A-Za-z0-9_.'])(?:sorry|admit)(?![A-Za-z0-9_'])")
BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--[^\n]*")


def module_name(path: pathlib.Path) -> str:
    return path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")


def strip_comments(text: str) -> str:
    return LINE_COMMENT_RE.sub("", BLOCK_COMMENT_RE.sub("", text))


def collect() -> tuple[dict[str, pathlib.Path], dict[str, set[str]], set[str]]:
    paths: dict[str, pathlib.Path] = {}
    imports: dict[str, set[str]] = {}
    admitted: set[str] = set()
    for lib in LIBS:
        for path in sorted((ROOT / lib).rglob("*.lean")):
            name = module_name(path)
            text = path.read_text(encoding="utf-8", errors="replace")
            paths[name] = path
            imports[name] = set(IMPORT_RE.findall(text))
            if ADMISSION_RE.search(strip_comments(text)):
                admitted.add(name)
        root_file = ROOT / f"{lib}.lean"
        if root_file.exists():
            name = lib
            text = root_file.read_text(encoding="utf-8", errors="replace")
            paths[name] = root_file
            imports[name] = set(IMPORT_RE.findall(text))
    return paths, imports, admitted


def taint(paths, imports, admitted) -> dict[str, set[str]]:
    """Map each module to the admitted modules reachable from it."""
    # Reverse edges: admitted module -> everything that (transitively) imports it.
    rdeps: dict[str, set[str]] = defaultdict(set)
    for name, deps in imports.items():
        for dep in deps:
            if dep in paths:
                rdeps[dep].add(name)

    tainted: dict[str, set[str]] = defaultdict(set)
    for source in admitted:
        queue = deque([source])
        seen = {source}
        while queue:
            current = queue.popleft()
            tainted[current].add(source)
            for parent in rdeps[current]:
                if parent not in seen:
                    seen.add(parent)
                    queue.append(parent)
    return tainted


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", type=pathlib.Path)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    paths, imports, admitted = collect()
    tainted = taint(paths, imports, admitted)

    rows = []
    for name in sorted(paths):
        path = paths[name].relative_to(ROOT).as_posix()
        experimental = ".Experimental." in name or name.endswith(".Experimental")
        sources = sorted(tainted.get(name, ()))
        rows.append(
            {
                "module": name,
                "path": path,
                "in_experimental_tree": experimental,
                "has_own_admission": name in admitted,
                "admission_closure": sources,
                # The two ways the tree currently disagrees with the rule.
                "misplaced_clean": experimental and not sources,
                "misplaced_tainted": not experimental and bool(sources),
            }
        )

    clean_in_experimental = [r for r in rows if r["misplaced_clean"]]
    tainted_in_production = [r for r in rows if r["misplaced_tainted"]]

    if not args.quiet:
        print(f"modules scanned              : {len(rows)}")
        print(f"modules with own admission   : {len(admitted)}")
        print(f"modules in admission closure : {len(tainted)}")
        print(f"clean modules under Experimental (promote) : {len(clean_in_experimental)}")
        print(f"tainted modules outside Experimental (quarantine) : {len(tainted_in_production)}")
        if tainted_in_production:
            print("\n-- tainted but outside Experimental --")
            for row in tainted_in_production:
                print(f"  {row['module']}")
                for source in row["admission_closure"]:
                    print(f"      via {source}")

    if args.json:
        args.json.write_text(json.dumps(rows, indent=2) + "\n")
        if not args.quiet:
            print(f"\nwrote {args.json.relative_to(ROOT)}")

    # This script reports; it never fails a build.
    sys.exit(0)


if __name__ == "__main__":
    main()
