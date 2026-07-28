#!/usr/bin/env python3
"""Find (and optionally delete) build artifacts whose Lean source is gone.

`lake` does not garbage-collect `.olean`/`.ilean`/`.c`/`.trace` files when the
`.lean` that produced them is deleted or renamed.  The stale artifacts are
invisible to `lake build`, which works from the source tree, but they are *not*
invisible to anything that imports **by module name** through `LEAN_PATH` --
and that is how the frontier probe (`scripts/check_davis_kahan_frontier.py`)
and the comparator pre-flight build their scratch files.

The failure mode is confusing rather than obvious.  A module deleted during a
migration leaves an orphan that still exports its declarations, so a *live*
module declaring the same name now looks like a duplicate:

    import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic failed,
    environment already contains
    'ContinuousLinearMap.approximationNumber_comp_comp_le'
    from ForMathlib.Analysis.Normed.Operator.ApproximationNumber

`ForMathlib.Analysis.Normed.Operator.ApproximationNumber` was deleted in the
Wave-1 move to `ForTauCeti`; only its `.olean` survived.  Because every
checkout accumulates its own orphans, a gate broken this way looks broken for
everyone and is easy to write off as "a stale build".

Only the repository's own libraries are considered.  Nothing under
`.lake/packages` (Mathlib, Batteries, ...) is ever touched: those sources live
elsewhere and their artifacts are legitimately unmatched here.

Usage:

    python3 scripts/clean_orphan_build_artifacts.py            # report only
    python3 scripts/clean_orphan_build_artifacts.py --delete   # remove them
    python3 scripts/clean_orphan_build_artifacts.py --json
"""

from __future__ import annotations

import argparse
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# Libraries whose sources live in this repository.  A build artifact under one
# of these roots with no matching `.lean` is an orphan.
OWN_LIBS = {
    "Acharyya2025",
    "Challenge",
    "DavisKahan",
    "DkpsQuench2026",
    "ForMathlib",
    "ForTauCeti",
    "Helm2025",
}

# Artifact trees keyed by the suffix lake gives the built file.
ARTIFACT_DIRS = {
    ".lake/build/lib/lean": (".olean", ".ilean"),
    ".lake/build/ir": (".c", ".trace"),
}


def orphans(root: pathlib.Path) -> list[pathlib.Path]:
    """Artifacts under `root` whose corresponding `.lean` source is missing."""
    found: list[pathlib.Path] = []
    for subdir, suffixes in ARTIFACT_DIRS.items():
        base = root / subdir
        if not base.is_dir():
            continue
        for artifact in base.rglob("*"):
            if not artifact.is_file() or artifact.suffix not in suffixes:
                continue
            rel = artifact.relative_to(base)
            if not rel.parts or rel.parts[0] not in OWN_LIBS:
                continue
            # `Foo/Bar.setup.json` and friends hang off the same stem; compare
            # against the plain source path.
            source = root / rel.with_suffix(".lean")
            if not source.exists():
                found.append(artifact)
    return sorted(found)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--root", default=str(ROOT), help="repository root")
    ap.add_argument("--delete", action="store_true",
                    help="delete the orphaned artifacts (default: report only)")
    ap.add_argument("--json", action="store_true", help="emit JSON")
    args = ap.parse_args(argv)

    root = pathlib.Path(args.root).resolve()
    found = orphans(root)

    if args.json:
        print(json.dumps([str(p.relative_to(root)) for p in found], indent=2))
    else:
        if not found:
            print("orphan build artifacts: none")
        else:
            # Group by library so a migration shows up as one block.
            by_lib: dict[str, int] = {}
            for p in found:
                rel = p.relative_to(root)
                # .lake/build/{lib/lean,ir}/<Lib>/...
                lib = next((part for part in rel.parts if part in OWN_LIBS), "?")
                by_lib[lib] = by_lib.get(lib, 0) + 1
            print(f"orphan build artifacts: {len(found)} "
                  f"(source deleted or renamed, artifact left behind)")
            for lib, n in sorted(by_lib.items()):
                print(f"  {lib}: {n}")
            if not args.delete:
                print("\nre-run with --delete to remove them; they are under "
                      ".lake/build and are not tracked by git")

    if args.delete:
        for p in found:
            p.unlink()
        if found and not args.json:
            print(f"deleted {len(found)} artifact(s)")

    return 0


if __name__ == "__main__":
    sys.exit(main())
