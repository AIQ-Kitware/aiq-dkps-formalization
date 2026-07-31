#!/usr/bin/env python3
"""Refuse build products for modules whose source no longer exists.

`lake` compiles a source file into `.lake/build/lib/lean/<Module>.olean` and
**never deletes that artifact when the source goes away**.  Nothing in the tool
chain notices, because nothing looks: `lake build` walks *sources*, and an
orphaned `.olean` is not reachable from any source, so it is neither rebuilt nor
removed.  It simply stays on disk, importable, indefinitely.

That is harmless right up until something imports by name outside
`defaultTargets` -- and this repository does exactly that, in
`check_davis_kahan_frontier.py`, which writes a probe file importing
`DavisKahan.Experimental.Frontier.All` and compiles it with `lake env lean`.

**Measured on 2026-07-31: 126 modules had build products and no source.**  The
oldest were the 23 `SinTheta/Continuation*.lean` files that lane `EXP-CONT`
moved into `Continuation/` a day earlier.  The frontier gate failed with

    error: import ...SinTheta.Continuation.Core failed, environment already
    contains 'TauCeti.DavisKahanExt.SameProjectionComponent' from
    ...SinTheta.ContinuationCore

which is the failure worth naming: **the moved module and the ghost of its old
self were both in the environment, and the ghost won the name.**  A reader
diagnosing that message looks for a duplicate *source* file, and there is none;
`git status` is clean; `lake build` is green.  The evidence is only on disk in a
build directory nobody reads.

## Why this is a gate and not a `lake clean`

`lake clean` fixes it and takes an hour of rebuild.  The point of a gate is that
the condition is **cheap to detect and expensive to discover**: comparing the
artifact tree to the source tree is a directory walk, while the alternative is
what happened here -- a gate failing with a message about the wrong file, in a
tree where every other check is green.

A rename is the only way to reach this state, so the gate is really a check that
renames were followed through.  `--fix` removes the orphans; the default reports
them, because deleting build products is not something a check should do without
being asked.

    python3 scripts/check_stale_build_artifacts.py           # report
    python3 scripts/check_stale_build_artifacts.py --check   # exit 1 on a finding
    python3 scripts/check_stale_build_artifacts.py --fix     # remove them
"""

from __future__ import annotations

import argparse
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
BUILD = ROOT / ".lake/build/lib/lean"
IR = ROOT / ".lake/build/ir"

#: The libraries whose sources live in this repository.  Everything else under
#: the build tree belongs to a dependency and is not ours to judge.
LIBS = ("DavisKahan", "ForTauCeti", "Challenge", "Acharyya2025")

#: Every extension `lake` writes for one module, so `--fix` removes the whole
#: set.  Leaving a `.trace` behind while deleting its `.olean` produces a
#: *different* confusing failure, which would not be an improvement.
EXTENSIONS = (".olean", ".ilean", ".trace", ".c", ".c.o.export",
              ".c.o.noexport", ".extraDepTrace", ".hash", ".log.json")


def orphans() -> list[pathlib.Path]:
    """Modules with an `.olean` and no `.lean`, as paths relative to BUILD."""
    out: list[pathlib.Path] = []
    for lib in LIBS:
        directory = BUILD / lib
        if not directory.is_dir():
            continue
        for olean in sorted(directory.rglob("*.olean")):
            rel = olean.relative_to(BUILD)
            if not (ROOT / rel.with_suffix(".lean")).is_file():
                out.append(rel.with_suffix(""))
    return out


def remove(module: pathlib.Path) -> int:
    removed = 0
    for extension in EXTENSIONS:
        for target in (BUILD / module.with_suffix(extension),
                       IR / module.with_suffix(extension)):
            if target.exists():
                target.unlink()
                removed += 1
    return removed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="exit 1 on a finding")
    parser.add_argument("--fix", action="store_true", help="remove the artifacts")
    args = parser.parse_args()

    if not BUILD.is_dir():
        print("stale build artifacts: no build tree -- nothing to check")
        return 0

    stale = orphans()
    if not stale:
        print("stale build artifacts: OK -- every build product has a source")
        return 0

    print(f"stale build artifacts: {len(stale)} module(s) with no source")
    for module in stale:
        print(f"-> {str(module).replace('/', '.')}")

    if args.fix:
        total = sum(remove(module) for module in stale)
        print(f"\nremoved {total} file(s) for {len(stale)} module(s).")
        print("  Rebuild any target that imports them by name -- `lake build` alone")
        print("  only covers `defaultTargets`, which is how they went stale.")
        return 0

    print(
        "\n  These are importable.  A module moved or deleted without clearing its\n"
        "  build products keeps resolving under its old name, and an importer that\n"
        "  names it directly -- `check_davis_kahan_frontier.py` writes such a probe --\n"
        "  gets the ghost instead of an error.  Re-run with `--fix`."
    )
    return 1 if args.check else 0


if __name__ == "__main__":
    sys.exit(main())
