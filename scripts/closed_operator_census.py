#!/usr/bin/env python3
"""Measure the U1 gate metric: type-position uses of the DKPS `ClosedOperator`.

Gate U1.4's second command is stated in terms of "type-position uses", but the
figure it was quoted with (171) was never accompanied by a command, so nobody
could check the gate they were being held to.  The fallback that *was* given --

    grep -rc ClosedOperator --include='*.lean' DavisKahan/ | ...

counts every mention, so it also counts `import` lines, docstrings, provenance
prose, `#check`s and `alias`es.  On 2026-07-29 that fallback read 707 while the
true type-position count was far lower: of the nine modules it reported at
exactly one occurrence, four were imports, one a docstring, one a `#check`, one
an `alias`, and only two were real.

This script reports both numbers so the gap is visible, and lists the modules
that genuinely still name the bundle in a signature -- which is the set U1
actually has to migrate.

Usage:  python3 scripts/closed_operator_census.py [--verbose]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Excluded by the gate's own statement: the bundle's own home, and Experimental
# (outside defaultTargets).
EXCLUDED_PREFIXES = (
    "DavisKahan/SpectralTheory/ClosedOperator/",
    "DavisKahan/Experimental/",
)

# Every alias/abbrev for the same bundle counts: a signature naming any of them
# is still a type-position use of the bundle.
#
# Deliberately EXCLUDED, because a bare `grep ClosedOperator` conflates them
# with the bundle and thereby inflates the gate metric:
#   * `ClosedOperatorComplexification` -- a *namespace*, not a type (86 hits,
#     68 of them in one module that the old table listed at 104);
#   * `RealClosedOperator` -- a different type;
#   * `inverseClosedOperator`, `toClosedOperator`, `toClosedOperatorOfGraphNorm`
#     and friends -- functions, whose migration is implied by their types rather
#     than being separate type positions.
NAMES = re.compile(
    r"\b("
    r"DKClosedOperator"
    r"|DirectClosedOperatorOn[EF]"
    r"|ComplexClosedOperator(?:H|On[EF])"
    r"|ClosedOperatorOn[EF]"
    r"|ClosedOperator[EF]"
    r"|ClosedOperator"
    r")\b"
)

BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)


def strip_noise(text: str) -> str:
    """Remove block comments (incl. docstrings), line comments, and imports."""
    text = BLOCK_COMMENT.sub("", text)
    kept = []
    for line in text.split("\n"):
        stripped = line.lstrip()
        if stripped.startswith("import "):
            continue
        if stripped.startswith("--"):
            continue
        if stripped.startswith("#check") or stripped.startswith("#print"):
            continue
        line = line.split("--")[0]
        kept.append(line)
    return "\n".join(kept)


def main() -> int:
    verbose = "--verbose" in sys.argv
    raw_total = 0
    real_total = 0
    raw_modules: set[str] = set()
    real_modules: dict[str, int] = {}

    for path in sorted((ROOT / "DavisKahan").rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        if any(rel.startswith(p) for p in EXCLUDED_PREFIXES):
            continue
        text = path.read_text(encoding="utf-8")
        raw = len(NAMES.findall(text))
        if raw:
            raw_total += raw
            raw_modules.add(rel)
        real = len(NAMES.findall(strip_noise(text)))
        if real:
            real_total += real
            real_modules[rel] = real

    print(f"raw mentions      : {raw_total} across {len(raw_modules)} modules")
    print(f"type-position uses: {real_total} across {len(real_modules)} modules")
    print(f"prose/import/#check overcount: {raw_total - real_total}")

    if verbose and real_modules:
        print("\nmodules with genuine type-position uses (descending):")
        for rel, n in sorted(real_modules.items(), key=lambda kv: -kv[1]):
            print(f"  {n:4d}  {rel}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
