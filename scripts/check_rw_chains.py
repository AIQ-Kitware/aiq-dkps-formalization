#!/usr/bin/env python3
"""Report long `rw` chains, which the `proof-quality` rubric calls brittle.

The rubric: *"Prefer robust automation (`grind`, `simp`, `omega`) over long chains of
named-lemma rewriting, which break on Mathlib renames.  A single explicit `simp only` or
`rw` step is fine; the brittle chain is not."*

**This script exists because the count was wrong twice, and both times it was measured by
an ad-hoc regex in somebody's shell.**  `{lane:RUB-RWCHAIN}` was posted at 63 chains and
the real figure was 53; a later re-measurement said 18 where the answer was 14.  A number
that only lives in shell history gets re-derived slightly differently every time somebody
asks, and a lane sized from it is sized wrong.

**The mistake both times was counting commas inside a `by` block.**  A rewrite by a proved
term -- `rw [show P from ..., by tac]` or `rw [show P by ext p; constructor; ...]` -- is a
SINGLE rewrite, but its tactic block contains commas at the same bracket depth as the
chain's own separators.  `LinearPMap/Closed.lean:707` scored as an eleven-lemma chain
while being one `show`.  Once a `by` opens at depth 1, everything after it belongs to the
tactic block, so entries are counted only up to that point.

Nesting is handled by bracket matching, not by a regex: `rw [foo (bar x) h, baz]` is two
entries, and the comma inside `Summable.tsum_add (h.mul_left s) (h.div_const s)` is not a
separator at all.

Advisory by design, like `check_inline_duplicates`.  A seven-lemma chain is a candidate for
a human to look at, not a defect: three of `ForTauCeti`'s fourteen were examined and kept,
because `simp only` with the same lemmas either loops or cannot reproduce the intermediate
shape a later lemma needs.  Wired in as a failing gate it would train everyone to ignore
the suite, which is what `ADVISORY` exists to prevent.

    python3 scripts/check_rw_chains.py                    # ForTauCeti, threshold 7
    python3 scripts/check_rw_chains.py --scope DavisKahan --min 7
    python3 scripts/check_rw_chains.py --check            # exit 1 if any are found
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

#: `Experimental/` is open research and is not held to the submission rubric.
EXCLUDED_PARTS = {"Experimental"}

RW = re.compile(r"\brw\s*\[")
#: `by` as a whole token -- `by_cases` and `abelian` must not match.
BY = re.compile(r"(?<![A-Za-z_])by(?![A-Za-z_])")


class Chain:
    __slots__ = ("path", "line", "entries", "body", "is_term")

    def __init__(self, path: pathlib.Path, line: int, entries: int, body: str,
                 is_term: bool) -> None:
        self.path, self.line, self.entries = path, line, entries
        self.body, self.is_term = body, is_term

    def __repr__(self) -> str:                      # pragma: no cover
        return f"<Chain {self.path.name}:{self.line} n={self.entries}>"


def chains_in(source: str, path: pathlib.Path = pathlib.Path(".")) -> list[Chain]:
    """Every `rw [...]` in `source`, with its entry count.

    An entry count of `n` means `n` comma-separated rewrites at bracket depth 1, stopping
    at a `by` if one opens there -- see the module docstring for why that matters.
    """
    out: list[Chain] = []
    for m in RW.finditer(source):
        start = m.end()
        depth, i = 1, start
        commas: list[int] = []
        while i < len(source) and depth:
            c = source[i]
            if c in "[(":
                depth += 1
            elif c == ")":
                depth -= 1
            elif c == "]":
                depth -= 1
                if depth == 0:
                    break
            elif c == "," and depth == 1:
                commas.append(i)
            i += 1
        body = source[start:i]
        by = BY.search(body)
        if by is None:
            entries, is_term = 1 + len(commas), False
        else:
            entries = 1 + sum(1 for c in commas if c - start < by.start())
            is_term = True
        out.append(Chain(path, source.count("\n", 0, m.start()) + 1, entries, body, is_term))
    return out


def lean_files(scope: str) -> list[pathlib.Path]:
    root = ROOT / scope
    return sorted(p for p in root.rglob("*.lean")
                  if not EXCLUDED_PARTS & set(p.relative_to(ROOT).parts))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--scope", default="ForTauCeti", help="library to scan")
    ap.add_argument("--min", type=int, default=7, help="report chains with >= this many entries")
    ap.add_argument("--check", action="store_true", help="exit 1 if any chain is reported")
    ap.add_argument("--top", type=int, default=40, help="how many to print")
    args = ap.parse_args(argv)

    found: list[Chain] = []
    rejected = 0
    for path in lean_files(args.scope):
        for chain in chains_in(path.read_text(errors="ignore"), path):
            if chain.is_term and 1 + chain.body.count(",") >= args.min > chain.entries:
                rejected += 1
            if chain.entries >= args.min:
                found.append(chain)

    found.sort(key=lambda c: (-c.entries, c.path.as_posix(), c.line))
    modules = {c.path for c in found}
    for chain in found[:args.top]:
        rel = chain.path.relative_to(ROOT).as_posix()
        print(f"{chain.entries:3}  {rel}:{chain.line}")
        print(f"      {' '.join(chain.body.split())[:140]}")
    if len(found) > args.top:
        print(f"    ... {len(found) - args.top} more not shown (raise --top)")

    print(f"\nrw chains of >= {args.min} named lemmas in {args.scope}/: "
          f"{len(found)} across {len(modules)} module(s)")
    if rejected:
        # Never silent: this exclusion is the whole reason the script exists, and a
        # reader who cannot see it applied has no way to tell it from under-reporting.
        print(f"  ({rejected} `rw [... by ...]` term rewrite(s) excluded -- a tactic "
              f"block's commas are not chain separators)")
    return 1 if (args.check and found) else 0


if __name__ == "__main__":
    sys.exit(main())
