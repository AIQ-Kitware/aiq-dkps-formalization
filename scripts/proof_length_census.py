#!/usr/bin/env python3
"""Classify every long proof as scaffolding-bound or refactorable, in any library.

`{lane:RUB-LONGPROOF-CENSUS}` asked one question and answered it well: **is a long
proof long because it has unfactored steps, or because it is mostly local
scaffolding** -- `let`/`set`/`obtain`/`haveI` naming coordinate data -- which does
not factor out without passing every binding back in as an argument?  Its answer
for `ForTauCeti/**` was that only 3 of 123 proofs are ≥30% scaffolding, so the
lane is refactorable and its two stalled slices were the unrepresentative ones.

**That analysis was run and not kept.**  Its scope names "a scan script"; nothing
matching it is in `scripts/`, so its numbers cannot be re-checked and, more to
the point, **`DavisKahan/**` was never measured** -- which matters because that is
where the long proofs actually are:

    ForTauCeti/**   1 proof over 150 lines, worst 153
    DavisKahan/**  21 proofs over 150 lines, worst 466

This script is that analysis, kept.

    python3 scripts/proof_length_census.py                     # both libraries
    python3 scripts/proof_length_census.py --lib DavisKahan
    python3 scripts/proof_length_census.py --min 150 --list    # name every proof

## What counts as a body line

A proof's **body** is what follows `:=` -- the tactic block.  Counting from the
declaration keyword instead includes the signature, which for a theorem with
fifteen hypotheses is twenty lines of binders no refactor can remove.

This measure **is** reproducible against the sibling census: it puts
`pair_mul_eq_inner_comp` at 130 body lines where that lane's row reports the
refactor as `135 -> 94`, which is signature-counting noise and nothing more.

## The scaffolding fraction is NOT reproducible, and that is this script's finding

The sibling census published three numbers -- 3 proofs at >=30% scaffolding, 9 at
15-29%, 111 under 15% -- and two named data points:
`uiNorm_projection_sub_le_of_kyFanSum_le` at **24%** and `pair_mul_eq_inner_comp`
at **23%**.  **Measured at the commits immediately before each was refactored, no
definition of "scaffolding" reproduces those two figures:**

    let/set/obtain/haveI/letI/classical  (the published wording)   10%   15%
    ... plus `have ... :=` naming a term                           15%   18%
    ... plus every `have`                                          54%   38%
    ... plus every `have`, `rcases`, `cases`                       54%   38%

The published 23% and 24% fall between the second and third rows, so that census
counted *some* `have`s under a rule its row does not state -- **and its script was
never committed, so the rule cannot be recovered.**

**The consequence is not that its conclusion is wrong.  It is that the conclusion
cannot be checked**, and twenty-four slices were sized against it.  A scaffolding
percentage is meaningful only relative to a committed definition, which is the
argument for committing this one.  `--scaffold-defn` exposes all four so the
sensitivity is visible rather than hidden in a single number: the same proof
reads 10% or 54% depending on where the line is drawn, and no reader of a bare
"23%" could know that.

**So the length census below is offered as authoritative and the scaffolding
split is offered as parameterized.**  The length census is what `{lane:DK-LONGPROOF}`
actually needs: it is what says `DavisKahan/**` has nineteen proofs over 150 body
lines and `ForTauCeti/**` has none.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

DECL = re.compile(
    r"^(?P<indent>\s*)(?:@\[[^]]*\]\s*)?"
    r"(?:public |private |protected |noncomputable |partial |unsafe )*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][\w.'!?]*)")

#: Opens a local binding whose lines cannot be lifted without passing every
#: binding back in.
#:
#: **`have` is deliberately absent, and that is the sibling census's definition,
#: not an oversight.**  `{lane:RUB-LONGPROOF-CENSUS}` lists exactly
#: "`let`/`set`/`obtain`/`haveI`/`letI`/`classical` and their indented
#: continuations".  Adding `have ... :=` -- which looks like scaffolding, since it
#: names a term -- was the first thing tried here and it moved `ForTauCeti`'s
#: ">= 30%" bucket from 2% to 15%, i.e. it reclassified an eighth of the library
#: on a judgement call.  A `have` is usually a *proof step* that happens to be
#: named, and proof steps are the thing a refactor lifts.  Matching the published
#: definition exactly is what makes the two libraries comparable.
SCAFFOLD_DEFNS: dict[str, str] = {
    "published": r"^\s*(let\b|set\b|obtain\b|haveI\b|letI\b|classical\b)",
    "have-term": r"^\s*(let\b|set\b|obtain\b|haveI\b|letI\b|classical\b"
                 r"|have\s+[\w'\u27e8\u27e9,\s]+:=(?!\s*by\b))",
    "have-all": r"^\s*(let\b|set\b|obtain\b|haveI\b|letI\b|classical\b|have\b)",
    "have-and-cases": r"^\s*(let\b|set\b|obtain\b|haveI\b|letI\b|classical\b"
                      r"|have\b|rcases\b|cases\b)",
}

SCAFFOLD = re.compile(SCAFFOLD_DEFNS["published"])

#: Ends a declaration: a new top-level keyword or the section closing it.
BOUNDARY = re.compile(
    r"^(end\b|namespace\b|section\b|/-!|/--|"
    r"\s*(?:@\[[^]]*\]\s*)?(?:public |private |protected |noncomputable |partial |unsafe )*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|variable|open|import)\b)")


class Proof:
    def __init__(self, name: str, path: pathlib.Path, body: list[str]) -> None:
        self.name = name
        self.path = path
        self.body = body

    @property
    def length(self) -> int:
        return len([line for line in self.body if line.strip()])

    @property
    def scaffold_lines(self) -> int:
        count = 0
        inside = False
        for line in self.body:
            if not line.strip():
                continue
            if SCAFFOLD.match(line):
                inside = True
                count += 1
                continue
            if inside:
                # An indented continuation of the binding that opened above.
                if line.startswith(("      ", "\t\t")) and not line.lstrip().startswith("·"):
                    count += 1
                    continue
                inside = False
        return count

    @property
    def scaffold_percent(self) -> int:
        return 100 * self.scaffold_lines // self.length if self.length else 0


def proofs_in(path: pathlib.Path) -> list[Proof]:
    lines = path.read_text(encoding="utf-8", errors="replace").split("\n")
    out: list[Proof] = []
    index = 0
    while index < len(lines):
        match = DECL.match(lines[index])
        if not match:
            index += 1
            continue
        # Walk to the `:=` that opens the body, then to the declaration's end.
        start = index
        body_start = None
        cursor = index
        while cursor < len(lines):
            if ":=" in lines[cursor]:
                body_start = cursor + 1 if lines[cursor].rstrip().endswith((":=", "by")) else cursor
                break
            if cursor > start and BOUNDARY.match(lines[cursor]):
                break
            cursor += 1
        if body_start is None:
            index = start + 1
            continue
        end = body_start
        while end < len(lines) and not BOUNDARY.match(lines[end]):
            end += 1
        out.append(Proof(match.group("name"), path, lines[body_start:end]))
        index = max(end, start + 1)
    return out


def census(library: str) -> list[Proof]:
    found: list[Proof] = []
    for path in sorted((ROOT / library).rglob("*.lean")):
        if "Experimental" in path.parts:
            continue
        found.extend(proofs_in(path))
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lib", action="append",
                        help="library to scan (repeatable; default both)")
    parser.add_argument("--min", type=int, default=50,
                        help="only proofs with at least this many body lines")
    parser.add_argument("--list", action="store_true",
                        help="name every proof above --min, longest first")
    parser.add_argument("--scaffold-defn", choices=sorted(SCAFFOLD_DEFNS),
                        default="published",
                        help="which line counts as scaffolding (see the module docstring: "
                             "the choice moves a single proof between 10%% and 54%%)")
    args = parser.parse_args()

    global SCAFFOLD
    SCAFFOLD = re.compile(SCAFFOLD_DEFNS[args.scaffold_defn])

    libraries = args.lib or ["ForTauCeti", "DavisKahan"]
    for library in libraries:
        long_proofs = [p for p in census(library) if p.length >= args.min]
        heavy = [p for p in long_proofs if p.scaffold_percent >= 30]
        medium = [p for p in long_proofs if 15 <= p.scaffold_percent < 30]
        light = [p for p in long_proofs if p.scaffold_percent < 15]
        total = len(long_proofs) or 1
        print(f"\n{library}/** -- {len(long_proofs)} proof(s) of {args.min}+ body lines")
        print(f"  scaffolding definition: {args.scaffold_defn} "
              f"(not reproducible against the sibling census -- see the docstring)")
        print(f"  scaffolding >= 30%   {len(heavy):3d}  ({100 * len(heavy) // total}%)"
              "   hard to factor: every lifted line needs its bindings passed back")
        print(f"  scaffolding 15-29%   {len(medium):3d}  ({100 * len(medium) // total}%)")
        print(f"  scaffolding  < 15%   {len(light):3d}  ({100 * len(light) // total}%)"
              "   ordinary tactic sequences")
        over150 = sorted((p for p in long_proofs if p.length > 150),
                         key=lambda p: -p.length)
        if over150:
            print(f"  over 150 body lines  {len(over150):3d}   worst {over150[0].length}")
        if args.list:
            for proof in sorted(long_proofs, key=lambda p: -p.length):
                rel = proof.path.relative_to(ROOT)
                print(f"    {proof.length:4d} lines  {proof.scaffold_percent:3d}% scaffold  "
                      f"{rel}:{proof.name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
