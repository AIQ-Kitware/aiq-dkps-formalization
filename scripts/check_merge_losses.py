#!/usr/bin/env python3
"""Report declarations that a merge dropped and that no later commit restored.

**A merge that resolves a conflict by taking one side wholesale silently loses
whatever the other side added, and nothing in this repository can see it.**  The
build is green -- the dropped declaration is gone, so nothing references it.
Every gate is green, for the same reason.  `git status` is clean.  The merge
message says "merged".  The only witness is the parent commit, and nothing reads
parent commits.

That matters here more than in most repositories because several agents work in
parallel branches and merge constantly: on 2026-07-31 the last 30 merges on
`origin/main` had **28 declaration names** that were present in a parent and
absent from the result.

## What it does NOT tell you

Every one of those 28 was deliberate.  The gate cannot know that, and **it should
not try** -- a deletion and a loss are the same event to git.  What it produces
is a *short list a human can adjudicate*, which is the whole value: 28 names is
an afternoon's checking, and "did any of today's merges lose anything" is
otherwise unanswerable.  For the record, the 28 fell into five kinds:

  - a retirement lane doing its job (`HasKyFanApproximationGaugeTriangle`)
  - a deduplication (`basisDiagonalRealMap`, `card_filter_lt'` -- the prime)
  - a rename (`spectralCutoff_lower_bound` -> `tailCutoff_lower_bound`)
  - a roadmap sketch upgraded (`def LowerHemicontinuous _ := True` replaced by
    Mathlib's real `LowerHemicontinuousAt`)
  - one false positive: `rather`, from a docstring line wrapping after `def`

**A rename always reads as a loss** and always will, because the check is by
name.  That is the intended trade: comparing bodies would drown in reformatting,
while a name is exactly the thing a consumer depends on.

    python3 scripts/check_merge_losses.py            # last 30 merges, report
    python3 scripts/check_merge_losses.py --limit 5  # just today's
    python3 scripts/check_merge_losses.py --check    # exit 1 on a finding

`--check` is for a human running it after a merge session, not for a hook: it
fires on every legitimate rename, so wiring it into CI would train people to
ignore it.
"""

from __future__ import annotations

import argparse
import functools
import re
import subprocess
import sys

#: Lines that open a declaration.  Deliberately loose on the modifier prefix --
#: `private`, `@[simp]`, `noncomputable` and friends all have to pass through,
#: and missing one shows up as a phantom "loss" rather than a silent gap.
DECL_LINE = (r"^\s*(@\[[^]]*\]\s*)?"
             r"(public |private |protected |noncomputable |partial |unsafe )*"
             r"(theorem|lemma|def|abbrev|instance|structure|class|inductive) ")

NAME = re.compile(
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
    r"([A-Za-z_][\w.'!?]*)")


def run(*args: str) -> str:
    return subprocess.run(args, capture_output=True, text=True).stdout


@functools.lru_cache(maxsize=None)
def declarations_at(rev: str) -> frozenset[str]:
    """Every declaration name in every `.lean` file at `rev`.

    One `git grep` per revision.  The obvious implementation -- `git show` per
    file -- is roughly 70,000 subprocesses over 30 merges, which is the
    difference between a minute and an afternoon.
    """
    text = run("git", "grep", "-h", "-E", DECL_LINE, rev, "--", "*.lean")
    return frozenset(match.group(1) for line in text.split("\n")
                     if (match := NAME.search(line)))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=30, help="how many merges back")
    parser.add_argument("--ref", default="origin/main", help="branch to walk")
    parser.add_argument("--check", action="store_true", help="exit 1 on a finding")
    args = parser.parse_args()

    merges = [line for line in run("git", "log", "--merges", "--format=%H",
                                   f"-{args.limit}", args.ref).strip().split("\n") if line]
    if not merges:
        print(f"merge losses: no merges on {args.ref} -- nothing to check")
        return 0

    head = declarations_at("HEAD")
    print(f"merge losses: HEAD carries {len(head)} declaration names; "
          f"walking {len(merges)} merge(s) on {args.ref}")

    total: set[str] = set()
    for merge in merges:
        parents = run("git", "rev-parse", f"{merge}^@").split()
        if len(parents) != 2:
            continue
        result = declarations_at(merge)
        dropped: set[str] = set()
        for parent in parents:
            dropped |= declarations_at(parent) - result
        absent = sorted(dropped - head)
        if not absent:
            continue
        total |= set(absent)
        subject = run("git", "log", "-1", "--format=%h %s", merge).strip()
        print(f"\n{subject}")
        print(f"  {len(dropped)} dropped at the merge, {len(absent)} still absent from HEAD:")
        for name in absent:
            print(f"    {name}")

    if not total:
        print("\nmerge losses: OK -- every declaration dropped at a merge is back at HEAD")
        return 0

    print(f"\nmerge losses: {len(total)} distinct name(s) dropped and not restored.")
    print("  Adjudicate each one; they are not all defects.  A rename reads as a loss,")
    print("  and so does a deliberate retirement or dedup.  What you are looking for is")
    print("  a name with no successor and no lane row explaining it -- that is content")
    print("  a conflict resolution dropped, and nothing else in the repository can see it.")
    return 1 if args.check else 0


if __name__ == "__main__":
    sys.exit(main())
