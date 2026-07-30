#!/usr/bin/env python3
"""Ratchet the internal-workflow prose in `ForTauCeti` docstrings.

`ForTauCeti` is a rehearsal for a Tau Ceti submission, and its module docstrings are
read there, not here.  A docstring that says *"Lane SPLIT-1K divided it at its `end
Reduce` seam"* or points at `dev/LANES.md` documents **our bookkeeping**, not the
mathematics, and names nothing a Tau Ceti maintainer can look up.  Worse, 31 of these
point at `ForMathlib/`, a tree lane `FM-RETIRE` deleted -- those are broken references
*today*, in this repository, before any question of submission arises.

Tau Ceti's `documentation` rubric is explicit that presence is the linter's job and
usefulness is the reviewer's: *"Linters may check presence; you judge usefulness and
honesty ... Flag documentation that is wrong, stale, or copied without being adapted."*

**This does NOT touch attribution.**  `Formalized by Claude ...` and the `## Provenance`
block stay: the `attribution` rubric requires them, and it warns against inventing
requirements for routine work.  A lane id is not a source and a move-date is not a
source.  What goes is the workflow narration.  Git already records who moved what and
when, losslessly and without going stale.

**Why a ratchet rather than a fix.**  The prose accretes because the convention produces
it: every lane that touches a file records that it did.  Measured 2026-07-30, the count
went from 69 modules to 70 *during the FTC-EXPOSE conversion*, and internal-path
references went 7 -> 32 -- much of that added by the very agent that opened the cleanup
lane, writing "tracked with lane FTC-EXPOSE-SPECMEAS" into exposure comments.  So the
gate lands first and holds the line; the cleanup slices follow.

    python3 scripts/check_submission_prose.py           # report
    python3 scripts/check_submission_prose.py --check   # gate; exit 1 above the baseline
    python3 scripts/check_submission_prose.py --list    # name every module and hit
"""

import argparse
import importlib.util
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LIB = ROOT / "ForTauCeti"

#: Highest number of modules that may carry internal-workflow prose.  Only ever lower it.
#: Measured 2026-07-30, the day the gate landed.  **Corrected the same day from 70 to 58,
#: and that drop is NOT cleanup** -- it is the provenance exemption below fixing a
#: false-positive class in this gate's first version.  Twelve modules were being flagged
#: for `ForMathlib/` inside `* Original module:` bullets, which are genuine source records.
#: Do not read the change as progress; no docstring was touched.  The cleanup slices are lanes
#: FTC-PROSE-a .. FTC-PROSE-d; FTC-PROSE-ENFORCE drops this to 0 and flips the
#: convention so new files stop generating it.
#:
#: **RAISED from 0 to 34 on 2026-07-30, and this is not a regression in the tree.**  The
#: tree did not change; the ruler did.  Both patterns below had holes wide enough to
#: report a clean repository over 58 real hits, so the 0 recorded here was measuring the
#: regexes rather than the docstrings.  Raising it is the honest move -- a baseline that
#: is only ever lowered is worth having precisely because it is never quietly wrong, and
#: leaving 0 in place would have made every future run agree with a number that was false
#: the day it was written.  **Back to 0 in the very next commit**, which removed all 58.
BASELINE = 0

#: Highest number of individual hits.  The module count alone is not enough: adding a
#: fourth lane id to a module that already has three leaves the module count unchanged,
#: so a modules-only ratchet lets the prose keep growing inside the files that already
#: have it.  Found by testing this gate against a deliberate regression -- it passed.
#:
#: Raised to 42 with `BASELINE` and returned to 0 with it, for the reason recorded there.
HIT_BASELINE = 0

#: An internal lane id: `lane FTC-EXPOSE-g2`, `Lane SPLIT-1K`, `lane Y3`, `lane T15a`.
#: Anchored on the word `lane` so ordinary prose ("the bounded-operator lane ever
#: needs") does not match -- that phrasing produced a false positive in the first
#: measurement of this defect.
#:
#: `[`*_]{0,2}` is not cosmetic, and leaving it out is how this gate reported a clean
#: tree while 15 lane references sat in 12 modules.  A lane id is an identifier, so in a
#: Lean docstring the natural way to write it is in backticks -- ``lane `AN-A4-COMPACT` ``
#: -- and the undecorated pattern misses every one of those.  Bold (`lane **SR-E**`) fails
#: the same way.  The decoration must be optional and must sit between the keyword and the
#: id, which is exactly where a writer puts it.  `\s+` already spans a newline, which
#: matters: three of the fifteen had wrapped between `lane` and the id.
LANE_ID = re.compile(
    r"\b[Ll]anes?\s+[`*_]{0,2}(?:[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+|Y\d+|T\d+[a-c]?)\b")

#: Paths that do not exist in the destination repository, or at all.
#:
#: `dev/` is matched as a whole rather than by naming its subdirectories one at a time.
#: The enumerated version listed `dev/LANES.md`, `dev/journals` and `dev/audit/`, and
#: missed 15 references to `dev/tauceti/` for no reason other than that nobody had added
#: it -- a gate that has to be extended every time a directory is created is a gate that
#: is quietly wrong most of the time.  The whole `dev/` tree is our workflow and none of
#: it travels with a submission.
INTERNAL_PATH = re.compile(r"\bdev/|\.claude/worktrees|ForMathlib/")

#: Provenance lines are EXEMPT from the path check, and getting this wrong was the first
#: version's bug.  `* Original module: ForMathlib/.../CourantFischer.lean at Davis--Kahan
#: commit fc38eb48...` is a genuine source record: it names where the material came from
#: and pins a resolvable commit.  The `attribution` rubric requires exactly that and warns
#: against inventing requirements for routine work.  What is NOT exempt is narration that
#: happens to mention the same path -- "Moved from ForMathlib/... on 2026-07-29 under lane
#: Y3(b2)" -- which git already records losslessly.  Match the provenance BULLET, not the
#: word: a line beginning `* Original ...`.
PROVENANCE_LINE = re.compile(
    r"^\s*\*\s*(?:Original\s+(?:repository|module|declarations|authors)"
    r"|`?[\w.']+`? was originally)", re.M)

#: "Moved 2026-07-29", "Documented 2026-07-30" -- migration archaeology.
DATED_MOVE = re.compile(
    r"\b(?:Moved|Migrated|Split|Renamed|Promoted|Documented|Recorded|Divided|Deduplicated)"
    r"\b[^.]{0,60}?\b20\d\d-\d\d-\d\d")

KINDS = (("lane id", LANE_ID), ("internal path", INTERNAL_PATH), ("dated move", DATED_MOVE))

# Reuse the readiness gate's comment stripper rather than re-implementing it.  Block
# comments MUST be removed before line comments: a docstring containing "Davis--Kahan"
# otherwise eats its own `-/` closer, and that bug has produced two false clean reports
# in this repository already.
_spec = importlib.util.spec_from_file_location(
    "_readiness", pathlib.Path(__file__).with_name("check_tauceti_readiness.py"))
_READY = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_READY)

_BLOCK = re.compile(r"/-.*?-/", re.S)
_LINE = re.compile(r"--.*?$", re.M)


def comment_text(source: str) -> str:
    """Every comment and docstring, and nothing else."""
    blocks = [m.group(0) for m in _BLOCK.finditer(source)]
    lines = [m.group(0) for m in _LINE.finditer(_BLOCK.sub("", source))]
    return "\n".join(blocks + lines)


def _drop_provenance_lines(text: str) -> str:
    """Blank out `* Original ...` bullets, including their continuation lines.

    A provenance bullet wraps, so dropping only the matched line would leave the path on
    the next one and the exemption would not fire."""
    out, skipping = [], False
    for line in text.splitlines():
        if PROVENANCE_LINE.match(line):
            skipping = True
            out.append("")
            continue
        if skipping:
            # continuation = indented and not the start of a new bullet
            if line.strip() and not line.lstrip().startswith("*"):
                out.append("")
                continue
            skipping = False
        out.append(line)
    return "\n".join(out)


def offenders() -> list[tuple[pathlib.Path, dict[str, list[str]]]]:
    out = []
    for path in sorted(LIB.rglob("*.lean")):
        text = comment_text(path.read_text(errors="ignore"))
        without_provenance = _drop_provenance_lines(text)
        found = {}
        for name, pattern in KINDS:
            # the path check exempts provenance bullets; the others apply everywhere
            scope = without_provenance if name == "internal path" else text
            hits = [m.group(0).strip() for m in pattern.finditer(scope)]
            if hits:
                found[name] = hits
        if found:
            out.append((path, found))
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if the count exceeds the recorded baseline")
    ap.add_argument("--list", action="store_true", help="name every module and hit")
    args = ap.parse_args(argv)

    found = offenders()
    n = len(found)
    total = sum(1 for _ in LIB.rglob("*.lean"))
    by_kind = {name: sum(len(f.get(name, [])) for _, f in found) for name, _ in KINDS}

    if args.list:
        for path, kinds in found:
            print(f"  {path.relative_to(ROOT)}")
            for name, hits in kinds.items():
                for h in sorted(set(hits))[:4]:
                    print(f"      {name}: {h}")

    summary = ", ".join(f"{k} {v}" for k, v in by_kind.items())
    hits = sum(by_kind.values())
    if n > BASELINE or hits > HIT_BASELINE:
        which = []
        if n > BASELINE:
            which.append(f"{n} modules, above the baseline of {BASELINE}")
        if hits > HIT_BASELINE:
            which.append(f"{hits} hits, above the baseline of {HIT_BASELINE}")
        print(f"submission-prose check: {' and '.join(which)}  ({summary})")
        print("  A module gained a lane id, an internal path, or dated move archaeology.")
        print("  Docstrings describe the mathematics for a reader of the destination repo;")
        print("  lane bookkeeping belongs in dev/LANES.md and the commit message.")
        print("  Provenance is NOT the target -- `Formalized by ...` stays.")
        print("  Run with --list to see them.")
        return 1 if args.check else 0

    if n < BASELINE or hits < HIT_BASELINE:
        print(f"submission-prose check: {n} of {total} modules and {hits} hits, BELOW the "
              f"baselines ({BASELINE} / {HIT_BASELINE}) -- lower `BASELINE` to {n} and "
              f"`HIT_BASELINE` to {hits}, in the commit that did the cleanup  ({summary})")
        return 0

    print(f"submission-prose check: OK ({n} of {total} modules, {hits} hits, at the "
          f"baselines of {BASELINE} / {HIT_BASELINE})  ({summary})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
