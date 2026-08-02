#!/usr/bin/env python3
"""Refuse a tree with committed merge-conflict markers, anywhere.

`dev/LANES.md` had been pushed with markers twice, which is where this started.
But the same failure is not specific to that file.
On 2026-07-30 an integration merge left markers in **two `.lean` files**, and nothing
noticed until `lake build` reported `unexpected token '<<<'` several minutes later.
The merge had reported the conflict; the report scrolled past inside a backgrounded
command that also ran the build, so it was never read.

The lesson is not "read more carefully".  A conflicted tree is detectable in under a
second without a compiler, so it should be, and this gate is that second:

    python3 scripts/check_conflict_markers.py           # report
    python3 scripts/check_conflict_markers.py --check   # exit 1 on any finding

**Run it between the merge and the build, not after.**  A build is the most expensive
way to discover a conflict marker and the slowest to point at it -- the compiler
reports a parse error at the marker, plus a cascade of duplicated-namespace errors
downstream, and the real cause is the least prominent line in the output.

There is no baseline.  A committed marker is never acceptable and never becomes
technical debt to be paid down later; it is a file that does not mean anything yet.
"""

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

#: Built from parts so this file never matches itself -- a self-flagging gate would be
#: reported as broken and then disabled, which is worse than not having it.
#:
#: The length must be EXACTLY seven, and this is the whole difference between a working
#: gate and a useless one.  A first version anchored only at the start, and its first run
#: reported ten hits, every one a decorative rule: `====...` under a Markdown heading and
#: a row of `=` in a shell script's banner.  A gate whose default output is false
#: positives gets ignored, so it may as well not exist.  Git writes seven and only seven,
#: followed by end-of-line (`=======`) or a space and a label (`<<<<<<< HEAD`).
MARKER = re.compile("^(?:" + "|".join(
    c * 7 + (r"(?: .*)?" if c != "=" else "") for c in "<=>") + ")$")

#: `.lake` is build output and vendored dependencies, neither of ours to police.  Patch
#: files under `retired/` legitimately CONTAIN marker-shaped lines as patch content --
#: `0002-dkps-complete-fork.patch` records a fork, and its body is not source we compile.
SKIP = ("/.lake/", "/retired/patches-", ".patch", ".diff")


def tracked_files() -> list[pathlib.Path]:
    """Only tracked files: an untracked scratch file with markers is not a repo defect."""
    out = subprocess.run(["git", "-C", str(ROOT), "ls-files", "-z"],
                         capture_output=True, text=True).stdout
    return [ROOT / p for p in out.split("\0") if p]


def offenders() -> list[tuple[pathlib.Path, int, str]]:
    found = []
    for path in tracked_files():
        rel = "/" + str(path.relative_to(ROOT))
        if any(s in rel for s in SKIP):
            continue
        try:
            text = path.read_text(errors="ignore")
        except (OSError, UnicodeDecodeError):
            continue          # binary or unreadable; markers there are not our problem
        if "<" * 7 not in text and "=" * 7 not in text:
            continue          # cheap pre-filter, so the common case costs one scan
        for n, line in enumerate(text.splitlines(), 1):
            if MARKER.match(line):
                found.append((path, n, line[:60]))
    return found


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="exit 1 on any finding")
    args = ap.parse_args(argv)

    found = offenders()
    if not found:
        return print("conflict-marker check: OK (no markers in any tracked file)") or 0

    files = {p for p, _, _ in found}
    print(f"conflict-marker check: {len(found)} marker(s) in {len(files)} file(s)\n")
    for path, n, line in found:
        print(f"  {path.relative_to(ROOT)}:{n}: {line}")
    print("\n  These files do not mean anything yet -- an unfinished merge was committed.")
    print("  Resolve them per hunk. Prefer that to `git checkout --theirs <file>`, which")
    print("  also discards your side's NON-conflicting edits to the same file.")
    return 1 if args.check else 0


if __name__ == "__main__":
    sys.exit(main())
