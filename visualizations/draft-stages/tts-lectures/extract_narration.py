#!/usr/bin/env python3
"""Extract only the spoken portion of a staged markdown lecture.

Pure standard library. In --check mode validate one or more files and print
word-count/rough-duration diagnostics to stderr rather than stdout.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

BEGIN = "<!-- BEGIN SPOKEN LECTURE -->"
END = "<!-- END SPOKEN LECTURE -->"


def extract(path: pathlib.Path) -> str:
    data = path.read_text(encoding="utf-8")
    if data.count(BEGIN) != 1 or data.count(END) != 1:
        raise ValueError(f"{path}: expected exactly one spoken-region marker pair")
    begin = data.index(BEGIN) + len(BEGIN)
    end = data.index(END)
    if begin >= end:
        raise ValueError(f"{path}: end marker precedes begin marker")
    spoken = data[begin:end].strip()
    if not spoken:
        raise ValueError(f"{path}: empty spoken portion")
    for token in ("```", "$$", "\\[", "\\(", "<script", "<!--"):
        if token in spoken:
            raise ValueError(f"{path}: non-spoken markup {token!r} within narration")
    # Normal markdown headings are useful in source but unnecessary in speech.
    spoken = re.sub(r"(?m)^#{1,6}\s+", "", spoken)
    return spoken + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate and report word counts")
    parser.add_argument("files", nargs="+", type=pathlib.Path)
    args = parser.parse_args()
    if not args.check and len(args.files) != 1:
        parser.error("pass one input file for extraction, or use --check for multiple")
    error = False
    for path in args.files:
        try:
            spoken = extract(path)
            if args.check:
                words = len(re.findall(r"\b[\w']+\b", spoken))
                minutes_lo = words / 165
                minutes_hi = words / 130
                print(
                    f"{path}: {words} spoken words (~{minutes_lo:.1f}-{minutes_hi:.1f} min)",
                    file=sys.stderr,
                )
            else:
                sys.stdout.write(spoken)
        except (OSError, ValueError) as exc:
            print(exc, file=sys.stderr)
            error = True
    return 1 if error else 0


if __name__ == "__main__":
    raise SystemExit(main())
