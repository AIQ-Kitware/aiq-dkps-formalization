#!/usr/bin/env python3
"""Move rows of finished lanes out of `dev/LANES.md` into `dev/LANES-COMPLETED.md`.

Step 8 of the lane loop says a completed row leaves the live board, and it is the
step agents skip most: `LANES.md` is the file every agent is told to read before
starting, so every finished row left on it is a cost on every session, and a
finished row competes for attention with a live one. Left alone the board grows
back -- it reached 661 KB before the first archive sweep and 1304 KB before the
second, at which point 328 of its 459 rows belonged to lanes that were already
terminal.

Doing it by hand is what makes it get skipped, so this does it by rule.

WHAT MOVES: every row carrying a `{lane:ID}` marker whose LANE is terminal.
Lane state is `done > held > open` across all of a lane's rows -- the same test
`check_lane_graph` uses -- so a lane with one terminal row is terminal, and all
of its rows move together. Splitting a lane's rows across the two files would
leave half its history where nobody looks for it.

WHAT STAYS, deliberately:

  * rows of lanes that are open or held;
  * rows with no `{lane:}` marker. These cannot be attributed to a lane, so
    moving them would be a guess. Most predate the marker convention and are
    the ones `check_lane_format`'s markerless ratchet already tolerates;
    leaving them also keeps that count at its baseline rather than moving the
    goalposts;
  * the table header and separator, and therefore the rows under them -- the
    markerless rows directly beneath keep the one actually-rendered table from
    becoming a header with no body.

NOTHING IS HIDDEN. `check_lane_graph` reads `LANES.md` and `LANES-COMPLETED.md`
together, so archived lanes still resolve and `{needs:}` references still point
at something. Rows move verbatim and in order, which is what the archive's own
header promises.

Rows already present in the archive are not appended twice: repeated merges
duplicate rows on the live board, and importing that churn is how the archive
grew four duplicate rows of its own.

Usage:
    python3 scripts/archive_completed_lanes.py            # move them
    python3 scripts/archive_completed_lanes.py --check    # exit 1 if any are due
    python3 scripts/archive_completed_lanes.py --dry-run  # report, change nothing
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LANES = ROOT / "dev/LANES.md"
ARCHIVE = ROOT / "dev/LANES-COMPLETED.md"

LANE_RE = re.compile(r"\{lane:([A-Za-z0-9()\-_]+)\}")
NEEDS_RE = re.compile(r"\{needs:[^}]*\}")
SEPARATOR = re.compile(r"^\s*\|[\s:|-]+\|\s*$")
# Kept identical to check_lane_graph's tests on purpose: if these drift, the
# archiver and the state report disagree about what "finished" means.
TERMINAL_RE = re.compile(
    r"^(done|released|yielded|retracted|withdrawn|superseded|closed|resolved)", re.I)
HELD_RE = re.compile(r"^(claimed|in progress|partially|blocked on)", re.I)
RANK = {"open": 0, "held": 1, "done": 2}


def bare(cell: str) -> str:
    cell = LANE_RE.sub("", NEEDS_RE.sub("", cell))
    return re.sub(r"^[*_`\s]+", "", cell).strip()


def row_cells(line: str) -> list[str] | None:
    if not line.startswith("|") or SEPARATOR.match(line):
        return None
    if line.strip().startswith("| agent |"):
        return None
    cells = re.split(r"(?<!\\)\|", line)
    return cells if len(cells) == 7 else None


def lane_states(lines: list[str]) -> dict[str, str]:
    state: dict[str, str] = {}
    for line in lines:
        cells = row_cells(line)
        if not cells:
            continue
        marker = LANE_RE.search(cells[5])
        if not marker:
            continue
        prose = bare(cells[5])
        s = "done" if TERMINAL_RE.match(prose) else (
            "held" if HELD_RE.match(prose) else "open")
        if RANK[s] >= RANK.get(state.get(marker.group(1), "open"), 0):
            state[marker.group(1)] = s
    return state


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if any finished row is still on the live board")
    ap.add_argument("--dry-run", action="store_true",
                    help="report what would move, change nothing")
    args = ap.parse_args(argv)

    lines = LANES.read_text().split("\n")
    state = lane_states(lines)
    archived = {l.rstrip("\n") for l in ARCHIVE.read_text().split("\n")
                if l.startswith("|")}

    keep: list[str] = []
    move: list[str] = []
    already = 0
    for line in lines:
        cells = row_cells(line)
        marker = LANE_RE.search(cells[5]) if cells else None
        if marker and state[marker.group(1)] == "done":
            if line in archived:
                already += 1          # a merge put it back on the live board
            else:
                move.append(line)
                archived.add(line)
            continue
        keep.append(line)

    lanes_moved = sorted({LANE_RE.search(row_cells(l)[5]).group(1) for l in move})
    due = len(move) + already

    if args.check:
        if due:
            print(f"archive check: {due} finished row(s) still on the live board "
                  f"across {len(lanes_moved)} lane(s) -- run "
                  f"scripts/archive_completed_lanes.py", file=sys.stderr)
            return 1
        print("archive check: OK (no finished rows on the live board)")
        return 0

    if args.dry_run:
        print(f"would move {len(move)} row(s) across {len(lanes_moved)} lane(s); "
              f"{already} already in the archive")
        for lane in lanes_moved:
            print(f"  {lane}")
        return 0

    if not due:
        print("nothing to archive")
        return 0

    LANES.write_text("\n".join(keep))
    if move:
        body = ARCHIVE.read_text().rstrip("\n")
        ARCHIVE.write_text(body + "\n" + "\n".join(move) + "\n")
    print(f"archived {len(move)} row(s) across {len(lanes_moved)} lane(s); "
          f"{already} already present and not duplicated; "
          f"live board now {sum(1 for l in keep if l.startswith('|'))} rows")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
