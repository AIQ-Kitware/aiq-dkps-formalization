#!/usr/bin/env python3
"""Refuse a `dev/LANES.md` that lies to `check_lane_graph.py`.

Every collision and phantom-free-lane in this repository on 2026-07-30 came from the
board *saying* something the parser could not *read*.  The rows were honest; the query
was wrong.  Each check below is a failure that actually happened:

1. **conflict markers committed.**  `dev/LANES.md` has been pushed with `<<<<<<<` in it
   at least twice, and `dev/audit/FILE-CHECKLIST.md` once.  A file in that state parses
   as garbage and every downstream count is wrong.

2. **an unescaped `|` inside a cell.**  A claim row containing `(|lam| + 1)` split into
   9 cells instead of 7, which silently drops the row from every count.

3. **a claim or completion row with no `{lane:}` marker.**  `check_lane_graph` keys on
   the marker, so a claim without one is invisible: the lane keeps reporting READY and
   a second agent takes work someone is already doing.  This is exactly how
   `FTC-LONGPROOF` slice 1 nearly went twice.

4. **a terminal keyword that is not first.**  `TERMINAL_RE` anchors at the start of the
   status prose, so `**unclaimed - ...** ... **DONE 2026-07-30**` parses as OPEN.
   Sixteen finished lanes were advertising themselves as available this way, two of them
   holding five other lanes blocked.

5. **a lane with both a terminal row and a claimed row.**  Lane state is
   `done > held > open` across rows, so a row saying "superseded by the row below" --
   true of the row -- marks the whole LANE done and hides an in-progress claim.  Drop
   the marker from the superseded row instead.

    python3 scripts/check_lane_format.py           # report
    python3 scripts/check_lane_format.py --check   # exit 1 on any finding
"""

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LANES = ROOT / "dev/LANES.md"

#: Findings tolerated today.  Checks 1, 2 and 5 are ALWAYS fatal -- a committed conflict
#: marker, a miscounted row, or a lane whose state is self-contradictory are never
#: acceptable and have no baseline.  Only check 3 (a claim/completion row with no marker)
#: is ratcheted, because 60 historical rows predate the convention and most are terminal
#: rows for lanes already marked elsewhere.  New ones are what cause collisions, so the
#: number may only fall.  Measured 2026-07-30.
MARKERLESS_BASELINE = 57

LANE_RE = re.compile(r"\{lane:([A-Za-z0-9()\-_]+)\}")
NEEDS_RE = re.compile(r"\{needs:[^}]*\}")
SEPARATOR = re.compile(r"^\s*\|[\s:|-]+\|\s*$")
CONFLICT = re.compile(r"^(<{7}|={7}|>{7})")
#: an owner cell that announces the agent is taking or has finished the work
ANNOUNCES = re.compile(r"\b(CLAIMED|DONE|claimed|RELEASED|SUPERSEDED)\b")
TERMINAL_RE = re.compile(r"^(done|released|yielded|retracted|withdrawn|superseded|closed|resolved)",
                         re.I)
HELD_RE = re.compile(r"^(claimed|in progress|partially|blocked on)", re.I)


def bare(cell: str) -> str:
    cell = LANE_RE.sub("", NEEDS_RE.sub("", cell))
    return re.sub(r"^[*_`\s]+", "", cell).strip()


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="exit 1 on any finding")
    args = ap.parse_args(argv)

    lines = LANES.read_text().splitlines()
    findings: list[str] = []       # always fatal
    markerless: list[str] = []     # ratcheted

    for n, line in enumerate(lines, 1):
        if CONFLICT.match(line):
            findings.append(f"{LANES.name}:{n}: conflict marker committed -- {line[:40]}")

    rows = [(n, l) for n, l in enumerate(lines, 1)
            if l.startswith("|") and not SEPARATOR.match(l)]

    per_lane: dict[str, dict[str, list[int]]] = {}
    for n, line in rows:
        cells = re.split(r"(?<!\\)\|", line)
        if len(cells) != 7:
            findings.append(
                f"{LANES.name}:{n}: {len(cells)} cells, expected 7 -- an unescaped `|` "
                f"inside a cell? escape it as `\\|`")
            continue
        owner, status = cells[1], cells[5]
        m = LANE_RE.search(status)
        if m is None:
            if ANNOUNCES.search(owner):
                markerless.append(
                    f"{LANES.name}:{n}: row announces a claim/completion but carries no "
                    f"{{lane:...}} marker, so the lane graph cannot see it -- "
                    f"{re.sub(r'[*]+', '', owner).strip()[:70]}")
            continue
        lane, prose = m.group(1), bare(status)
        rec = per_lane.setdefault(lane, {"terminal": [], "held": [], "open": []})
        if TERMINAL_RE.match(prose):
            rec["terminal"].append(n)
        elif HELD_RE.match(prose):
            rec["held"].append(n)
        else:
            rec["open"].append(n)
            # A row whose OWNER cell asserts the whole lane is finished, while the
            # status does not lead with a terminal keyword.
            #
            # The owner must *begin* with the keyword, and must not qualify it: a row
            # reading `DONE - lane X slice 1 of 3` or `PARTLY DONE - ...` is reporting
            # partial progress on a lane that is correctly still open, and flagging those
            # was this check's first false-positive class.
            asserts_whole_lane = (
                TERMINAL_RE.match(bare(owner))
                and not re.search(r"\bslice\b|\bstatement\b|\bpartly\b|\bpartial\b",
                                  owner, re.I))
            if asserts_whole_lane:
                findings.append(
                    f"{LANES.name}:{n}: lane {lane} reads as OPEN because its status does "
                    f"not BEGIN with a terminal keyword, though the row says it is finished "
                    f"-- write `DONE - ...`, not `unclaimed ... DONE`")

    for lane, rec in sorted(per_lane.items()):
        if rec["terminal"] and rec["held"]:
            findings.append(
                f"{LANES.name}: lane {lane} has a terminal row (line "
                f"{rec['terminal'][0]}) and a claimed row (line {rec['held'][0]}). Lane "
                f"state is done>held>open, so the terminal row hides the active claim. "
                f"Drop the {{lane:}} marker from the superseded ROW instead.")

    bad = False
    if findings:
        print(f"lane-format check: {len(findings)} FATAL finding(s)\n")
        for f in findings:
            print(f"  {f}")
        bad = True

    if len(markerless) > MARKERLESS_BASELINE:
        print(f"\nlane-format check: {len(markerless)} markerless claim/completion rows, "
              f"ABOVE the baseline of {MARKERLESS_BASELINE}")
        print("  A NEW row announces a claim or completion without a {lane:...} marker.")
        print("  The lane graph cannot see it, so the lane keeps reporting READY and a")
        print("  second agent will take work you are already doing. Add the marker.")
        for f in markerless[MARKERLESS_BASELINE:]:
            print(f"  {f}")
        bad = True
    elif len(markerless) < MARKERLESS_BASELINE:
        print(f"lane-format check: {len(markerless)} markerless rows, BELOW the baseline "
              f"of {MARKERLESS_BASELINE} -- lower MARKERLESS_BASELINE to {len(markerless)}.")

    if bad:
        return 1 if args.check else 0

    print(f"lane-format check: OK ({len(rows)} rows, {len(per_lane)} lanes, "
          f"{len(markerless)} markerless at the baseline)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
