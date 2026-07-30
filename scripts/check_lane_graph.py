#!/usr/bin/env python3
"""Report which lanes in `dev/LANES.md` are ready to take, and which are blocked.

Parallel agents need two things this file could not previously express: that a
lane can be **sliced** so several agents work it at once, and that a lane is a
**follow-on** which becomes available only when its prerequisites finish. Before
this, a follow-on was either posted as prose nobody parsed, or not posted at all
and therefore forgotten.

Two markers in a row's status cell carry it:

```text
`{lane:FTT-DEDUP}` `{needs:FTT-PROMOTE}` **BLOCKED on FTT-PROMOTE — posted now …**
```

* `{lane:ID}` names the lane. IDs are unique.
* `{needs:A,B}` lists prerequisite lane IDs. A lane is **READY** when every
  prerequisite is terminal, and **BLOCKED** otherwise.

A lane counts as terminal when its status begins `done`/`released`/`closed`/…,
which is the same test the archiver uses, so the two cannot disagree.

**Post the follow-on when you post the lane it depends on.** The point of
`{needs:}` is that a blocked lane is *visible* — it sits on the board, measured,
and flips to READY by itself when the prerequisite lands, instead of depending on
somebody remembering it existed.

Usage:
    python3 scripts/check_lane_graph.py           # ready / blocked report
    python3 scripts/check_lane_graph.py --check   # exit 1 on a cycle or dangling need
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
NEEDS_RE = re.compile(r"\{needs:([A-Za-z0-9()\-_,\s]+)\}")
TERMINAL_RE = re.compile(
    r"^(done|released|yielded|retracted|withdrawn|superseded|closed|resolved)")
# A lane whose prerequisites are met but which someone already holds is not
# available. Reporting it as READY sends two agents at the same work, which is
# the collision this whole file exists to prevent.
HELD_RE = re.compile(r"^(claimed|in progress|partially|blocked on)")


def rows(path: pathlib.Path):
    if not path.exists():
        return
    for line in path.read_text().splitlines():
        if not line.startswith("|"):
            continue
        if re.match(r"^\s*\|[\s:|-]+\|\s*$", line):
            continue
        cells = re.split(r"(?<!\\)\|", line)
        if len(cells) >= 7:
            yield cells[1], cells[5]


def bare(status: str) -> str:
    return re.sub(r"^[^A-Za-z]*", "", status).lower()


def collect() -> tuple[dict, list[str]]:
    lanes, problems = {}, []
    for path in (LANES, ARCHIVE):
        for who, status in rows(path):
            m = LANE_RE.search(status)
            if not m:
                continue
            lane = m.group(1)
            needs = []
            n = NEEDS_RE.search(status)
            if n:
                needs = [x.strip() for x in n.group(1).split(",") if x.strip()]
            # strip the markers before reading the status prose
            prose = bare(LANE_RE.sub("", NEEDS_RE.sub("", status)))
            done = bool(TERMINAL_RE.match(prose))
            held = bool(HELD_RE.match(prose))
            rec = lanes.setdefault(lane, {"needs": [], "done": False,
                                          "held": False, "who": "", "rows": 0})
            # A lane legitimately has MORE THAN ONE row: an advertisement posted
            # by one agent and a claim or completion added by another. So the
            # lane's state is the most advanced status across its rows --
            # done > held > open -- never simply the last one parsed. Reading
            # only one row is what let a completed lane keep advertising itself
            # as unclaimed on 2026-07-29.
            rec["rows"] += 1
            rec["needs"] = sorted(set(rec["needs"]) | set(needs))
            if done:
                rec["done"] = True
                rec["who"] = re.sub(r"[*~]", "", who).strip()[:58]
            elif held and not rec["done"]:
                rec["held"] = True
                rec["who"] = re.sub(r"[*~]", "", who).strip()[:58]
            elif not rec["who"]:
                rec["who"] = re.sub(r"[*~]", "", who).strip()[:58]
    return lanes, problems


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="exit 1 on a dependency cycle or a dangling prerequisite")
    ap.add_argument("--rows", action="store_true",
                    help="show how many rows each lane has")
    args = ap.parse_args(argv)
    lanes, problems = collect()

    for lane, rec in lanes.items():
        for need in rec["needs"]:
            if need not in lanes:
                problems.append(f"{lane} needs {need}, which is not a posted lane")

    # cycle detection
    colour: dict[str, int] = {}

    def visit(node: str, trail: list[str]) -> None:
        if colour.get(node) == 2:
            return
        if colour.get(node) == 1:
            problems.append("dependency cycle: " + " -> ".join(trail + [node]))
            return
        colour[node] = 1
        for nxt in lanes.get(node, {}).get("needs", []):
            if nxt in lanes:
                visit(nxt, trail + [node])
        colour[node] = 2

    for lane in lanes:
        visit(lane, [])

    ready, held, blocked, done = [], [], [], []
    for lane, rec in sorted(lanes.items()):
        if rec["done"]:
            done.append(lane)
        elif not all(lanes.get(n, {}).get("done") for n in rec["needs"]):
            pass
        elif rec["held"]:
            held.append((lane, rec["who"]))
            continue
        else:
            ready.append(lane)
            continue
        if not rec["done"]:
            waiting = [n for n in rec["needs"] if not lanes.get(n, {}).get("done")]
            blocked.append((lane, waiting))

    if not args.check:
        print(f"READY TO TAKE ({len(ready)})")
        for lane in ready:
            print(f"  {lane}")
        print(f"\nHELD ({len(held)}) — do not take")
        for lane, who in held:
            print(f"  {lane:<18} {who}")
        print(f"\nBLOCKED ({len(blocked)}) — these unblock by themselves")
        for lane, waiting in blocked:
            print(f"  {lane:<16} waiting on {', '.join(waiting)}")
        print(f"\nDONE ({len(done)}): {', '.join(done) if done else '—'}")
        if args.rows:
            multi = {k: v["rows"] for k, v in sorted(lanes.items()) if v["rows"] > 1}
            print(f"\nlanes with more than one row ({len(multi)}) — normal: an "
                  f"advertisement plus a claim or completion")
            for k, n in multi.items():
                print(f"  {k:<18} {n} rows")

    if problems:
        for p in dict.fromkeys(problems):
            print(f"ERROR: {p}", file=sys.stderr)
        print(f"\nlane graph: {len(set(problems))} problem(s)")
        return 1
    if args.check:
        print(f"lane graph: OK — {len(ready)} ready, {len(held)} held, "
              f"{len(blocked)} blocked, {len(done)} done, "
              f"no cycles or dangling prerequisites")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
