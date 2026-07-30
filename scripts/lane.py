#!/usr/bin/env python3
"""Claim a lane without colliding with another agent.

**Why this exists.**  On 2026-07-30 two agents claimed `FTC-EXPOSE-g1` 2m53s apart.
Both had run `git fetch --all` first.  The claim that lost was not invisible -- it was
sitting on `origin/yardrat-work`, pushed three minutes earlier -- and the agent that
missed it had checked **one** branch:

    git grep 'lane FTC-EXPOSE-g1' origin/aiq-gpu-work      # <- the bug

The lane board is replicated per agent branch and only converges when someone merges.
So "is this lane free?" is a question about **every** remote branch at once, and asking
it by hand is a step that is easy to get subtly wrong under time pressure.  This script
asks it correctly, every time.

    python3 scripts/lane.py free                  # every lane nobody holds, across all branches
    python3 scripts/lane.py check FTC-PROSE-a     # who holds it, on which branch, since when
    python3 scripts/lane.py claim FTC-PROSE-a     # check, then print the row to paste

`claim` refuses when the lane is held on any branch, and prints the holder and the
commit time so the two agents can resolve by the documented rule: **earliest claim
commit wins**, and the loser takes something else rather than negotiating.
"""

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LANES = "dev/LANES.md"

LANE_RE = re.compile(r"\{lane:([A-Za-z0-9()\-_]+)\}")
HELD_RE = re.compile(r"^(claimed|in progress|partially|blocked on)", re.I)
TERMINAL_RE = re.compile(r"^(done|released|yielded|retracted|withdrawn|superseded|closed|resolved)",
                         re.I)


def git(*args: str) -> str:
    return subprocess.run(["git", "-C", str(ROOT), *args],
                          capture_output=True, text=True).stdout


def branches() -> list[str]:
    out = git("for-each-ref", "--format=%(refname:short)", "refs/remotes/origin")
    return [b for b in out.split() if not b.endswith("/HEAD")]


def bare(cell: str) -> str:
    """Status prose with the markers and markdown emphasis stripped."""
    cell = LANE_RE.sub("", cell)
    cell = re.sub(r"\{needs:[^}]*\}", "", cell)
    return re.sub(r"^[*_`\s]+", "", cell).strip()


def rows_of(branch: str) -> list[list[str]]:
    text = git("show", f"{branch}:{LANES}")
    out = []
    for line in text.splitlines():
        if not line.startswith("|"):
            continue
        cells = re.split(r"(?<!\\)\|", line)
        if len(cells) == 7:
            out.append(cells)
    return out


def survey() -> dict[str, dict]:
    """lane -> {'state': ..., 'branch': ..., 'owner': ...} across every remote branch."""
    state: dict[str, dict] = {}
    for br in branches():
        for cells in rows_of(br):
            m = LANE_RE.search(cells[5])
            if not m:
                continue
            lane, prose = m.group(1), bare(cells[5])
            rec = state.setdefault(lane, {"state": "open", "branch": br, "owner": ""})
            if TERMINAL_RE.match(prose):
                rec.update(state="done", branch=br, owner=cells[1].strip())
            elif HELD_RE.match(prose) and rec["state"] != "done":
                rec.update(state="held", branch=br, owner=cells[1].strip())
    return state


def claim_time(lane: str, branch: str) -> str:
    """When the claim for `lane` landed on `branch`, so ties resolve on evidence."""
    # `-S` is a literal-string pickaxe; do NOT add --pickaxe-regex, because the marker
    # contains `{` and `}` and would be read as a regex quantifier.
    out = git("log", "-1", "--format=%cI", "-S", f"{{lane:{lane}}}", branch, "--", LANES)
    if out.strip():
        return out.strip()
    # fall back to the first commit whose message names the lane
    out = git("log", "-1", "--format=%cI", f"--grep={lane}", branch)
    return out.strip() or "unknown"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("free", help="lanes nobody holds, across every remote branch")
    for name in ("check", "claim"):
        s = sub.add_parser(name)
        s.add_argument("lane")
    args = ap.parse_args(argv)

    print(f"fetching {len(branches())} remote branches ...", file=sys.stderr)
    git("fetch", "--all", "--quiet")
    state = survey()

    if args.cmd == "free":
        free = sorted(k for k, v in state.items() if v["state"] == "open")
        print(f"{len(free)} lane(s) nobody holds, checked across {len(branches())} branches:\n")
        for lane in free:
            print(f"  {lane}")
        return 0

    lane = args.lane
    rec = state.get(lane)
    if rec is None:
        print(f"{lane}: no row on any branch. Post the advertisement row first.")
        return 1
    if rec["state"] != "open":
        when = claim_time(lane, rec["branch"])
        print(f"{lane} is {rec['state'].upper()} -- do not take it.")
        print(f"  held on : {rec['branch']}")
        print(f"  since   : {when}")
        print(f"  owner   : {re.sub(r'[*]+', '', rec['owner'])[:90]}")
        print()
        print("  If you already claimed it too, the documented rule is EARLIEST CLAIM")
        print("  COMMIT WINS. Compare timestamps, and the later claimant takes another")
        print("  lane rather than negotiating.")
        return 1

    print(f"{lane} is FREE across all {len(branches())} remote branches.")
    if args.cmd == "claim":
        print()
        print("Paste this row, push it BEFORE the first edit, then re-run:")
        print(f"    python3 scripts/lane.py check {lane}")
        print("to confirm nobody claimed it in the gap.\n")
        print(f"| <you> — **lane {lane}, CLAIMED** | <files> | <what and why> | "
              f"<date> | `{{lane:{lane}}}` **claimed, row pushed before the first edit** |")
    return 0


if __name__ == "__main__":
    sys.exit(main())
