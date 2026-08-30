#!/usr/bin/env python3
"""Derive the Tau Ceti submission ladder from the `ForTauCeti` import graph.

`dev/tauceti/submission-ladder.md` answers "what is the most valuable
reorganization for Tau Ceti submission?" by slicing the staging library into
dependency-closed rungs, each reviewable as one topic.

**It was hand-measured, and it went stale the same day it was written.** It
recorded 127 `ForTauCeti` modules; 29 more landed hours later. Every headline
statistic in it -- median closure, leaf count, "cumulative 41 of 127" -- was then
measured against a tree that no longer existed. This tool exists so the ladder is
*derived* rather than maintained: the import graph is the source of truth, and a
number in the document that this tool does not reproduce is a bug in the
document.

A rung is a list of **seed** modules. Its *closed slice* is the dependency
closure of every seed in that rung and all earlier rungs; its *new* modules are
the ones that closure adds over the previous rung. Submitting in rung order
means each PR reviews as one topic against a base Tau Ceti has already accepted.
The seeds, the rung order, and the topic partition live in
`dev/policy/tauceti-module-plan.yaml`; the closure arithmetic is
`aiq-lean source module-plan`.

**Seeding a module used to mean three hand edits in two files**, and the gate
caught only some of them: the totals and each rung's tally were checked, the
rung's *module list* was not.  Rung G once read "34 new" above 33 bullets and
`--check` passed.  On 2026-07-31 the ladder was left red twice in one day by two
different agents, each of whom had landed a correct module and simply not known
about the second file.  `--sync` exists so the only edit is the policy file.

What stays a human decision is *which* rung a module belongs on: the rung seeds
are the submission order, an editorial judgement about what a reviewer should see
first, and deriving them from the import graph would discard exactly the
information the document is for.  Everything downstream of that choice is
generated.

Usage:
    python3 scripts/derive_tauceti_submission_ladder.py            # report
    python3 scripts/derive_tauceti_submission_ladder.py --check    # exit 1 if the doc disagrees
    python3 scripts/derive_tauceti_submission_ladder.py --sync     # rewrite the doc
    python3 scripts/derive_tauceti_submission_ladder.py --json     # machine-readable
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import statistics
import sys

try:
    from aiq_lean_tools.lean_source import scan_lean_project
    from aiq_lean_tools.module_plan import ModulePlanPolicy, check_module_plan
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )

ROOT = pathlib.Path(__file__).resolve().parents[1]
LIB = "ForTauCeti"
LADDER = ROOT / "dev/tauceti/submission-ladder.md"
POLICY = ROOT / "dev/policy/tauceti-module-plan.yaml"


def _short(module: str) -> str:
    return module[len(LIB) + 1:] if module.startswith(LIB + ".") else module


def closure_statistics() -> dict:
    """Distribution of how much each module drags in, from the source index."""
    index = scan_lean_project(ROOT)
    graph = {m: {d for d in deps if d.startswith(LIB + ".")}
             for m, deps in index.imports.items() if m.startswith(LIB + ".")}
    sizes = sorted(len(index.import_closure([m])) - 1 for m in graph)
    return {
        "total_modules": len(graph),
        "median_internal_closure": sizes[len(sizes) // 2],
        "mean_internal_closure": round(statistics.mean(sizes), 1),
        "internal_leaves": sum(1 for m in graph if not graph[m]),
        "pulling_over_30": sum(1 for s in sizes if s > 30),
        "max_closure": sizes[-1],
    }


def derive() -> dict:
    report = check_module_plan(ModulePlanPolicy.load(POLICY), root=ROOT)
    data = closure_statistics()
    data["rungs"] = [
        {
            "rung": rung.id,
            "title": rung.title,
            "new": len(rung.new_modules),
            "closed_slice": rung.closed_slice,
            "new_modules": sorted(_short(m) for m in rung.new_modules),
            "unknown_seeds": [_short(s) for s in rung.unknown_seeds],
        }
        for rung in report.rungs
    ]
    data["cumulative"] = report.rungs[-1].closed_slice if report.rungs else 0
    data["off_ladder"] = sorted(_short(m) for m in report.off_ladder)
    data["topics"] = {
        topic.id: {"title": topic.title, "modules": sorted(_short(m) for m in topic.modules)}
        for topic in report.topics
    }
    return data


def report(data: dict) -> None:
    print(f"ForTauCeti modules: {data['total_modules']}")
    print(f"  median internal closure {data['median_internal_closure']}, "
          f"mean {data['mean_internal_closure']}, max {data['max_closure']}")
    print(f"  internal leaves {data['internal_leaves']}, "
          f"pulling >30: {data['pulling_over_30']}")
    print()
    for r in data["rungs"]:
        print(f"Rung {r['rung']} — {r['title']}")
        print(f"    {r['new']} new, closed slice {r['closed_slice']}")
        for s in r["unknown_seeds"]:
            print(f"    UNKNOWN SEED (no such module): {s}")
    print()
    print(f"Cumulative on the ladder: {data['cumulative']} of {data['total_modules']}")
    print(f"Off the ladder: {len(data['off_ladder'])}")


def suggested_rung(module: str, data: dict) -> str | None:
    """The rung a module belongs on, read off its topic in the module plan.

    Every rung from G onwards *is* a topic -- the rung titles carry the topic id
    in parentheses -- so an unplaced module does not need a judgement call; it
    needs the two tables joined.  Returns `None` when the module has no topic,
    which is the only case that is genuinely a decision.
    """
    topic = next((tid for tid, row in data["topics"].items() if module in row["modules"]), None)
    if topic is None:
        return None
    for r in data["rungs"]:
        if f"({topic})" in r["title"]:
            return f"{r['rung']} — {r['title']}"
    # Rung G is stated as a range rather than a single topic ("the rest of
    # topics T01-T10"), which is why an exact `(T09)` match misses it.
    for r in data["rungs"]:
        for lo, hi in re.findall(r"T(\d\d)-T(\d\d)", r["title"]):
            if topic[1:3].isdigit() and lo <= topic[1:3] <= hi:
                return f"{r['rung']} — {r['title']}"
    return (f"no rung carries topic {topic}; either the topic is new or rung "
            f"titles and the topic table have drifted apart")


TALLY_RE = re.compile(r"^\*\*(\d+) new, (?:cumulative )?closed slice (\d+)\.\*\*$")
BULLET_RE = re.compile(r"^  - `([A-Za-z0-9_.']+)`$")


def rung_sections(text: str) -> list[tuple[str, int, int]]:
    """Each rung heading in the document, as `(key, start_line, end_line)`.

    `end_line` is the line of the next `### ` heading, or the end of the file.
    Working in line ranges rather than one big regex keeps the prose between a
    rung's tally and its bullet list untouched -- several rungs carry a
    paragraph there, and it is the part a human wrote.
    """
    lines = text.splitlines()
    heads = [(i, m.group(1)) for i, l in enumerate(lines)
             if (m := re.match(r"^### Rung (\S+) ", l))]
    out = []
    for n, (i, key) in enumerate(heads):
        end = heads[n + 1][0] if n + 1 < len(heads) else len(lines)
        out.append((key, i, end))
    return out


def bullet_block(lines: list[str], start: int, end: int) -> tuple[int, int] | None:
    """The first contiguous run of module bullets in `lines[start:end]`."""
    first = None
    for i in range(start, end):
        if BULLET_RE.match(lines[i]):
            if first is None:
                first = i
        elif first is not None:
            return (first, i)
    return (first, end) if first is not None else None


def sync(data: dict) -> int:
    """Rewrite every derived part of the ladder document from `RUNGS`."""
    if not LADDER.exists():
        print(f"ERROR: {LADDER.relative_to(ROOT)} is missing")
        return 1
    text = LADDER.read_text()
    total = data["total_modules"]
    text = re.sub(r"of \d+ `ForTauCeti` modules", f"of {total} `ForTauCeti` modules", text)
    lines = text.splitlines()
    by_key = {r["rung"]: r for r in data["rungs"]}
    changed = 0
    # back to front, so rewriting a section cannot shift the ones not yet done
    for key, start, end in reversed(rung_sections("\n".join(lines))):
        r = by_key.get(key)
        if r is None:
            print(f"WARNING: document has rung {key}, which RUNGS does not define")
            continue
        want_tally = f"**{r['new']} new, cumulative closed slice {r['closed_slice']}.**"
        for i in range(start, end):
            if TALLY_RE.match(lines[i]):
                if lines[i] != want_tally:
                    lines[i] = want_tally
                    changed += 1
                break
        span = bullet_block(lines, start, end)
        want = [f"  - `{m}`" for m in r["new_modules"]]
        if span is None:
            if want:
                print(f"WARNING: rung {key} has no bullet list to sync")
            continue
        if lines[span[0]:span[1]] != want:
            lines[span[0]:span[1]] = want
            changed += 1
    LADDER.write_text("\n".join(lines) + "\n")
    print(f"submission ladder: synced ({changed} section(s) rewritten, total {total})")
    return 0


def check(data: dict) -> int:
    """Fail when the ladder document disagrees with the tree."""
    problems: list[str] = []
    # An unplaced module is the usual cause of a stale count, and the count
    # alone names neither the module nor the fix.  Report the module first.
    for module in data["off_ladder"]:
        rung = suggested_rung(module, data)
        where = (f"seed it in rung {rung}" if rung
                 else "it has no roadmap topic, so its rung is a decision")
        problems.append(
            f"{module} is on no rung -- {where} "
            f"(the `rungs` list in dev/policy/tauceti-module-plan.yaml), then "
            f"re-sync the document with --sync")
    for r in data["rungs"]:
        for s in r["unknown_seeds"]:
            problems.append(f"rung {r['rung']} seeds a module that does not exist: {s}")
    if not LADDER.exists():
        problems.append(f"{LADDER.relative_to(ROOT)} is missing")
    else:
        text = LADDER.read_text()
        total = data["total_modules"]
        for stale in re.findall(r"of (\d+) `ForTauCeti` modules", text):
            if int(stale) != total:
                problems.append(
                    f"document says 'of {stale} ForTauCeti modules'; "
                    f"the tree has {total}")
        for r in data["rungs"]:
            pat = (rf"### Rung {r['rung']} .*?"
                   rf"\*\*(\d+) new, (?:cumulative )?closed slice (\d+)\.\*\*")
            m = re.search(pat, text, re.S)
            if not m:
                problems.append(f"rung {r['rung']}: no counts found in the document")
            elif (int(m.group(1)), int(m.group(2))) != (r["new"], r["closed_slice"]):
                problems.append(
                    f"rung {r['rung']}: document says {m.group(1)} new / slice "
                    f"{m.group(2)}; derived {r['new']} new / slice {r['closed_slice']}")
        # The rung *lists* were unchecked until 2026-07-31, which is how rung G came
        # to print 34 as its tally above 33 bullets with `--check` green.  A count
        # that agrees while the list does not is the drift nobody sees.
        lines = text.splitlines()
        by_key = {r["rung"]: r for r in data["rungs"]}
        for key, start, end in rung_sections(text):
            r = by_key.get(key)
            if r is None:
                problems.append(f"document has rung {key}, which RUNGS does not define")
                continue
            span = bullet_block(lines, start, end)
            listed = [BULLET_RE.match(lines[i]).group(1)
                      for i in range(*span)] if span else []
            if listed != r["new_modules"]:
                missing = sorted(set(r["new_modules"]) - set(listed))
                extra = sorted(set(listed) - set(r["new_modules"]))
                detail = (f"missing {missing}" if missing else "") + \
                         (("; " if missing and extra else "") +
                          f"not new here {extra}" if extra else "")
                problems.append(
                    f"rung {key}: module list disagrees with RUNGS "
                    f"({len(listed)} listed, {len(r['new_modules'])} derived"
                    + (f"; {detail}" if detail else "; same set, different order")
                    + ") -- run --sync")
    if problems:
        for p in problems:
            print(f"ERROR: {p}")
        print(f"submission ladder: STALE ({len(problems)} finding(s))")
        return 1
    print("submission ladder: OK — document agrees with the import graph")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="exit 1 if the ladder document disagrees with the tree")
    parser.add_argument("--sync", action="store_true",
                        help="rewrite the ladder document's derived parts from the policy")
    parser.add_argument("--json", action="store_true", help="machine-readable output")
    args = parser.parse_args(argv)
    data = derive()
    if args.json:
        json.dump(data, sys.stdout, indent=2)
        print()
        return 0
    if args.sync:
        return sync(data)
    if args.check:
        return check(data)
    report(data)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
