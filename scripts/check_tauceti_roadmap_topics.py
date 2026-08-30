#!/usr/bin/env python3
"""Validate the candidate Tau Ceti roadmap topic design against the import graph.

`dev/policy/tauceti-module-plan.yaml` partitions the maintained `ForTauCeti`
modules into fine-grained topics, ordered so that each is reviewable on its own
against a base Tau Ceti has already accepted.  `aiq-lean source module-plan`
enforces the three properties the first hand-drawn draft violated -- the
partition is total and disjoint, and no module imports anything assigned to a
later topic -- and derives each topic's exact prerequisites.

This script adds the layer that is specific to this proposal: the topics group
into a handful of **holistic roadmap directories** (one directory covers several
topics as its Parts).  Public roadmap prose deliberately contains no internal
topic keys, so that grouping is declared by `dev/tauceti/roadmap-topic-map.md`,
and the roadmap-level DAG it induces must be acyclic -- two roadmaps that each
contain a topic the other's topics import cannot be submitted in any order.

Usage:
    python3 scripts/check_tauceti_roadmap_topics.py           # report
    python3 scripts/check_tauceti_roadmap_topics.py --check    # exit 1 on any violation
    python3 scripts/check_tauceti_roadmap_topics.py --topic T15
    python3 scripts/check_tauceti_roadmap_topics.py --roadmaps
    python3 scripts/check_tauceti_roadmap_topics.py --needs
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
from collections import defaultdict

try:
    from aiq_lean_tools.module_plan import ModulePlanPolicy, check_module_plan
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from _external_checkouts import EXIT_UNAVAILABLE, roadmap_root  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
POLICY = ROOT / "dev/policy/tauceti-module-plan.yaml"
TOPIC_MAP = ROOT / "dev/tauceti/roadmap-topic-map.md"

#: The reserved topic-map row for topics delivered in `ForTauCeti` and
#: deliberately not proposed in any roadmap.  They are neither unowned nor part of
#: the roadmap dependency graph.
UNROADMAPPED = "(delivered, not roadmapped)"

#: The roadmap family this repository delivers.  The submodule carries 24 other
#: families whose `Suggested.lean` files are not ours.
FAMILY = "OperatorTheory"
EXTRA_LEAVES = {"BergeMaximumTheorem"}

#: Set from `--roadmap-root` in `main()`; otherwise resolved from the environment.
_ROADMAP_OVERRIDE: str | None = None


def _roadmap_dir() -> pathlib.Path:
    """The roadmap family directory inside an external TauCetiRoadmap checkout.

    Returns a non-existent path when no checkout is available; callers must ask
    `roadmap_available()` rather than treating an empty scan as a clean result.
    """
    base = roadmap_root(_ROADMAP_OVERRIDE)
    return (base / "TauCetiRoadmap") if base else (ROOT / "__no_roadmap_checkout__")


def roadmap_available() -> bool:
    return _roadmap_dir().is_dir()


def roadmap_coverage(topics) -> tuple[list, list, list, list, dict]:
    """(covered, missing, unexpected orphans, intentional orphans, dir->topics).

    A leaf roadmap is a directory containing `Suggested.lean`; family indexes and
    `internal/` are not roadmaps and are ignored by construction.
    """
    root = _roadmap_dir()
    all_leaves = ({p.parent.relative_to(root).as_posix()
                   for p in root.rglob("Suggested.lean")} if root.exists() else set())
    leaf_dirs = {d for d in all_leaves
                 if d.startswith(FAMILY + "/") or d in EXTRA_LEAVES}

    rows: dict[str, list[str]] = {}
    if TOPIC_MAP.exists():
        text = TOPIC_MAP.read_text(errors="ignore")
        row_re = re.compile(r"^\|\s*`([^`]+)`\s*\|\s*((?:T\d+[a-c]?\s*)+)\|\s*$", re.M)
        for directory, raw_keys in row_re.findall(text):
            rows[directory] = re.findall(r"T\d+[a-c]?", raw_keys)

    unroadmapped = set(rows.pop(UNROADMAPPED, []))

    declared: dict[str, list[str]] = defaultdict(list)   # topic key -> directories
    for directory, keys in rows.items():
        for key in dict.fromkeys(keys):
            declared[key].append(directory)

    known = {topic.id for topic in topics}
    covered, missing, doubled, deliberate = [], [], [], []
    for topic in topics:
        owners = declared.get(topic.id, [])
        if len(owners) > 1:
            doubled.append(f"topic {topic.id} declared by {', '.join(owners)}")
        if topic.id in unroadmapped:
            deliberate.append(f"{topic.id}  {topic.title}")
            continue
        (covered if owners else missing).append(
            (topic.id, topic.title, owners[0] if owners else None)
        )

    bogus_topics = sorted(
        f"{directory} (declares unknown topic {key})"
        for key, directories in declared.items() if key not in known
        for directory in directories)
    unmapped_leaves = sorted(leaf_dirs - set(rows))
    missing_leaves = sorted(
        f"{directory} (mapped directory has no Suggested.lean)"
        for directory in set(rows) - leaf_dirs)
    bogus_unroadmapped = sorted(f"{UNROADMAPPED} declares unknown topic {k}"
                                for k in unroadmapped if k not in known)
    orphans = unmapped_leaves + missing_leaves + bogus_topics + doubled + bogus_unroadmapped

    groups: dict[str, list[str]] = defaultdict(list)     # directory -> topics, design order
    for topic in topics:
        owners = declared.get(topic.id, [])
        if owners:
            groups[owners[0]].append(topic.id)
    return covered, missing, orphans, deliberate, dict(groups)


def roadmap_dag(groups: dict[str, list[str]], topic_needs: dict[str, set[str]]
                ) -> tuple[dict[str, set[str]], list[str]]:
    """Roadmap-level dependency DAG derived from the topic-level prerequisites.

    The coarse graph must be acyclic or the grouping is wrong: two roadmaps that
    each contain a topic the other's topics import cannot be submitted in any
    order.  This is exactly why T05-T08 live in one roadmap (geometry->norms 7
    edges, norms->geometry 3).
    """
    owner = {t: d for d, ts in groups.items() for t in ts}
    needs: dict[str, set[str]] = {d: set() for d in groups}
    for d, ts in groups.items():
        for t in ts:
            for p in topic_needs.get(t, ()):
                if p in owner and owner[p] != d:
                    needs[d].add(owner[p])
    # Kahn's algorithm; anything left over sits on a cycle.
    left = {d: set(ps) for d, ps in needs.items()}
    while True:
        ready = [d for d, ps in left.items() if not ps]
        if not ready:
            break
        for d in ready:
            del left[d]
        for ps in left.values():
            ps.difference_update(ready)
    cycles = [f"roadmap cycle through: {', '.join(sorted(left))}"] if left else []
    return needs, cycles


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="exit 1 on any violation")
    ap.add_argument("--topic", help="list the modules of one topic")
    ap.add_argument("--roadmaps", action="store_true",
                    help="which topics have a roadmap, and which do not")
    ap.add_argument("--needs", action="store_true",
                    help="print each topic's exact prerequisite topics")
    ap.add_argument("--roadmap-root", default=None,
                    help="path to a TauCetiRoadmap checkout (or set "
                         "TAUCETI_ROADMAP_ROOT); without one the coverage layer "
                         "reports UNAVAILABLE instead of guessing")
    args = ap.parse_args(argv)
    global _ROADMAP_OVERRIDE
    _ROADMAP_OVERRIDE = args.roadmap_root

    report = check_module_plan(ModulePlanPolicy.load(POLICY), root=ROOT)
    topics = report.topics
    order = {topic.id: index for index, topic in enumerate(topics)}
    needs = {topic.id: set(topic.prerequisites) for topic in topics}

    if args.topic:
        for topic in topics:
            if topic.id == args.topic:
                print(f"{topic.id} — {topic.title}  ({len(topic.modules)} modules)")
                for module in sorted(topic.modules):
                    print(f"    {module}")
                return 0
        print(f"no such topic: {args.topic}", file=sys.stderr)
        return 2

    if args.needs:
        for topic in topics:
            need = sorted(needs[topic.id], key=lambda t: order.get(t, 0))
            print(f"  {topic.id} ({len(topic.modules):3}) needs: "
                  f"{', '.join(need) if need else '— independent'}   {topic.title}")
        return 0

    if args.roadmaps:
        covered, missing, orphans, intentional, groups = roadmap_coverage(topics)
        dag, cycles = roadmap_dag(groups, needs)
        sizes = {topic.id: len(topic.modules) for topic in topics}
        print(f"roadmap coverage: {len(covered)}/{len(topics)} topics "
              f"across {len(groups)} roadmaps\n")
        for name in sorted(groups, key=lambda n: min(order[t] for t in groups[n])):
            ts = groups[name]
            total = sum(sizes[t] for t in ts)
            need = sorted(dag[name], key=lambda x: min(order[t] for t in groups[x]))
            print(f"  {name:<30} {' '.join(ts):<28} {total:3} modules  "
                  f"needs: {', '.join(need) if need else '— independent'}")
        print()
        for key, title, _ in missing:
            print(f"  MISSING  {key:<5} {title}")
        for row in orphans:
            print(f"  ORPHAN   {row} covers no topic in the design")
        for row in intentional:
            print(f"  note: {row} — delivered, not proposed by any roadmap")
        for cycle in cycles:
            print(f"  CYCLE    {cycle}")
        bad = len(missing) + len(orphans) + len(cycles)
        if bad:
            print(f"\nroadmap coverage: {bad} violation(s)")
            return 1
        print("\nroadmap coverage: OK — every roadmapped topic covered by exactly one "
              "roadmap, and the roadmap DAG is acyclic")
        return 0

    print(f"modules {report.module_count}   topics {len(topics)}   "
          f"assigned {report.module_count - len(report.unassigned)}")
    for finding in report.findings:
        if finding.code in {"module-plan-rung-seed"}:
            continue
        print(f"  {finding.code.removeprefix('module-plan-').upper()}  "
              f"{finding.location}: {finding.message}")
    bad = sum(1 for f in report.findings
              if f.level == "error" and f.code != "module-plan-rung-seed")

    # The coverage layer is part of the gate: every topic must belong to exactly
    # one roadmap directory, and the roadmap-level DAG must be acyclic. It needs an
    # external TauCetiRoadmap checkout, which this repository no longer vendors. With
    # none present the scan would find no roadmap directories at all and report every
    # topic as uncovered -- findings about the missing checkout, not about the design.
    # Say so instead.
    coverage_ran = roadmap_available()
    if coverage_ran:
        _covered, missing, orphans, _intentional, groups = roadmap_coverage(topics)
        _, cycles = roadmap_dag(groups, needs)
        for key, title, _ in missing:
            print(f"  NO ROADMAP  {key}  {title}")
        for row in orphans:
            print(f"  ORPHAN  {row} covers no topic in the design")
        for cycle in cycles:
            print(f"  CYCLE  {cycle}")
        bad += len(missing) + len(orphans) + len(cycles)
    else:
        print("  SKIP  roadmap coverage and DAG: no TauCetiRoadmap checkout; "
              "pass --roadmap-root PATH or set TAUCETI_ROADMAP_ROOT. "
              "This is not a pass -- that layer did not run.")

    if not args.check:
        print()
        for topic in topics:
            print(f"  {topic.id}  {len(topic.modules):3}  {topic.title}")
    if bad:
        print(f"\nroadmap topics: {bad} violation(s)"
              + ("" if coverage_ran else "  (roadmap coverage layer did not run)"))
        return 1
    if not coverage_ran:
        print("\nroadmap topics: module assignment is total, disjoint and acyclic; "
              "roadmap coverage UNAVAILABLE")
        return EXIT_UNAVAILABLE
    print("\nroadmap topics: OK — total, disjoint, acyclic in submission order, "
          "and every topic is covered by exactly one roadmap")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
