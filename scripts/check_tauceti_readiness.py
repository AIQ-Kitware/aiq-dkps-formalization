#!/usr/bin/env python3
"""Measure Tau Ceti submission readiness per roadmap topic, without a build.

`ForTauCeti/README.md` sets the standard: the library should already satisfy the
**platonic ideal** Tau Ceti roadmap, so that whatever is accepted, we already
have what it needs. Most of that standard needs a human or a compiler — but four
of its stated requirements are mechanically checkable from the sources alone,
and none of them had a gate:

* **Provenance.** §5 requires *every* staged module to carry a `## Provenance`
  section recording origin, commit, authorship and extraction class. It is how
  Kitware and third-party attribution survives the move upstream, so a module
  without one cannot be submitted at all.
* **Proof escapes.** A staged module must be complete. (The literal tactic names
  are matched here; per `AGENTS.md` they are never written in prose.)
* **The 1000-line new-file limit**, which `ForTauCeti/README.md` §4 states
  outright for Tau Ceti submission.
* **Topic attribution**, so every number is reported against the roadmap topic
  that would carry the module upstream rather than as a library-wide average
  that hides where the debt actually is.

Topic assignment comes from `check_tauceti_roadmap_topics.py`, so this tool
inherits that design and cannot drift from it.

`--check` fails on a missing provenance section or a proof escape: both are
absolute blockers. Oversize files are **reported, not failed** — three exist and
splitting them is a real refactor with a build, not a hygiene sweep.

Usage:
    python3 scripts/check_tauceti_readiness.py           # per-topic report
    python3 scripts/check_tauceti_readiness.py --check    # exit 1 on a blocker
    python3 scripts/check_tauceti_readiness.py --json
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LINE_LIMIT = 1000
# Written split so this file does not itself trip a repository-wide grep for
# proof escapes; AGENTS.md forbids naming them in prose, and a scanner that
# flags its own scanner is noise.
ESCAPE_RE = re.compile(r"\b(" + "sor" + "ry|ad" + "mit|nat" + "ive_decide)\b")


def load_topics():
    spec = importlib.util.spec_from_file_location(
        "roadmap_topics", ROOT / "scripts" / "check_tauceti_roadmap_topics.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def measure() -> dict:
    topics = load_topics()
    data = topics.analyse()
    assign = data["assign"]
    titles = {k: t for k, t, _ in topics.TOPICS}
    per = {k: {"title": titles[k], "modules": 0, "no_provenance": [],
               "oversize": [], "escapes": []} for k, _, _ in topics.TOPICS}
    unplaced = []
    for path in sorted((ROOT / "ForTauCeti").rglob("*.lean")):
        name = str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")
        key = assign.get(name)
        if key is None:
            unplaced.append(name)
            continue
        text = path.read_text()
        lines = text.count("\n") + 1
        rec = per[key]
        rec["modules"] += 1
        rel = path.relative_to(ROOT).as_posix()
        if "## Provenance" not in text:
            rec["no_provenance"].append(rel)
        if lines > LINE_LIMIT:
            rec["oversize"].append((rel, lines))
        if ESCAPE_RE.search(text):
            rec["escapes"].append(rel)
    return {"per_topic": per, "unplaced": unplaced,
            "order": [k for k, _, _ in topics.TOPICS]}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="exit 1 on a missing provenance section or a proof escape")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)
    m = measure()
    per, order = m["per_topic"], m["order"]

    if args.json:
        json.dump(m, sys.stdout, indent=2)
        print()
        return 0

    total = sum(r["modules"] for r in per.values())
    prov = sum(len(r["no_provenance"]) for r in per.values())
    over = sum(len(r["oversize"]) for r in per.values())
    esc = sum(len(r["escapes"]) for r in per.values())

    if not args.check:
        print(f"{'topic':<5} {'n':>4}  {'prov':>5} {'>1k':>4} {'esc':>4}   title")
        for k in order:
            r = per[k]
            ok = r["modules"] - len(r["no_provenance"])
            flag = "" if not (r["no_provenance"] or r["oversize"] or r["escapes"]) else "  <-"
            print(f"{k:<5} {r['modules']:>4}  {ok:>2}/{r['modules']:<2} "
                  f"{len(r['oversize']):>4} {len(r['escapes']):>4}   {r['title']}{flag}")
        print()

    print(f"modules {total} | provenance {total - prov}/{total} | "
          f"over {LINE_LIMIT} lines: {over} | proof escapes: {esc}")
    for k in order:
        for rel in per[k]["no_provenance"]:
            print(f"  NO PROVENANCE   {k}  {rel}")
        for rel in per[k]["escapes"]:
            print(f"  PROOF ESCAPE    {k}  {rel}")
        for rel, n in per[k]["oversize"]:
            print(f"  OVERSIZE        {k}  {n:5} lines  {rel}")
    for name in m["unplaced"]:
        print(f"  UNPLACED        {name}")

    if args.check:
        blockers = prov + esc + len(m["unplaced"])
        if blockers:
            print(f"\nreadiness: {blockers} blocker(s)")
            return 1
        print("\nreadiness: OK — every module has provenance and no proof escapes"
              + (f" ({over} oversize, reported not failed)" if over else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
