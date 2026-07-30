#!/usr/bin/env python3
"""Generate and maintain the hostile-review audit checklists.

The audit is a line-by-line review of every Lean file in the repository, done in
the voice of a reviewer **who does not want to inherit this code** and has to
say why: near-duplicate theorems, statements that should be split, proofs that
should be simplified, names that mislead, files in the wrong place.

Two checklists, because the findings are of two kinds:

* **`dev/audit/FILE-CHECKLIST.md`** — every file, once. Findings that live
  inside one file: a bad name, a proof that restates its own hypothesis, a
  theorem doing three things.
* **`dev/audit/GROUP-CHECKLIST.md`** — every group, reviewed *after* its files.
  Findings that only exist across files: two modules proving the same lemma,
  an abstraction used twice and inlined a third time, a split that should be a
  merge. A group cannot be reviewed before its files are, and this file records
  that dependency explicitly.

**Checkboxes are preserved across regeneration.** Rerunning after files move or
land keeps every `[x]`, adds new files unchecked, and drops vanished ones. That
is the whole reason this is generated rather than hand-written: a 795-file
checklist maintained by hand goes stale in a day, and then nobody trusts the
marks.

`ForTauCeti` is grouped by its 22 **roadmap topics** rather than by directory,
so its holistic review lands on the units that actually get submitted. Every
other library is grouped by directory.

Usage:
    python3 scripts/audit_checklist.py            # regenerate, preserving marks
    python3 scripts/audit_checklist.py --progress # counts only, no write
"""

from __future__ import annotations

import argparse
import importlib.util
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
AUDIT = ROOT / "dev/audit"
FILE_LIST = AUDIT / "FILE-CHECKLIST.md"
GROUP_LIST = AUDIT / "GROUP-CHECKLIST.md"
SKIP_PREFIX = ("retired/", "external/", ".lake/", "vendor/")
DONE_RE = re.compile(r"^\s*-\s*\[[xX]\]\s+`([^`]+)`")


def tracked_lean() -> list[str]:
    out = subprocess.run(["git", "ls-files", "*.lean"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout
    return sorted(p for p in out.splitlines()
                  if p and not p.startswith(SKIP_PREFIX))


def topic_of() -> dict[str, str]:
    """ForTauCeti module -> roadmap topic id, from the validated design."""
    spec = importlib.util.spec_from_file_location(
        "rt", ROOT / "scripts" / "check_tauceti_roadmap_topics.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    out = {}
    for key, title, mods in mod.TOPICS:
        for m in mods:
            out["ForTauCeti/" + m.replace(".", "/") + ".lean"] = f"{key} {title}"
    return out


def group_of(path: str, topics: dict[str, str]) -> str:
    if path in topics:
        return "ForTauCeti :: " + topics[path]
    if path.startswith("ForTauCeti/"):
        return "ForTauCeti :: (unassigned — fix the topic design)"
    parts = path.split("/")
    if len(parts) == 1:
        return "(root modules)"
    if parts[0] == "DavisKahan" and len(parts) > 2:
        # Experimental and Sources are large; split one level deeper
        if parts[1] in ("Experimental", "Sources") and len(parts) > 3:
            return "/".join(parts[:3])
        return "/".join(parts[:2])
    if len(parts) > 2:
        return "/".join(parts[:2])
    return parts[0]


def existing_marks(path: pathlib.Path) -> set[str]:
    if not path.exists():
        return set()
    return {m.group(1) for m in
            (DONE_RE.match(l) for l in path.read_text().splitlines()) if m}


def lines_of(rel: str) -> int:
    p = ROOT / rel
    try:
        return p.read_text().count("\n") + 1
    except OSError:
        return 0


def build():
    files = tracked_lean()
    topics = topic_of()
    groups: dict[str, list[str]] = {}
    for f in files:
        groups.setdefault(group_of(f, topics), []).append(f)
    return files, dict(sorted(groups.items()))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--progress", action="store_true",
                    help="report counts without rewriting the checklists")
    args = ap.parse_args(argv)

    files, groups = build()
    done_files = existing_marks(FILE_LIST)
    done_groups = existing_marks(GROUP_LIST)
    total_lines = sum(lines_of(f) for f in files)
    reviewed_lines = sum(lines_of(f) for f in files if f in done_files)

    if args.progress:
        print(f"files   {len(done_files & set(files))}/{len(files)} reviewed "
              f"({reviewed_lines}/{total_lines} lines)")
        print(f"groups  {len(done_groups & set(groups))}/{len(groups)} reviewed")
        pending = [g for g in groups if g not in done_groups
                   and all(f in done_files for f in groups[g])]
        print(f"groups ready for holistic review now: {len(pending)}")
        for g in pending:
            print(f"    {g}")
        return 0

    AUDIT.mkdir(parents=True, exist_ok=True)

    # ---- file checklist
    out = [FILE_HEADER.format(
        n=len(files), lines=f"{total_lines:,}", groups=len(groups),
        done=len(done_files & set(files)))]
    for g, members in groups.items():
        gl = sum(lines_of(f) for f in members)
        nd = sum(1 for f in members if f in done_files)
        out.append(f"\n### {g}\n\n"
                   f"*{len(members)} files, {gl:,} lines — {nd}/{len(members)} reviewed*\n")
        for f in sorted(members, key=lambda x: (-lines_of(x), x)):
            mark = "x" if f in done_files else " "
            out.append(f"- [{mark}] `{f}` — {lines_of(f):,} lines")
    FILE_LIST.write_text("\n".join(out) + "\n")

    # ---- group checklist
    out = [GROUP_HEADER.format(n=len(groups),
                               done=len(done_groups & set(groups)))]
    for g, members in groups.items():
        gl = sum(lines_of(f) for f in members)
        nd = sum(1 for f in members if f in done_files)
        ready = "READY" if nd == len(members) else f"blocked ({nd}/{len(members)} files)"
        mark = "x" if g in done_groups else " "
        out.append(f"- [{mark}] `{g}` — {len(members)} files, {gl:,} lines — **{ready}**")
    GROUP_LIST.write_text("\n".join(out) + "\n")

    print(f"wrote {FILE_LIST.relative_to(ROOT)}  ({len(files)} files, {len(groups)} groups)")
    print(f"wrote {GROUP_LIST.relative_to(ROOT)}")
    print(f"preserved {len(done_files)} file marks, {len(done_groups)} group marks")
    return 0


FILE_HEADER = """# Audit checklist — every file, once

**Generated by `scripts/audit_checklist.py`. Marks are preserved on
regeneration** — rerun it after files move or land; `[x]` survives, new files
appear unchecked, vanished files drop out. Do not hand-maintain this list.

{done}/{n} files reviewed · {n} files · {lines} lines · {groups} groups

## How to review

Read in the voice of a reviewer **who does not want to inherit this code** and
must justify that. For each file, look for and record:

- **near-duplicate theorems** — the same statement proved twice, or a special
  case that is really the general one with a hypothesis bolted on;
- **theorems that should be split** — a statement doing three things, so no
  consumer can cite the one part it needs;
- **proofs that should be simplified** — a tactic trace where a lemma exists, a
  coordinate argument where an abstraction exists;
- **names that mislead** — a qualifier on the wrong side, a name asserting its
  own quality (`Genuine`, `PaperFaithful`, `LiteratureComplete`), a name
  promising content the file does not have;
- **wrong placement** — a module whose path disagrees with its mathematics;
- **API shape** — a definition with no consumers, a wrapper restating one
  hypothesis, an abstraction used twice and inlined a third time.

**Write findings into a review document under `dev/audit/`, one per group**, and
mark each finding with the lane it belongs to (`{{lane:ID}}`) so
`scripts/check_lane_graph.py` can pick it up. A finding without a lane is a
complaint; a finding with a lane is work.

**Mark a file `[x]` only when its findings are written down**, not when it has
been read. An unrecorded review is indistinguishable from no review.
"""

GROUP_HEADER = """# Audit checklist — holistic group review

**Generated by `scripts/audit_checklist.py`. Marks are preserved.**

{done}/{n} groups reviewed

A group becomes **READY** only when every file in it is marked in
[`FILE-CHECKLIST.md`](FILE-CHECKLIST.md). That ordering is the point: the
cross-file findings are invisible until the files themselves have been read.

## What a group review adds that a file review cannot

- **Duplication across files** — the same lemma proved in two modules, or an
  abstraction defined twice under different names.
- **Boundaries** — a split that should be a merge, a module that is really two
  topics, a directory whose contents do not share a subject.
- **Layering** — a helper that everything imports and nothing owns; a dependency
  that points the wrong way; a `Basic.lean` that is not basic.
- **Coverage** — the result the group obviously ought to contain and does not.
- **One narrative** — whether the group reads as a designed API or as an
  accumulation. That judgement is the deliverable.

`ForTauCeti` groups are its **22 roadmap topics**, not directories, so a group
review is exactly a review of a future submission unit.
"""


if __name__ == "__main__":
    raise SystemExit(main())
