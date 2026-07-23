#!/usr/bin/env python3
"""Resolve every census declaration against the real default build target.

The census records a mathematical status per source item, but a status is an
annotation: it cannot tell you whether the declarations backing it still exist,
still carry the name written down, or are reachable from the target that CI
actually builds.  Name-only greps cannot answer that either -- they match the
short name after the last dot, so a row naming a declaration in the wrong
namespace passes vacuously.

This probe answers it directly.  It emits one Lean file that imports the
default build target and `#check`s every declaration by fully qualified name,
then compiles it.  A name that elaborates exists *and* is reachable from
`DavisKahan.All`; a name that does not is reported with the reason.  One `lake`
invocation covers the whole census.

Usage:
    python3 scripts/probe_census_declarations.py            # human report
    python3 scripts/probe_census_declarations.py --json     # machine readable
    python3 scripts/probe_census_declarations.py --check    # exit 1 on any unresolved
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
CENSUS = ROOT / "dev/davis-kahan-1970-full-source-census.json"
PROBE = ROOT / "dev/.census-probe.lean"

# The probe must see exactly what the default build target sees, so that
# "resolved" means "reachable from the build", not "exists somewhere on disk".
PREAMBLE = "import DavisKahan.All\nimport ForMathlib\n"


def census_declarations() -> list[tuple[str, str]]:
    """Return (item id, fully qualified declaration) for the whole census."""
    data = json.loads(CENSUS.read_text(encoding="utf8"))
    out: list[tuple[str, str]] = []
    for item in data["items"]:
        for decl in item.get("lean_declarations") or []:
            out.append((item["id"], decl))
    return out


# A name that must never resolve.  If the parser stops recognizing Lean's
# diagnostics, every probe silently reports success -- so the run asserts that
# this one still fails, and refuses to report at all if it does not.
CANARY = "ForMathlib.DavisKahan1970.CensusProbeCanaryMustNotResolve"


def write_probe(pairs: list[tuple[str, str]]) -> None:
    lines = [PREAMBLE]
    for index, (_, decl) in enumerate(pairs):
        lines.append(f"-- probe {index}\n#check @{decl}\n")
    lines.append(f"-- probe {len(pairs)}\n#check @{CANARY}\n")
    PROBE.write_text("".join(lines), encoding="utf8")


def run_probe() -> str:
    result = subprocess.run(
        ["lake", "env", "lean", str(PROBE.relative_to(ROOT))],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False,
    )
    return result.stdout


# Match any diagnostic carrying a line number rather than a specific message.
# Lean writes `error(lean.unknownIdentifier): Unknown identifier `X`` today and
# has changed both the tag and the quoting style before; keying on the message
# text means a silent pass the next time it changes, which is the worst
# possible failure mode for a checker.
UNKNOWN = re.compile(r"^dev/\.census-probe\.lean:(\d+):\d+: error", re.I)


def parse(output: str, pairs: list[tuple[str, str]]) -> dict[str, str]:
    """Map declaration -> "resolved" or the compiler's reason for failing."""
    # Every probe occupies two lines after the preamble, so the reported line
    # number identifies which declaration failed.
    failures: dict[int, str] = {}
    for line in output.splitlines():
        match = UNKNOWN.match(line.strip())
        if match:
            failures[int(match.group(1))] = "unresolved"
    # Recover the probe index from the emitted file rather than recomputing the
    # offset arithmetic, which silently rots if the preamble changes.
    text = PROBE.read_text(encoding="utf8").splitlines()
    line_to_index: dict[int, int] = {}
    current = None
    for number, line in enumerate(text, start=1):
        marker = re.match(r"-- probe (\d+)", line)
        if marker:
            current = int(marker.group(1))
        elif line.startswith("#check") and current is not None:
            line_to_index[number] = current
    status = {decl: "resolved" for _, decl in pairs}
    for line_number in failures:
        index = line_to_index.get(line_number)
        if index is not None:
            status[pairs[index][1]] = "unresolved"
    return status


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--verify", action="store_true",
                        help="check each row's recorded `verification` against "
                             "what the build actually resolves")
    parser.add_argument("--sync", action="store_true",
                        help="write the build-derived verification back into "
                             "the census")
    parser.add_argument("--keep", action="store_true",
                        help="keep the generated probe file for inspection")
    args = parser.parse_args()

    pairs = census_declarations()
    probed = pairs + [("__canary__", CANARY)]
    write_probe(pairs)
    try:
        output = run_probe()
        status = parse(output, probed)
    finally:
        if not args.keep and PROBE.exists():
            PROBE.unlink()

    if status.get(CANARY) == "resolved":
        print("Census declaration probe: BROKEN -- the canary resolved, so the "
              "parser is no longer recognizing Lean's diagnostics and every "
              "result below would be a false pass. Fix the parser.",
              file=sys.stderr)
        return 2
    status.pop(CANARY, None)

    unresolved = sorted({d for d, s in status.items() if s != "resolved"})
    by_item: dict[str, list[str]] = {}
    for item_id, decl in pairs:
        if status.get(decl) != "resolved":
            by_item.setdefault(item_id, []).append(decl)

    if args.json:
        print(json.dumps({
            "total": len(status),
            "resolved": len(status) - len(unresolved),
            "unresolved": unresolved,
            "unresolved_by_item": by_item,
        }, indent=2))
    else:
        print(f"Census declaration probe: {len(status) - len(unresolved)}"
              f"/{len(status)} resolve against DavisKahan.All")
        if unresolved:
            print("\nUnresolved (name is wrong, or the declaration is not "
                  "reachable from the default build target):")
            for item_id in sorted(by_item):
                print(f"  {item_id}")
                for decl in by_item[item_id]:
                    print(f"      {decl}")

    if args.verify or args.sync:
        return verify(status, sync=args.sync)

    if args.check and unresolved:
        return 1
    return 0


# Values the probe cannot infer, because they are judgements about the *shape*
# of the statement rather than about whether a name resolves.  A row carrying
# one of these keeps it, and the probe only checks the resolve/not-resolve
# facts underneath.
JUDGEMENT_VALUES = {"proved_conditional", "not_applicable", "not_compiling"}


def derive(item: dict, status: dict[str, str]) -> tuple[str, list[str]]:
    """Compute a row's verification from what the build actually resolves.

    Deriving rather than hand-maintaining is the point: a recorded status drifts
    the moment someone moves a module, and nobody notices.  A derived one is
    recomputed on every run.
    """
    decls = item.get("lean_declarations") or []
    outside = [d for d in decls if status.get(d) != "resolved"]
    inside = [d for d in decls if status.get(d) == "resolved"]

    recorded = item.get("verification")
    if recorded in JUDGEMENT_VALUES:
        # `not_compiling` is a claim about the package, which name resolution
        # cannot see -- but it cannot survive its declarations becoming
        # reachable, or the row would under-report a package that got fixed.
        if recorded == "not_compiling" and decls and not outside:
            return "proved_in_build", []
        # the judgement stands; the probe still reports which names are unguarded
        return recorded, outside
    if not decls:
        return "absent", []
    if outside and inside:
        return "partially_in_build", outside
    if outside:
        # Everything named is unreachable. Whether that is "compiles elsewhere"
        # or "does not compile at all" is a fact about the package, so it stays
        # a judgement: a row must opt in to `not_compiling` explicitly.
        return "proved_outside_build", outside
    return "proved_in_build", []


def verify(status: dict[str, str], sync: bool = False) -> int:
    """Recompute every row's verification and compare, or write it back."""
    data = json.loads(CENSUS.read_text(encoding="utf8"))
    known = set(data.get("verification_definitions", {}))
    problems: list[str] = []
    changed = 0
    for item in data["items"]:
        want, outside = derive(item, status)
        if want not in known:
            problems.append(f"{item['id']}: derived unknown value {want!r}")
        if sync:
            if item.get("verification") != want:
                changed += 1
            item["verification"] = want
            if outside:
                item["declarations_outside_build"] = outside
            else:
                item.pop("declarations_outside_build", None)
        else:
            if item.get("verification") != want:
                problems.append(
                    f"{item['id']}: records {item.get('verification')!r} but the "
                    f"build says {want!r}"
                    + (f" (unguarded: {', '.join(outside)})" if outside else ""))
            elif (item.get("declarations_outside_build") or []) != outside:
                problems.append(
                    f"{item['id']}: declarations_outside_build is stale; build "
                    f"says {outside or 'none'}")
        for blocker in item.get("blocked_by") or []:
            if blocker not in data.get("blockers", {}):
                problems.append(
                    f"{item['id']}: blocked_by names {blocker!r}, which is not "
                    f"in the blockers table")

    if sync:
        CENSUS.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                          encoding="utf8")
        print(f"Census sync: {changed} row(s) updated from the build")
        return 1 if problems else 0
    if problems:
        print("Census verification: FAILED")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    print(f"Census verification: CLEAN -- all {len(data['items'])} rows agree "
          f"with the build")
    return 0


if __name__ == "__main__":
    sys.exit(main())
