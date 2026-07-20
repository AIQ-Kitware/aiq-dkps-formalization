#!/usr/bin/env python3
"""Build and audit the literal Davis--Kahan 1970 sine-theta surface."""
from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
TARGET = "DavisKahan.Sources.DavisKahan1970.FullSineTheta"
AUDIT = ROOT / "DavisKahan/Sources/DavisKahan1970/Audits/FullPaperSineTheta.lean"
EXPECTED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
AXIOM_REPORT = re.compile(r"'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]")


def run(cmd: list[str]) -> str:
    proc = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True)
    output = proc.stdout + proc.stderr
    if proc.returncode:
        print(output, end="")
        raise SystemExit(proc.returncode)
    return output


def static_check() -> None:
    files = [
        *ROOT.glob("DavisKahan/Experimental/InfiniteDimensional/**/*Paper*.lean"),
        ROOT / "DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean",
    ]
    forbidden = re.compile(r"\b(?:sorry|admit|native_decide)\b")
    failures: list[str] = []
    for path in files:
        text = path.read_text()
        for number, line in enumerate(text.splitlines(), 1):
            if forbidden.search(line):
                failures.append(f"{path.relative_to(ROOT)}:{number}: {line.strip()}")
    if failures:
        print("Proof-bypass scan failed:")
        print("\n".join(failures))
        raise SystemExit(1)


def expected_report_count() -> int:
    """Number of dependency reports the audit file is required to emit."""
    return sum(
        1
        for line in AUDIT.read_text().splitlines()
        if line.strip().startswith("#print axioms")
    )


def audit_output(output: str) -> None:
    # Lean wraps long axiom lists over several lines, so a report has to be
    # matched against whitespace-normalized output rather than line by line.
    # Matching per line silently mistakes a correct wrapped report for a
    # failure, and would equally hide a bad one whose offending axiom landed on
    # a continuation line.
    normalized = " ".join(output.split())
    if "sorryAx" in normalized:
        print("Audit output depends on sorryAx:")
        print(output, end="")
        raise SystemExit(1)
    reports = list(AXIOM_REPORT.finditer(normalized))
    bad = [
        match.group(0)
        for match in reports
        if tuple(a.strip() for a in match.group("axioms").split(","))
        != EXPECTED_AXIOMS
    ]
    if bad:
        print("Unexpected dependency output:")
        print("\n".join(bad))
        raise SystemExit(1)
    # Every `#print axioms` command must actually have produced a report; a
    # missing one would otherwise pass vacuously.
    expected = expected_report_count()
    if len(reports) != expected:
        print(f"Audit emitted {len(reports)} dependency reports, expected {expected}.")
        print(output, end="")
        raise SystemExit(1)
    # The reports must be the whole output: any warning or error left over means
    # the audited surface did not elaborate cleanly.
    leftover = AXIOM_REPORT.sub("", normalized).strip()
    if leftover:
        print("Unexpected extra audit output:")
        print(leftover)
        raise SystemExit(1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--static-only", action="store_true")
    args = parser.parse_args()
    static_check()
    if args.static_only:
        print("Full paper sine-theta static audit: CLEAN")
        return
    run(["lake", "build", TARGET])
    output = run(["lake", "env", "lean", str(AUDIT.relative_to(ROOT))])
    audit_output(output)
    print("Full paper sine-theta build and dependency audit: CLEAN")


if __name__ == "__main__":
    main()
