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
AUDIT = ROOT / "DavisKahan/Experimental/InfiniteDimensional/SinTheta/FullPaperSineThetaAudit.lean"
EXPECTED = "[propext, Classical.choice, Quot.sound]"


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


def audit_output(output: str) -> None:
    bad = []
    for line in output.splitlines():
        if "depends on axioms:" in line and EXPECTED not in line:
            bad.append(line)
        if "sorryAx" in line:
            bad.append(line)
    if bad:
        print("Unexpected dependency output:")
        print("\n".join(bad))
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
