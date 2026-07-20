#!/usr/bin/env python3
"""Build and audit the arbitrary-pairwise-gap Hilbert--Schmidt theorem."""
from __future__ import annotations

import argparse
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
MODULES = [
    "Spectra.Spaces.Tensor.HilbertSchmidt",
    "DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidtBasis",
    "Spectra.YosidaHille.RectangularIntertwining",
    "Spectra.SpectralTheory.SeparatedIntertwiner",
    "DavisKahan.Experimental.InfiniteDimensional.Sylvester.PairwiseSpectrumGap",
    "DavisKahan.Sylvester.PairwiseHomogeneousUniqueness",
    "Spectra.Spaces.Tensor.HilbertSchmidtSpectralGap",
    "DavisKahan.Experimental.InfiniteDimensional.Sylvester.PaperHilbertSchmidtPairwise",
    "DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperTheorem62",
    "DavisKahan.Sources.DavisKahan1970.FullSineTheta",
]
AUDITS = [
    ROOT / "DavisKahan/Experimental/InfiniteDimensional/Sylvester/"
    "PaperHilbertSchmidtMathAheadAudit.lean",
    ROOT / "DavisKahan/Experimental/InfiniteDimensional/SinTheta/"
    "FullPaperSineThetaAudit.lean",
]
EXPECTED = "[propext, Classical.choice, Quot.sound]"


def run(cmd: list[str]) -> str:
    proc = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True)
    output = proc.stdout + proc.stderr
    if proc.returncode:
        print(output, end="")
        raise SystemExit(proc.returncode)
    return output


def static_check() -> None:
    paths = [
        ROOT / "vendor/Spectra/Spectra/Spaces/Tensor/HilbertSchmidt.lean",
        ROOT / "vendor/Spectra/Spectra/YosidaHille/RectangularIntertwining.lean",
        ROOT / "vendor/Spectra/Spectra/SpectralTheory/SeparatedIntertwiner.lean",
        ROOT / "vendor/Spectra/Spectra/Spaces/Tensor/HilbertSchmidtSpectralGap.lean",
        ROOT / "DavisKahan/Experimental/InfiniteDimensional/Sylvester/PairwiseSpectrumGap.lean",
        ROOT / "DavisKahan/Sylvester/PairwiseHomogeneousUniqueness.lean",
        ROOT / "DavisKahan/Experimental/InfiniteDimensional/Sylvester/PaperHilbertSchmidtPairwise.lean",
    ]
    forbidden = re.compile(r"\b(?:sorry|admit|native_decide)\b")
    failures: list[str] = []
    for path in paths:
        text = path.read_text()
        for line_no, line in enumerate(text.splitlines(), 1):
            if forbidden.search(line):
                failures.append(f"{path.relative_to(ROOT)}:{line_no}: {line.strip()}")
    tensor = (ROOT / "vendor/Spectra/Spectra/Spaces/Tensor/"
        "HilbertSchmidt.lean").read_text()
    stale_identifiers = [
        "norm_noninc",
        "ContinuousLinearMap.congr_fun",
        "LinearMap.rank_sum_rankOne_le",
    ]
    for identifier in stale_identifiers:
        if identifier in tensor:
            failures.append(f"HilbertSchmidt still uses unavailable identifier {identifier}")
    theorem62 = (ROOT / "DavisKahan/Experimental/InfiniteDimensional/"
        "SinTheta/PaperTheorem62.lean").read_text()
    if "Sylvester.PaperHilbertSchmidtPairwise" not in theorem62:
        failures.append("PaperTheorem62 does not import the direct pairwise engine")
    if "Sylvester.PaperHilbertSchmidt\n" in theorem62:
        failures.append("PaperTheorem62 still imports the superseded solution-first engine")
    if failures:
        print("Theorem 6.2 hard-front static audit failed:")
        print("\n".join(failures))
        raise SystemExit(1)
    print("Theorem 6.2 hard-front static audit: CLEAN")


def audit_output(output: str) -> None:
    bad: list[str] = []
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
        return
    for module in MODULES:
        run(["lake", "build", module])
    for audit in AUDITS:
        audit_output(run(["lake", "env", "lean", str(audit.relative_to(ROOT))]))
    print("Theorem 6.2 hard-front build and dependency audit: CLEAN")


if __name__ == "__main__":
    main()
