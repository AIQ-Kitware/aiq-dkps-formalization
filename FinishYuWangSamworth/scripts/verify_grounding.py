#!/usr/bin/env python3
"""Static grounding checks for the FinishYuWangSamworth lane."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

REQUIRED_FILES = [
    "DavisKahan/Sources/YuWangSamworth2015.lean",
    "DavisKahan/Specialized/Statistics.lean",
    "DavisKahan/Specialized/SingularSubspace.lean",
    "ForTauCeti/Analysis/InnerProductSpace/AlignedBasis.lean",
    "ForTauCeti/Analysis/InnerProductSpace/SingularSubspace.lean",
    "DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidt.lean",
    "DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtFrobenius.lean",
    "FinishYuWangSamworth/FinishYuWangSamworth/Rectangular/FrobeniusGram.lean",
    "FinishYuWangSamworth/FinishYuWangSamworth/Rectangular/Theorem4.lean",
]

REQUIRED_DECLARATIONS = {
    "DavisKahan/Specialized/Statistics.lean": [
        "theorem yuWangSamworth_sinTheta_le",
        "theorem yuWangSamworth_alignedBasis_le",
        "theorem yuWangSamworth_eigenvector_le",
    ],
    "DavisKahan/Specialized/SingularSubspace.lean": [
        "theorem rightSingularSubspace_sinTheta_le",
        "theorem leftSingularSubspace_sinTheta_le",
        "theorem sq_gap_mul_sum_cross_singularVectors_le",
    ],
    "DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidt.lean": [
        "theorem paperHilbertSchmidtNorm_adjoint",
        "theorem paperHilbertSchmidtNorm_comp_le",
    ],
    "DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtFrobenius.lean": [
        "theorem paperHilbertSchmidtNorm_eq_rectangularFrobenius",
        "theorem paperHilbertSchmidtNorm_eq_frobenius",
    ],
    "FinishYuWangSamworth/FinishYuWangSamworth/Rectangular/Theorem4.lean": [
        "theorem yuWangSamworth_rightSingularSubspace_le",
        "theorem yuWangSamworth_leftSingularSubspace_le",
        "theorem yuWangSamworth_rightSingularAlignedBasis_le",
        "theorem yuWangSamworth_leftSingularAlignedBasis_le",
    ],
}

for rel in REQUIRED_FILES:
    path = ROOT / rel
    if not path.is_file():
        raise SystemExit(f"missing grounded file: {rel}")

for rel, needles in REQUIRED_DECLARATIONS.items():
    text = (ROOT / rel).read_text()
    for needle in needles:
        if needle not in text:
            raise SystemExit(f"missing grounded declaration in {rel}: {needle}")

print("FinishYuWangSamworth grounding audit: OK")
