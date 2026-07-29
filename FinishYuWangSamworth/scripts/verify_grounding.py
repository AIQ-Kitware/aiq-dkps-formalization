#!/usr/bin/env python3
"""Static grounding checks for the FinishYuWangSamworth lane."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

REQUIRED_FILES = [
    "ForTauCeti/Analysis/InnerProductSpace/YuWangSamworth/Residual.lean",
    "ForTauCeti/Analysis/InnerProductSpace/YuWangSamworth/Statistics.lean",
    "ForTauCeti/Analysis/InnerProductSpace/YuWangSamworth/SingularSubspace.lean",
    "ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean",
    "DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidt.lean",
    "DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtFrobenius.lean",
    "FinishYuWangSamworth/FinishYuWangSamworth/Symmetric/Theorem1.lean",
    "FinishYuWangSamworth/FinishYuWangSamworth/Symmetric/AngleIdentity.lean",
    "FinishYuWangSamworth/FinishYuWangSamworth/Rectangular/FrobeniusGram.lean",
    "FinishYuWangSamworth/FinishYuWangSamworth/Rectangular/Theorem4.lean",
    "FinishYuWangSamworth/FinishYuWangSamworth/Rectangular/RankOne.lean",
    "FinishYuWangSamworth/FinishYuWangSamworth/Appendix/Lemma5.lean",
]

REQUIRED_DECLARATIONS = {
    "ForTauCeti/Analysis/InnerProductSpace/YuWangSamworth/Statistics.lean": [
        "theorem yuWangSamworth_sinTheta_le",
        "theorem yuWangSamworth_alignedBasis_le",
        "theorem yuWangSamworth_eigenvector_le",
    ],
    "ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean": [
        "theorem sinTheta_perturbation_le",
        "theorem opNorm_sinThetaMap_le_of_intervalGap",
    ],
    "FinishYuWangSamworth/FinishYuWangSamworth/Symmetric/Theorem1.lean": [
        "theorem yuWangSamworth_theorem1_uiNorm_le",
        "theorem yuWangSamworth_theorem1_frobenius_le",
        "theorem yuWangSamworth_theorem1_opNorm_le",
    ],
    "FinishYuWangSamworth/FinishYuWangSamworth/Symmetric/AngleIdentity.lean": [
        "theorem yuWangSamworth_equation4",
        "theorem yuWangSamworth_equation4_printed_counterexample",
    ],
    "FinishYuWangSamworth/FinishYuWangSamworth/Rectangular/Theorem4.lean": [
        "theorem yuWangSamworth_rightSingularSubspace_le",
        "theorem yuWangSamworth_leftSingularSubspace_le",
        "theorem yuWangSamworth_rightSingularAlignedBasis_le",
        "theorem yuWangSamworth_leftSingularAlignedBasis_le",
    ],
    "FinishYuWangSamworth/FinishYuWangSamworth/Rectangular/RankOne.lean": [
        "theorem yuWangSamworth_rightSingularVector_le",
        "theorem yuWangSamworth_leftSingularVector_le",
    ],
    "FinishYuWangSamworth/FinishYuWangSamworth/Appendix/Lemma5.lean": [
        "theorem yuWangSamworth_lemma5_columns",
        "theorem yuWangSamworth_lemma5_isometricColumns",
        "theorem yuWangSamworth_lemma5_orthonormalColumns",
        "theorem yuWangSamworth_lemma5_rows",
        "theorem yuWangSamworth_lemma5_orthonormalRows",
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

lane = ROOT / "FinishYuWangSamworth"
for path in lane.rglob("*.lean"):
    text = path.read_text()
    for forbidden in ("sorry", "axiom "):
        if forbidden in text:
            raise SystemExit(f"forbidden placeholder in {path.relative_to(ROOT)}: {forbidden}")

print("FinishYuWangSamworth grounding audit: OK")
