"""Long-form self-study composition for learning the mathematics and evidence."""

from __future__ import annotations

from dkvis.deck_spec import DeckSpec
from dkvis.decks.reference import ref_use

# Everything useful is in the main path here.  Only raw matrices and the notation
# glossary remain marked as backup/reference material.
STUDY_SCENES = [
    "S00Title", "S00bSetting", "S01Ellipse", "S02Perturb", "S03bWanted", "S03dCompute", "S03NoGap", "S03cUnstable",
    "S04Angle", "S04bSinThetaOperator", "S05Residual", "S06Gap", "S07Theorem", "S07bReading", "S08Why", "S08Components",
    "S09Sylvester", "S11Payoff", "S10Sharp", "S12Lean",
    "W01Workflow", "W02TwoChecks", "W03ThreeStatements",
    "D01Planes", "D02Tilt", "D03Gap", "D04Perturb", "D05TryIt",
    "F01Setup", "F01bAngles", "F01cTwoByTwo", "F02TanTheta", "F02bTanBuys", "F02cTanWhy",
    "F03SinTwoTheta", "F03bReflect", "F03cPrice", "F04TanTwoTheta", "F04bJacobi", "F04cRepulsion", "F09WhichOne", "S13Family",
    "P01Claim", "P02Counterexample", "P03Why", "P04Details",
    "W04Reversals", "W05Scale", "W06Claims", "S14Summary",
    "G01Matrices", "G02Spectra", "G03Other",
]

STUDY = DeckSpec(
    name="study",
    description="Long-form curriculum for understanding the theorem family, formalization, and evidence in detail.",
    footer=r"Davis--Kahan formalization $\cdot$ study deck",
    slides=tuple(
        ref_use(scene, core=(scene not in {"P04Details", "G01Matrices", "G02Spectra", "G03Other"}))
        for scene in STUDY_SCENES
    ),
)
