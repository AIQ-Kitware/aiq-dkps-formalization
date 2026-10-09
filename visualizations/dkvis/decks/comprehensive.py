"""A narrative-first composition of every distinct existing Davis--Kahan scene.

A long, self-contained presentation: intuition -> sine-theta theorem -> 3D ->
other angle bounds -> Proposition 4.4 -> checking and evidence -> notation ->
conclusion.  The 21-scene Kitware talk is separately preserved; this deck is
free to improve the previously optional/reference-only scenes.

Each reusable mathematical scene appears once.  The two legacy title classes
are the same artwork with/without an optional-depth legend; a broader cover
is used here without modifying the completed talk.  Chapter interludes provide navigation between the long
sections; they are not part of the reference or Kitware talk decks.
"""

from __future__ import annotations

from dkvis.deck_spec import DeckSpec, use
from dkvis.decks.reference import ref_use


def _chapter(scene: str):
    if scene.startswith("C0"):
        # Navigational scenes belong to this presentation, not to the preserved
        # reference-deck scene registry.
        return use("dkvis.slides_compendium", scene)
    return ref_use(scene, core=True)


# Explicit, readable ordering rather than concatenating the seven historical
# reference decks.  Revisit this order when new explanatory components arrive.
COMPREHENSIVE_SCENES = [
    # Introduction: keep the finished talk's orientation, but give this collection its own cover.
    "C00LongTitle",
    "W00Overview",
    "C01Foundations",
    # Why perturbations matter and how one chooses a subspace to compute.
    "S00bSetting",
    "S01Ellipse",
    "S02Perturb",
    "S03bWanted",
    "S03dCompute",
    "S03NoGap",
    "S03cUnstable",
    # What the directed sine measures, and how the theorem certifies it.
    "S04Angle",
    "S04bSinThetaOperator",
    "S05Residual",
    "S06Gap",
    "S07Theorem",
    "S07bReading",
    "S08Why",
    "S08Components",
    "S09Sylvester",
    "S11Payoff",
    "S10Sharp",
    "S12Lean",
    # Move from vector cartoons to actual two-dimensional subspaces in R^3.
    "C02ThreeDimensions",
    "D01Planes",
    "D02Tilt",
    "D03Gap",
    "D04Perturb",
    "D05TryIt",
    # The remaining Section 2 angle bounds, arranged theorem -> intuition -> proof.
    "C03TheoremFamily",
    "F01Setup",
    "F01bAngles",
    "F01cTwoByTwo",
    "F02TanTheta",
    "F02bTanBuys",
    "F02cTanWhy",
    "F03SinTwoTheta",
    "F03bReflect",
    "F03cPrice",
    "F04TanTwoTheta",
    "F04bJacobi",
    "F04cRepulsion",
    "F09WhichOne",
    "S13Family",
    # A source theorem that did not survive scrutiny.
    "C04Proposition",
    "P01Claim",
    "P02Counterexample",
    "P03Why",
    "P04Details",
    "P04LeanRefutation",
    # How to read the result of a formalization process responsibly.
    "C05Evidence",
    "W01Workflow",
    "W02TwoChecks",
    "W03ThreeStatements",
    "W04Reversals",
    "W05Scale",
    "W06Claims",
    # Color-coded reference for revisiting symbols in the earlier sections.
    "C06Notation",
    "G01Matrices",
    "G02Spectra",
    "G03Other",
    # Preserve the finished talk's takeaways and full-frame VTK closing image.
    "S14Summary",
    "V01VTKFinale",
]

COMPREHENSIVE = DeckSpec(
    name="comprehensive",
    description=(
        "All distinct Davis--Kahan visualization scenes in a coherent sequence, "
        "with chapter transitions and detailed reference material."
    ),
    footer=r"Davis--Kahan (1970) $\cdot$ geometry, operator theory, and formalization",
    slides=tuple(_chapter(scene) for scene in COMPREHENSIVE_SCENES),
)
