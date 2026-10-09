"""Reference deck compositions preserved from the pre-reorganization layout.

Keep these decks behaviorally stable while alternative presentations evolve.
They are the visual regression baseline for the deck/component refactor.
"""

from __future__ import annotations

from dkvis.deck_spec import DeckSpec, SlideUse

MAIN = "dkvis.slides_sine_theta"
THREE_D = "dkvis.slides_sine_theta_3d"
PROP44 = "dkvis.slides_prop44"
FAMILY = "dkvis.slides_family"
FAMILY_DETAIL = "dkvis.slides_family_detail"
PROCESS = "dkvis.slides_process"
GLOSSARY = "dkvis.slides_glossary"

TECHNICAL = {
    "S03dCompute", "S04bSinThetaOperator", "S07bReading", "S08Components", "S09Sylvester", "S10Sharp", "S13Family",
    "D02Tilt", "D03Gap", "D04Perturb", "D05TryIt",
    "F01Setup", "F01bAngles", "F01cTwoByTwo", "F02TanTheta", "F02bTanBuys", "F02cTanWhy",
    "F03SinTwoTheta", "F03bReflect", "F03cPrice", "F04TanTwoTheta", "F04bJacobi", "F04cRepulsion", "F09WhichOne",
    "P03Why",
    "W01Workflow", "W02TwoChecks", "W03ThreeStatements", "W04Reversals", "W05Scale", "W06Claims",
}
BACKUP = {"P04Details", "G01Matrices", "G02Spectra", "G03Other"}

MODULE_OF = {
    **{name: MAIN for name in [
        "S00Title", "S00TitleShort", "S00bSetting", "S01Ellipse", "S02Perturb", "S03bWanted", "S03dCompute",
        "S03NoGap", "S03cUnstable", "S04Angle", "S04bSinThetaOperator", "S05Residual", "S06Gap", "S07Theorem",
        "S07bReading", "S08Why", "S08Components", "S09Sylvester", "S10Sharp", "S11Payoff", "S12Lean", "S13Family", "S14Summary",
    ]},
    **{name: THREE_D for name in ["D01Planes", "D02Tilt", "D03Gap", "D04Perturb", "D05TryIt"]},
    **{name: FAMILY for name in ["F01Setup", "F01bAngles", "F01cTwoByTwo", "F02TanTheta", "F03SinTwoTheta", "F04TanTwoTheta"]},
    **{name: FAMILY_DETAIL for name in ["F02bTanBuys", "F02cTanWhy", "F03bReflect", "F03cPrice", "F04bJacobi", "F04cRepulsion", "F09WhichOne"]},
    **{name: PROP44 for name in ["P01Claim", "P02Counterexample", "P03Why", "P04Details", "P04LeanRefutation"]},
    **{name: PROCESS for name in ["W00Overview", "W01Workflow", "W02TwoChecks", "W03ThreeStatements", "W04Reversals", "W05Scale", "W06Claims"]},
    **{name: GLOSSARY for name in ["G01Matrices", "G02Spectra", "G03Other"]},
}


def ref_use(scene: str, *, core: bool = False) -> SlideUse:
    if core:
        depth = ""
    elif scene in BACKUP:
        depth = "**"
    elif scene in TECHNICAL:
        depth = "*"
    else:
        depth = ""
    return SlideUse(module=MODULE_OF[scene], scene=scene, depth=depth)


PART_SCENES = {
    "part1-sine-theta": [
        "S00Title", "S00bSetting", "S01Ellipse", "S02Perturb", "S03bWanted", "S03dCompute", "S03NoGap",
        "S03cUnstable", "S04Angle", "S04bSinThetaOperator", "S05Residual", "S06Gap", "S07Theorem", "S07bReading", "S08Why", "S08Components",
        "S09Sylvester", "S11Payoff", "S10Sharp", "S12Lean",
    ],
    "part2-3d": ["D01Planes", "D02Tilt", "D03Gap", "D04Perturb", "D05TryIt"],
    "part3-family": [
        "F01Setup", "F01bAngles", "F01cTwoByTwo",
        "F02TanTheta", "F02bTanBuys", "F02cTanWhy",
        "F03SinTwoTheta", "F03bReflect", "F03cPrice",
        "F04TanTwoTheta", "F04bJacobi", "F04cRepulsion",
        "F09WhichOne", "S13Family",
    ],
    "part4-prop44": ["P01Claim", "P02Counterexample", "P03Why", "P04Details"],
    "part5-process": ["W01Workflow", "W02TwoChecks", "W03ThreeStatements", "W04Reversals", "W05Scale", "W06Claims"],
    "part6-summary": ["S14Summary"],
    "part7-glossary": ["G01Matrices", "G02Spectra", "G03Other"],
}

PART_FOOTERS = {
    "part1-sine-theta": r"Part 1 $\cdot$ the Davis--Kahan $\sin\Theta$ theorem",
    "part2-3d": r"Part 2 $\cdot$ $\sin\Theta$ in three dimensions",
    "part3-family": r"Part 3 $\cdot$ the $\tan\Theta$, $\sin2\Theta$ and $\tan2\Theta$ theorems",
    "part4-prop44": r"Part 4 $\cdot$ Proposition 4.4, a printed claim that is false",
    "part5-process": r"Part 5 $\cdot$ how the formalization was built",
    "part6-summary": r"Part 6 $\cdot$ summary",
    "part7-glossary": r"Part 7 $\cdot$ notation",
}

PART_DECKS = {
    name: DeckSpec(
        name=name,
        slides=tuple(ref_use(scene) for scene in scenes),
        description=f"Reference composition: {PART_FOOTERS[name]}",
        footer=PART_FOOTERS[name],
    )
    for name, scenes in PART_SCENES.items()
}

SHORT = DeckSpec(
    name="sine-theta-short",
    slides=tuple(ref_use(scene, core=True) for scene in [
        "S00TitleShort", "S00bSetting", "S01Ellipse", "S02Perturb", "S03bWanted", "S03NoGap", "S03cUnstable", "S04Angle", "S05Residual",
        "S06Gap", "S07Theorem", "S08Why", "S11Payoff", "D01Planes", "S12Lean",
        "P01Claim", "P02Counterexample", "S14Summary",
    ]),
    description="Reference 15-minute core talk from before the deck/component reorganization.",
)

FULL_PARTS = tuple(PART_SCENES)
FULL = DeckSpec(
    name="sine-theta-full",
    slides=tuple(slide for name in FULL_PARTS for slide in PART_DECKS[name].slides),
    description="Reference full talk, assembled from the separately rendered reference parts.",
    composite_parts=FULL_PARTS,
)

REFERENCE_DECKS = {
    SHORT.name: SHORT,
    **PART_DECKS,
    FULL.name: FULL,
}
