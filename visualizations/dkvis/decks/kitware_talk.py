"""The completed Kitware talk, frozen as a reusable standalone composition.

The scene order and implementations are the October 9 presentation.  Keep this
manifest stable while longer and alternative explanations evolve elsewhere.
"""

from __future__ import annotations

from dkvis.deck_spec import DeckSpec
from dkvis.decks.reference import ref_use

KITWARE_TALK = DeckSpec(
    name="kitware-talk",
    description=(
        "The completed 21-scene Davis--Kahan presentation: geometry, the Lean "
        "formalization, Proposition 4.4, semantic review, and the VTK finale."
    ),
    footer=r"Davis--Kahan $\sin\Theta$ $\cdot$ LLM-assisted formalization",
    slides=tuple(ref_use(scene, core=True) for scene in [
        "S00TitleShort",
        "W00Overview",
        "W01Workflow",
        "S01Ellipse",
        "S02Perturb",
        "S03NoGap",
        "S03cUnstable",
        "S04Angle",
        "S05Residual",
        "S06Gap",
        "S07Theorem",
        "S11Payoff",
        "S12Lean",
        "P01Claim",
        "P02Counterexample",
        "P04LeanRefutation",
        "W02TwoChecks",
        "W04Reversals",
        "W06Claims",
        "S14Summary",
        "V01VTKFinale",
    ]),
)
