"""Working Friday-talk composition.

This is intentionally a composition, not a second implementation of the slide
scenes.  It should evolve quickly as the rendered narrative is reviewed.
"""

from __future__ import annotations

from dkvis.deck_spec import DeckSpec
from dkvis.decks.reference import ref_use

FRIDAY = DeckSpec(
    name="friday",
    description=(
        "Working talk: introduce the mathematics of sine-theta, then explain what "
        "Lean checked, what source review checked, and how those checks changed confidence."
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
    ]),
)
