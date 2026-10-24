"""Standalone deck teaching the mathematical novelty beyond the original talk."""

from __future__ import annotations

from dkvis.deck_spec import DeckSpec, SlideUse

MODULE = "dkvis.slides_novelty"
SCENES = [
    "N00Title",
    "N01ThreeStories",
    "N02OptimizationProblem",
    "N03LowerBound",
    "N04ComplexTrace",
    "N05SmoothedTransport",
    "N06SmoothedStability",
    "N06CriticalFlatness",
    "N07SchattenTransition",
    "N08ComplexVsReal",
    "N08CommutingCorrection",
    "N08NumericalCorrection",
    "N09StatusBoard",
]


NOVELTY_TOUR = DeckSpec(
    name="novelty-tour",
    description="Standalone teaching deck for the new spectral-transport mathematics.",
    footer=r"Mathematical novelty review $\cdot$ spectral-penalty transport",
    slides=tuple(SlideUse(module=MODULE, scene=scene, depth="") for scene in SCENES),
)
