"""Declarative slide regions for the standalone novelty presentation.

Manim measures LaTeX objects after rendering them.  Positioning separate large
objects by their *centers* without reserving space causes collisions whenever
text wraps or a formula has a tall subscript.  These cells are disjoint on
purpose: :func:`place` in ``slides_novelty`` fits each group inside its cell.

No Manim dependency here, so the layout topology is inexpensive to test.
Coordinates use the repository's 14.222 x 8 Manim frame.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Region:
    left: float
    right: float
    bottom: float
    top: float

    @property
    def width(self) -> float:
        return self.right - self.left

    @property
    def height(self) -> float:
        return self.top - self.bottom

    def overlaps(self, other: "Region") -> bool:
        return (self.left < other.right and other.left < self.right
                and self.bottom < other.top and other.bottom < self.top)


# BODY_TOP is conservative even when a kicker wraps to two lines.  Actual
# positioning clamps a region's top to the rendered header, if lower.
BODY_TOP = 1.78
BOTTOM = -3.13
L = -6.40
R = 6.40

# The slots are *content groups*. A card and its children share a single slot,
# so intentional internal contact is not incorrectly flagged as a collision.
LAYOUTS: dict[str, dict[str, Region]] = {
    "N00Title": {
        "title": Region(L, R, 2.70, 3.34),
        "subtitle": Region(L, R, 2.12, 2.61),
        "link": Region(L, R, 1.62, 2.02),
        "diagram": Region(L, -0.35, BOTTOM, 1.32),
        "prose": Region(0.23, R, BOTTOM, 1.32),
    },
    "N01ThreeStories": {
        "a": Region(L, -2.23, -2.18, BODY_TOP),
        "b": Region(-2.10, 2.10, -2.18, BODY_TOP),
        "c": Region(2.23, R, -2.18, BODY_TOP),
        "takeaway": Region(L, R, BOTTOM, -2.42),
    },
    "N02OptimizationProblem": {
        "diagram": Region(L, -0.55, -2.98, BODY_TOP),
        "definitions": Region(-0.25, R, 0.78, BODY_TOP),
        "costs": Region(-0.25, R, -2.00, 0.60),
        "note": Region(-0.25, R, BOTTOM, -2.17),
    },
    "N03LowerBound": {
        "diagram": Region(L, -0.55, -2.98, BODY_TOP),
        "theorem": Region(-0.25, R, 0.32, BODY_TOP),
        "bullets": Region(-0.25, R, -1.92, 0.16),
        "note": Region(-0.25, R, BOTTOM, -2.12),
    },
    "N04ComplexTrace": {
        "theorem": Region(L, R, 0.35, BODY_TOP),
        "construction": Region(L, -0.22, -2.40, 0.17),
        "bullets": Region(0.22, R, -2.40, 0.17),
        "takeaway": Region(L, R, BOTTOM, -2.59),
    },
    "N05SmoothedTransport": {
        "identities": Region(L, R, 0.43, BODY_TOP),
        "cost": Region(L, -0.22, -2.35, 0.20),
        "minimum": Region(0.22, R, -2.35, 0.20),
        "threshold": Region(-5.70, 5.70, BOTTOM, -2.55),
    },
    "N06SmoothedStability": {
        "theorem": Region(L, R, 0.40, BODY_TOP),
        "bullets": Region(L, -0.22, BOTTOM, 0.17),
        "interpretation": Region(0.22, R, BOTTOM, 0.17),
    },
    "N06CriticalFlatness": {
        "theorem": Region(L, R, 0.48, BODY_TOP),
        "plot": Region(L, -0.20, -2.41, 0.28),
        "explanation": Region(0.24, R, -2.41, 0.28),
        "takeaway": Region(L, R, BOTTOM, -2.59),
    },
    "N07SchattenTransition": {
        "theorem": Region(L, R, 0.41, BODY_TOP),
        "left_plot": Region(L, -0.24, -2.49, 0.20),
        "right_plot": Region(0.24, R, -2.49, 0.20),
        "left_caption": Region(L, -0.24, BOTTOM, -2.68),
        "right_caption": Region(0.24, R, BOTTOM, -2.68),
    },
    "N07GlobalSchatten": {
        "theorem": Region(L, R, 0.44, BODY_TOP),
        "planes": Region(L, -0.28, -2.29, 0.20),
        "numbers": Region(0.25, R, -2.29, 0.20),
        "takeaway": Region(L, R, BOTTOM, -2.51),
    },
    "N07NoMixingProof": {
        "theorem": Region(L, R, 0.43, BODY_TOP),
        "flow": Region(L, -0.34, -2.40, 0.20),
        "argument": Region(0.24, R, -2.40, 0.20),
        "takeaway": Region(L, R, BOTTOM, -2.60),
    },
    "N08ComplexVsReal": {
        "complex": Region(L, -0.23, -1.52, BODY_TOP),
        "real": Region(0.23, R, -1.52, BODY_TOP),
        "takeaway": Region(L, R, BOTTOM, -1.76),
    },
    "N08CommutingCorrection": {
        "diagram": Region(L, -0.66, -2.34, BODY_TOP),
        "theorem": Region(-0.29, R, -0.34, BODY_TOP),
        "bullets": Region(-0.29, R, -2.34, -0.50),
        "takeaway": Region(L, R, BOTTOM, -2.54),
    },
    "N08NumericalCorrection": {
        "plot": Region(L, 0.37, -2.43, BODY_TOP),
        "examples": Region(0.69, R, -2.43, BODY_TOP),
        "takeaway": Region(L, R, BOTTOM, -2.61),
    },
    "N09StatusBoard": {
        "strong": Region(L, -2.23, -2.14, BODY_TOP),
        "classical": Region(-2.10, 2.10, -2.14, BODY_TOP),
        "working": Region(2.23, R, -2.14, BODY_TOP),
        "takeaway": Region(L, R, BOTTOM, -2.38),
    },
}


def resolved_region(scene_name: str, name: str, content_top: float | None = None) -> Region:
    """Clamp body slots to the real header bottom when it is extra tall."""
    cell = LAYOUTS[scene_name][name]
    if cell.top == BODY_TOP and content_top is not None:
        return Region(cell.left, cell.right, cell.bottom, min(BODY_TOP, content_top - 0.12))
    return cell


def validate_layouts() -> None:
    for scene, slots in LAYOUTS.items():
        for name, slot in slots.items():
            assert -6.8 <= slot.left < slot.right <= 6.8, (scene, name, slot)
            assert -3.25 <= slot.bottom < slot.top <= 3.45, (scene, name, slot)
            for other_name, other_slot in slots.items():
                if other_name <= name:
                    continue
                assert not slot.overlaps(other_slot), (scene, name, other_name)


validate_layouts()
