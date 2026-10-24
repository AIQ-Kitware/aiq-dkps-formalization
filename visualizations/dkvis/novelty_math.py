"""Small numerical formulas used by the standalone spectral-transport slides.

These are illustrative evaluations of already-proved scalar identities, not
surrogates for the Lean results.  Keeping them separate from Manim lets unit
tests check the domain restrictions without importing the rendering stack.
"""

from __future__ import annotations

import math


def optimal_phase_three_halves(theta: float) -> float:
    """Optimal scalar phase for ``p=3/2`` on ``0 <= theta <= pi/2``.

    The formula ``acos(cos(theta)/(1-2*cos(theta)))`` is valid only *above*
    the critical angle ``acos(1/3)``. Below it the optimizer is zero and the
    argument of ``acos`` need not lie in ``[-1,1]``.
    """
    if not math.isfinite(theta) or not 0.0 <= theta <= math.pi / 2:
        raise ValueError("theta must be a finite principal angle in [0, pi/2]")
    if theta <= math.acos(1.0 / 3.0):
        return 0.0
    value = math.cos(theta) / (1.0 - 2.0 * math.cos(theta))
    return math.acos(max(-1.0, min(1.0, value)))
