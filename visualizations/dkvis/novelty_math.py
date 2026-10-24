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


def smoothing_radius(tau: float) -> float:
    """The ``eta>1`` parameter for a positive Charbonnier smoothing scale."""
    if not math.isfinite(tau) or tau <= 0:
        raise ValueError("tau must be finite and positive")
    return (tau + math.sqrt(tau * tau + 4.0)) / 2.0


def smoothed_cutoff(tau: float) -> float:
    """The exact principal-angle threshold for canonical smoothed optimality."""
    eta = smoothing_radius(tau)
    return math.acos(eta ** -2)


def _checked_principal_angle(theta: float) -> None:
    if not math.isfinite(theta) or not 0 <= theta <= math.pi / 2:
        raise ValueError("theta must be a finite principal angle in [0, pi/2]")


def optimal_smoothed_phase(tau: float, theta: float) -> float:
    """Nonnegative attaining scalar phase for finite complex planar transport."""
    _checked_principal_angle(theta)
    eta = smoothing_radius(tau)
    if theta <= smoothed_cutoff(tau):
        return 0.0
    return math.acos(max(-1.0, min(1.0, eta * eta * math.cos(theta))))


def canonical_smoothed_cost(tau: float, theta: float) -> float:
    """Literal two-singular-value Charbonnier cost of the planar rotation."""
    _checked_principal_angle(theta)
    smoothing_radius(tau)
    return 2.0 * (math.sqrt(tau * tau + 2.0 - 2.0 * math.cos(theta)) - tau)


def optimal_smoothed_cost(tau: float, theta: float) -> float:
    """Exact global value contributed by a single principal angle."""
    _checked_principal_angle(theta)
    eta = smoothing_radius(tau)
    if theta <= smoothed_cutoff(tau):
        return canonical_smoothed_cost(tau, theta)
    return 2.0 * eta * math.sin(theta) - 2.0 * tau


def critical_phase_excess(tau: float, phase: float) -> float:
    """Actual critical planar cost excess along a feasible scalar-phase path.

    The formula is ``G(e^{i phase})`` from SmoothedCriticalFlatness.  The
    fourth-order behavior here illustrates the Lean-certified theorem.
    """
    smoothing_radius(tau)
    if not math.isfinite(phase):
        raise ValueError("phase must be finite")
    eta = smoothing_radius(tau)
    b = 1.0 / eta
    d = math.sqrt(eta * eta - b * b)
    z = complex(math.cos(phase), math.sin(phase))
    gap = abs(complex(b, d) - b * z) + abs(complex(b, -d) - b * z) - 2.0 * d
    return max(0.0, gap)
