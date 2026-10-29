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


def schatten_phase_power_three_halves(theta: float, delta: float) -> float:
    """Literal planar Schatten-3/2 displacement power for a scalar phase.

    Both angles must be physical and 0 <= delta <= theta.  This helper
    evaluates the scalar model; the Lean global theorem rules out mixing.
    """
    _checked_principal_angle(theta)
    if not math.isfinite(delta) or not 0 <= delta <= theta:
        raise ValueError("phase must satisfy 0 <= delta <= theta")
    return ((2.0 * math.sin((theta + delta) / 2.0)) ** 1.5
            + (2.0 * math.sin((theta - delta) / 2.0)) ** 1.5)


def schatten_two_angle_example_three_halves() -> dict[str, float]:
    """Two-plane C^4 witness for the formalized unrestricted sum formula."""
    low, high = math.radians(45), math.radians(80)
    delta = optimal_phase_three_halves(high)
    return {
        "cutoff_deg": math.degrees(math.acos(1 / 3)),
        "low_phase_deg": math.degrees(optimal_phase_three_halves(low)),
        "high_phase_deg": math.degrees(delta),
        "low_minimum": schatten_phase_power_three_halves(low, 0.0),
        "high_minimum": schatten_phase_power_three_halves(high, delta),
        "canonical_sum": (schatten_phase_power_three_halves(low, 0.0)
                          + schatten_phase_power_three_halves(high, 0.0)),
        "global_sum": (schatten_phase_power_three_halves(low, 0.0)
                       + schatten_phase_power_three_halves(high, delta)),
    }


def schatten_signed_phase_power_three_halves(theta: float, delta: float) -> float:
    """Symmetric signed-phase cost on a physical principal plane.

    The sign does not affect the singular-value multiset, so this model
    evaluates the existing nonnegative formula at ``abs(delta)``.
    """
    _checked_principal_angle(theta)
    if not math.isfinite(delta) or abs(delta) > theta:
        raise ValueError("signed phase must satisfy |delta| <= theta")
    return schatten_phase_power_three_halves(theta, abs(delta))


def schatten_simple_active_signs_three_halves() -> dict:
    """Exactly four independent choices for two simple active angles.

    Equal costs in these four planar constructions illustrate the compiled
    *completeness* theorem; the numerical evaluation alone would show only
    four attaining examples, not that other ambient minimizers are absent.
    """
    low, high = math.radians(75.0), math.radians(80.0)
    da, db = optimal_phase_three_halves(low), optimal_phase_three_halves(high)
    assert 0 < da < low and 0 < db < high
    phases = [(a * da, b * db) for a in (-1, 1) for b in (-1, 1)]
    costs = [
        schatten_signed_phase_power_three_halves(low, a)
        + schatten_signed_phase_power_three_halves(high, b)
        for a, b in phases
    ]
    return {
        "angles_deg": (75.0, 80.0),
        "phases_deg": (math.degrees(da), math.degrees(db)),
        "choices": phases,
        "costs": costs,
    }


def nuclear_singleton_cost(theta: float) -> float:
    """Minimum nuclear cost of one real principal-plane transporter.

    The competing branches are the planar rotation and a reflection.
    """
    _checked_principal_angle(theta)
    return min(4.0 * math.sin(theta / 2.0), 2.0)


def nuclear_pair_cost(theta: float, psi: float) -> float:
    """Coupled four-dimensional real nuclear matching edge cost."""
    _checked_principal_angle(theta)
    _checked_principal_angle(psi)
    return 4.0 * math.sin((theta + psi) / 2.0)


def real_nuclear_matching_example(angles: tuple[float, ...]) -> dict:
    """Small-rank numeric instance of the proved unrestricted real formula.

    ``angles`` are radians. The exact finite matching combinatorics are
    enumerated by a bitmask dynamic program; the trigonometric weights are
    evaluated in floating point. This is slide data, not a numerical proof
    of the ambient theorem. Original angle indices are retained in the
    returned pairs, including when repeated values are supplied.
    """
    from functools import lru_cache

    if len(angles) > 12:
        raise ValueError("slide example allows at most twelve angle labels")
    for theta in angles:
        _checked_principal_angle(theta)
    positive = tuple((index, theta) for index, theta in enumerate(angles) if theta > 0)
    n = len(positive)

    @lru_cache(maxsize=None)
    def solve(mask: int) -> tuple[float, tuple[tuple[int, int], ...]]:
        if mask == 0:
            return 0.0, ()
        least_bit = mask & -mask
        i = least_bit.bit_length() - 1
        remainder = mask ^ least_bit
        tail, choice = solve(remainder)
        best = nuclear_singleton_cost(positive[i][1]) + tail
        best_pairs = choice
        for j in range(i + 1, n):
            if remainder & (1 << j):
                tail, choice = solve(remainder ^ (1 << j))
                candidate = nuclear_pair_cost(positive[i][1], positive[j][1]) + tail
                if candidate < best - 1e-13:
                    best = candidate
                    best_pairs = ((positive[i][0], positive[j][0]),) + choice
        return best, best_pairs

    minimum, pairs = solve((1 << n) - 1)
    paired_indices = {j for a, b in pairs for j in (a, b)}
    singleton_indices = tuple(i for i, _ in positive if i not in paired_indices)
    canonical = sum(4 * math.sin(theta / 2) for theta in angles)
    complex_minimum = sum(2 * math.sin(theta) for theta in angles)
    return {
        "real_minimum": minimum,
        "complex_minimum": complex_minimum,
        "canonical_value": canonical,
        "pairs": pairs,
        "singletons": singleton_indices,
    }


def nuclear_matching_graph_example() -> dict:
    """Three labeled angles shared by the manuscript and matching slides.

    Edge weights are savings against leaving both endpoints single. Thus
    a minimum-cost partition is a maximum-weight matching; negative edges
    can be omitted. Keep costs and savings distinct in every renderer.
    """
    degrees = (30.0, 45.0, 75.0)
    angles = tuple(math.radians(t) for t in degrees)
    singletons = tuple(nuclear_singleton_cost(t) for t in angles)
    pairs = {(i, j): nuclear_pair_cost(angles[i], angles[j])
             for i in range(3) for j in range(i + 1, 3)}
    savings = {(i, j): singletons[i] + singletons[j] - cost
               for (i, j), cost in pairs.items()}
    return {
        "angles_deg": degrees,
        "angles": angles,
        "singleton_costs": singletons,
        "pair_costs": pairs,
        "savings": savings,
        "all_singletons": sum(singletons),
        **real_nuclear_matching_example(angles),
    }
