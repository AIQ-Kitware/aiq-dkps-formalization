"""Numeric checks for the nuclear-endpoint figures and Manim examples.

These exercise scalar costs and finite matching examples. The ambient
minimization and parity converses are certified by Lean, not by this test.
"""

from __future__ import annotations

import math

import pytest

from dkvis.novelty_math import (
    nuclear_matching_graph_example,
    nuclear_pair_cost,
    nuclear_singleton_cost,
    real_nuclear_matching_example,
)


def test_three_angle_graph_selects_best_disjoint_saving():
    example = nuclear_matching_graph_example()
    singles = example["singleton_costs"]
    baseline = example["all_singletons"]
    # All four matchings on three vertices, checked independently of the DP.
    candidates = [baseline] + [
        cost + singles[3 - i - j]
        for (i, j), cost in example["pair_costs"].items()
    ]
    assert example["real_minimum"] == pytest.approx(min(candidates))
    assert example["pairs"] == ((0, 1),)
    assert example["singletons"] == (2,)
    assert singles[2] == 2  # the 75-degree singleton uses the reflection branch
    assert example["savings"][(0, 2)] < 0 < example["savings"][(1, 2)]
    assert baseline - example["savings"][(0, 1)] == pytest.approx(example["real_minimum"])


def test_single_angle_zero_sixty_ninety_boundary():
    assert nuclear_singleton_cost(0) == 0
    assert nuclear_singleton_cost(math.pi / 3) == pytest.approx(2)
    assert nuclear_singleton_cost(math.pi / 2) == pytest.approx(2)
    assert nuclear_singleton_cost(math.pi / 4) == pytest.approx(4 * math.sin(math.pi / 8))


def test_thirty_degree_parity_visuals():
    theta = math.pi / 6
    one = real_nuclear_matching_example((theta,))
    two = real_nuclear_matching_example((theta, theta))
    assert one["real_minimum"] == pytest.approx(4 * math.sin(math.pi / 12))
    assert one["complex_minimum"] == pytest.approx(1)
    assert one["real_minimum"] > one["complex_minimum"]
    assert one["canonical_value"] == pytest.approx(one["real_minimum"])
    assert two["pairs"] == ((0, 1),)
    assert two["singletons"] == ()
    assert two["real_minimum"] == pytest.approx(2)
    assert two["complex_minimum"] == pytest.approx(2)
    assert two["canonical_value"] == pytest.approx(8 * math.sin(math.pi / 12))
    assert two["real_minimum"] < two["canonical_value"]


def test_even_acute_multiplicity_matches_complex_nuclear_floor():
    thirty, fortyfive = math.pi / 6, math.pi / 4
    example = real_nuclear_matching_example(
        (thirty, fortyfive, fortyfive, thirty, 0.0, math.pi / 2)
    )
    assert example["real_minimum"] == pytest.approx(example["complex_minimum"])
    assert set(example["pairs"]) == {(0, 3), (1, 2)}
    assert example["singletons"] == (5,)


def test_odd_acute_multiplicity_has_positive_real_complex_gap():
    theta = math.pi / 6
    odd = real_nuclear_matching_example((theta, theta, theta))
    assert odd["real_minimum"] > odd["complex_minimum"]
    assert len(odd["pairs"]) == 1
    assert len(odd["singletons"]) == 1
    with_right_angle = real_nuclear_matching_example((theta, math.pi / 2))
    assert with_right_angle["real_minimum"] > with_right_angle["complex_minimum"]
    right_only = real_nuclear_matching_example((0, math.pi / 2))
    assert right_only["real_minimum"] == pytest.approx(right_only["complex_minimum"])


def test_mismatched_acute_pair_exceeds_complex_value():
    theta, psi = math.pi / 6, math.pi / 4
    pair = real_nuclear_matching_example((theta, psi))
    assert pair["real_minimum"] == pytest.approx(nuclear_pair_cost(theta, psi))
    assert pair["real_minimum"] > pair["complex_minimum"]


def test_zero_labels_and_limits_are_explicit():
    zero_only = real_nuclear_matching_example((0.0, 0.0))
    assert zero_only["real_minimum"] == 0
    assert zero_only["pairs"] == ()
    assert zero_only["singletons"] == ()
    with pytest.raises(ValueError):
        real_nuclear_matching_example((-0.01,))
    with pytest.raises(ValueError):
        real_nuclear_matching_example((float("nan"),))
    with pytest.raises(ValueError):
        real_nuclear_matching_example((math.pi / 2,) * 13)
