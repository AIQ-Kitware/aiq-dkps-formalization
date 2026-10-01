import math

import numpy as np
import pytest

from dkvis import sine_theta_story as story


@pytest.mark.parametrize("gap", [0.0, 0.02, 0.1, 0.5, 1.0, 3.0])
def test_perturbed_pair_closed_forms(gap):
    pair = story.PerturbedPair(gap=gap, eps=story.PERTURBATION_EPS)
    pair.verify()


def test_perturbed_pair_rotation_approaches_45_degrees():
    pair = story.PerturbedPair(gap=1e-9, eps=story.PERTURBATION_EPS)
    assert math.degrees(pair.theta) == pytest.approx(45.0, abs=1e-6)
    assert pair.eigenvalue_shift <= story.PERTURBATION_EPS


@pytest.mark.parametrize("gap", [0.0, story.PERTURBATION_END_GAP, 0.24, 1.0])
@pytest.mark.parametrize("phi_degrees", [0.0, 30.0, 90.0, 150.0, 180.0, 225.0, 270.0, 330.0])
def test_perturbed_pair_turned_perturbation(gap, phi_degrees):
    pair = story.PerturbedPair(gap=gap, eps=story.PERTURBATION_EPS, phi=math.radians(phi_degrees))
    pair.verify()
    assert np.linalg.norm(pair.H, 2) == pytest.approx(story.PERTURBATION_EPS)


def _spin(gap):
    eps = story.PERTURBATION_EPS
    return [story.PerturbedPair(gap=gap, eps=eps, phi=phi) for phi in np.linspace(0, 2 * np.pi, 721)]


def test_with_a_gap_turning_h_only_wobbles_the_eigenvector():
    gap, eps = story.PERTURBATION_START_GAP, story.PERTURBATION_EPS
    worst = max(p.line_angle for p in _spin(gap))
    assert worst == pytest.approx(0.5 * math.asin(2 * eps / gap), abs=1e-4)
    assert math.degrees(worst) < 7.0


def test_without_a_gap_turning_h_turns_the_eigenvector_everywhere():
    pairs = _spin(story.PERTURBATION_END_GAP)
    assert max(math.degrees(p.line_angle) for p in pairs) > 89.0
    assert all(p.eigenvalue_shift <= story.PERTURBATION_EPS + 1e-12 for p in pairs)
    plus = story.PerturbedPair(gap=story.PERTURBATION_END_GAP, eps=story.PERTURBATION_EPS)
    minus = story.PerturbedPair(gap=story.PERTURBATION_END_GAP, eps=story.PERTURBATION_EPS, phi=-math.pi / 2)
    assert np.linalg.norm(plus.perturbed - minus.perturbed, 2) == pytest.approx(2 * story.PERTURBATION_EPS)
    between = story.line_angle(plus.perturbed_top_eigenvector, minus.perturbed_top_eigenvector)
    assert math.degrees(between) > 85.0


def test_perturbed_pair_bound_is_asymptotically_tight():
    pair = story.PerturbedPair(gap=200.0, eps=0.12)
    assert pair.sin_theta / pair.bound == pytest.approx(1.0, abs=1e-5)


@pytest.mark.parametrize("phi_degrees", [0.0, 10.0, 35.0, 45.0, 70.0, 90.0])
def test_rayleigh_residual(phi_degrees):
    model = story.RayleighResidual(*story.RESIDUAL_EIGENVALUES, math.radians(phi_degrees))
    model.verify()


def test_rayleigh_residual_vanishes_on_eigenvectors():
    for phi in (0.0, math.pi / 2):
        model = story.RayleighResidual(*story.RESIDUAL_EIGENVALUES, phi)
        assert model.residual_norm == pytest.approx(0.0, abs=1e-12)


def test_component_example():
    ex = story.COMPONENT_EXAMPLE
    ex.verify()
    # The slide's picture: two eigenvalues in the window, and unwanted
    # eigenvalues on both sides of it.
    assert ex.wanted.sum() == 2
    assert np.any(ex.lam[~ex.wanted] < ex.rho)
    assert np.any(ex.lam[~ex.wanted] > ex.rho)
    # The closest unwanted eigenvalue sits exactly at distance delta.
    assert ex.weights[~ex.wanted].min() == pytest.approx(ex.delta)


def test_gap_example_satisfies_the_hypothesis():
    g = story.gap_picture_example()
    lo, hi = g["beta"] - g["delta"], g["alpha"] + g["delta"]
    assert all(g["beta"] <= a <= g["alpha"] for a in g["ritz"])
    assert all(not (lo < lam < hi) for lam in g["unwanted"])


def test_sylvester_example():
    ex = story.SYLVESTER_EXAMPLE
    ex.verify()
    g = story.gap_picture_example()
    # The grid uses the gap slide's spectra, so the two pictures agree.
    assert set(ex.a) == set(g["ritz"])
    assert set(ex.lam) <= set(g["unwanted"])


def test_two_directions_example():
    ex = story.TWO_DIRECTIONS
    ex.verify()
    # The residual has a wanted-direction part too, so the bound is strict here.
    assert abs(ex.u_part) > 0.1
    assert ex.model.residual_norm > ex.delta * ex.sin_theta + 0.05
