import math

import numpy as np
import pytest

from dkvis import sine_theta_3d as m3


@pytest.mark.parametrize("theta_deg", [0.0, 5.0, 30.0, 60.0, 89.0])
@pytest.mark.parametrize("phi_deg", [0.0, 35.0, 90.0, 140.0])
@pytest.mark.parametrize("lam3", [2.8, 1.3, 0.4])
def test_tilted_trial(theta_deg, phi_deg, lam3):
    cfg = m3.tilted_trial(math.radians(theta_deg), math.radians(phi_deg), (1.0, 1.6, lam3))
    cfg.verify()
    assert cfg.sin_theta == pytest.approx(math.sin(math.radians(theta_deg)), abs=1e-9)
    # Rayleigh--Ritz: the residual is orthogonal to the trial plane.
    np.testing.assert_allclose(cfg.E0.T @ cfg.R, 0.0, atol=1e-12)


def test_tilted_trial_hinge_is_shared_line():
    cfg = m3.tilted_trial(math.radians(40), math.radians(25))
    hinge, tilted = cfg.principal_vectors
    np.testing.assert_allclose(np.abs(hinge), np.abs(m3.hinge_axis(math.radians(25))), atol=1e-9)
    assert tilted @ cfg.F1 == pytest.approx(math.sin(math.radians(40)), abs=1e-9)


def test_gap_shrinks_as_trial_tilts_toward_the_unwanted_direction():
    deltas = [m3.tilted_trial(math.radians(t)).delta for t in (0, 30, 60, 85)]
    assert all(a > b for a, b in zip(deltas, deltas[1:]))


@pytest.mark.parametrize("eps", [0.0, 0.1, 0.4, 0.8])
def test_perturbed(eps):
    cfg = m3.perturbed(eps)
    cfg.verify()
    np.testing.assert_allclose(cfg.R, eps * m3.H_UNIT[:, :2], atol=1e-12)
    assert cfg.residual_norm_2 <= eps + 1e-12
    assert cfg.sin_theta <= eps / cfg.delta + 1e-12
