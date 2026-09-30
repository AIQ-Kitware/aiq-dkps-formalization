import math

import numpy as np
import pytest

from dkvis.prop44 import Prop44Model, SQRT2


@pytest.fixture
def model():
    return Prop44Model()


def test_full_verification(model):
    model.verify()


def test_principal_angles_are_pi_over_four(model):
    np.testing.assert_allclose(model.principal_angles, [math.pi / 4, math.pi / 4])
    assert np.max(model.principal_angles) < math.pi / 3


def test_direct_rotation_is_polar_factor(model):
    np.testing.assert_allclose(
        model.canonical_intertwiner.T @ model.canonical_intertwiner,
        0.5 * np.eye(4),
    )
    np.testing.assert_allclose(model.R, SQRT2 * model.canonical_intertwiner)


def test_both_operators_carry_u_to_same_v(model):
    np.testing.assert_allclose(model.R @ model.P_U @ model.R.T, model.P_V)
    np.testing.assert_allclose(model.W @ model.P_U @ model.W.T, model.P_V)


def test_competitor_is_quarter_turn_plus_identity(model):
    local = model.m_basis.T @ model.W @ model.m_basis
    expected = np.eye(4)
    expected[:2, :2] = [[0.0, -1.0], [1.0, 0.0]]
    np.testing.assert_allclose(local, expected, atol=1e-12)


def test_displacement_singular_values(model):
    chord = math.sqrt(2.0 - math.sqrt(2.0))
    np.testing.assert_allclose(model.direct_singular_values, np.full(4, chord), atol=1e-12)
    np.testing.assert_allclose(
        model.competitor_singular_values,
        [math.sqrt(2.0), math.sqrt(2.0), 0.0, 0.0],
        atol=1e-12,
    )


def test_trace_norm_refutation(model):
    assert model.competitor_trace_displacement == pytest.approx(2.0 * math.sqrt(2.0))
    assert model.direct_trace_displacement == pytest.approx(
        4.0 * math.sqrt(2.0 - math.sqrt(2.0))
    )
    assert model.competitor_trace_displacement < model.direct_trace_displacement


def test_animation_paths_have_correct_endpoints(model):
    np.testing.assert_allclose(model.direct_rotation_at(0.0), np.eye(4))
    np.testing.assert_allclose(model.direct_rotation_at(1.0), model.R)
    np.testing.assert_allclose(model.competitor_at(0.0), np.eye(4), atol=1e-12)
    np.testing.assert_allclose(model.competitor_at(1.0), model.W, atol=1e-12)


def test_4d_projection_has_orthonormal_rows(model):
    for angle in np.linspace(0, 2 * math.pi, 9):
        P = model.projection_4d_to_3d(float(angle))
        np.testing.assert_allclose(P @ P.T, np.eye(3), atol=1e-12)


def test_projection_accepts_vectors_and_point_clouds(model):
    v = np.array([1.0, 2.0, 3.0, 4.0])
    one = model.project(v, 0.3)
    many = model.project(np.vstack([v, -v]), 0.3)
    assert one.shape == (3,)
    assert many.shape == (2, 3)
    np.testing.assert_allclose(many[0], one)
    np.testing.assert_allclose(many[1], -one)
