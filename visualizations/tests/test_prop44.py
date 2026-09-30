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




def _rotation(angle):
    c = math.cos(angle)
    s = math.sin(angle)
    return np.array([[c, -s], [s, c]], dtype=float)


def test_direct_rotation_splits_into_two_exact_2d_planes(model):
    for basis, angle in zip(model.direct_plane_bases, model.direct_plane_angles):
        np.testing.assert_allclose(basis.T @ basis, np.eye(2), atol=1e-12)
        np.testing.assert_allclose(
            model.local_operator(model.R, basis),
            _rotation(angle),
            atol=1e-12,
        )


def test_competitor_splits_into_moving_and_fixed_2d_planes(model):
    moving, fixed = model.competitor_plane_bases
    np.testing.assert_allclose(
        model.local_operator(model.W, moving),
        _rotation(math.pi / 2.0),
        atol=1e-12,
    )
    np.testing.assert_allclose(
        model.local_operator(model.W, fixed),
        np.eye(2),
        atol=1e-12,
    )


def test_competitor_plane_views_show_actual_projected_u_components(model):
    moving, fixed = model.competitor_plane_bases
    e0, e1 = model.u_basis[:, 0], model.u_basis[:, 1]
    moving_coords_e0 = moving.T @ e0
    moving_coords_e1 = moving.T @ e1
    fixed_coords_e0 = fixed.T @ e0
    fixed_coords_e1 = fixed.T @ e1
    scale = 1.0 / math.sqrt(2.0)
    np.testing.assert_allclose(moving_coords_e0, [scale, 0.0], atol=1e-12)
    np.testing.assert_allclose(moving_coords_e1, [0.0, scale], atol=1e-12)
    np.testing.assert_allclose(fixed_coords_e0, [scale, 0.0], atol=1e-12)
    np.testing.assert_allclose(fixed_coords_e1, [0.0, scale], atol=1e-12)


def test_plane_trace_contributions_reconstruct_full_trace_norms(model):
    direct = [
        model.rotation_plane_trace_displacement(angle)
        for angle in model.direct_plane_angles
    ]
    competitor = [
        model.rotation_plane_trace_displacement(angle)
        for angle in model.competitor_plane_angles
    ]
    assert direct[0] == pytest.approx(direct[1])
    assert sum(direct) == pytest.approx(model.direct_trace_displacement)
    assert competitor[1] == pytest.approx(0.0)
    assert sum(competitor) == pytest.approx(model.competitor_trace_displacement)
    assert sum(competitor) < sum(direct)


def test_direct_endpoint_frames_match_rotated_source_frames(model):
    for idx, angle in enumerate(model.direct_plane_angles):
        expected = _rotation(angle) @ model.direct_source_local_frames[idx]
        np.testing.assert_allclose(
            expected,
            model.direct_endpoint_local_frames[idx],
            atol=1e-12,
        )


def test_competitor_endpoint_frames_match_rotated_source_frames(model):
    for idx, angle in enumerate(model.competitor_plane_angles):
        expected = _rotation(angle) @ model.competitor_source_local_frames[idx]
        np.testing.assert_allclose(
            expected,
            model.competitor_endpoint_local_frames[idx],
            atol=1e-12,
        )
