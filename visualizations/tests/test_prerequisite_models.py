"""Numerical identities and counterexamples shown in the prerequisite lectures."""
import numpy as np
import pytest

from dkvis.learning.projections.model import plane_frame, projection_example
from dkvis.learning.singular_norms.model import (
    block_displacement, competing_displacements, ellipse_example, overlapping_restrictions,
)
from dkvis.learning.matrix_exponential.model import (
    opening_flow, euler_path, noncommuting_generators, shear_generator, taylor_exponential,
)


@pytest.mark.parametrize('angle', [0., .3, 1.1])
def test_projection_is_orthogonal_and_the_unique_nearest_point(angle):
    x, p, fitted, error = projection_example(angle)
    assert np.allclose(p.T, p)
    assert np.allclose(p @ p, p)
    assert np.allclose(x, fitted+error)
    assert np.dot(fitted, error) == pytest.approx(0., abs=1e-12)
    u = np.array([np.cos(angle), np.sin(angle)])
    for shift in [-2., -.3, .8, 2.]:
        z = fitted+shift*u
        assert np.linalg.norm(x-z)**2 == pytest.approx(np.linalg.norm(error)**2+shift**2)


def test_rotating_the_frame_changes_coordinates_but_not_the_projector():
    initial = plane_frame()
    for angle in [.2, .85, 1.7]:
        frame = plane_frame(angle)
        assert not np.allclose(frame, initial)
        assert np.allclose(frame.T @ frame, np.eye(2))
        assert np.allclose(frame @ frame.T, np.diag([1., 1., 0.]))


def test_ellipse_axis_lengths_and_directions_are_actual_singular_data():
    t, u, s, v = ellipse_example()
    assert np.allclose(np.linalg.svd(t, compute_uv=False), s)
    assert np.allclose(t @ v, u @ np.diag(s))
    assert np.allclose(u.T @ u, np.eye(2))
    assert np.allclose(v.T @ v, np.eye(2))


def test_operator_and_trace_costs_really_reverse_the_two_competitors():
    reflection, turn = competing_displacements()
    assert np.allclose(reflection, [2, 0])
    assert np.allclose(turn, [1.1, 1.1])
    assert max(turn) < max(reflection)
    assert sum(reflection) < sum(turn)


def test_block_union_and_the_different_norm_additivity_rules():
    first, second, full = block_displacement()
    singular = lambda t: np.linalg.svd(t, compute_uv=False)
    assert np.allclose(np.sort(singular(full)), np.sort(np.r_[singular(first), singular(second)]))
    assert sum(singular(full)) == pytest.approx(4.)
    assert np.linalg.norm(full, 'fro')**2 == pytest.approx(
        np.linalg.norm(first, 'fro')**2+np.linalg.norm(second, 'fro')**2)
    assert np.linalg.norm(full, 2) == pytest.approx(max(np.linalg.norm(first, 2), np.linalg.norm(second, 2)))


def test_overlapping_images_prevent_the_proposed_trace_sum():
    t = overlapping_restrictions()
    assert np.allclose(t[:, 0], t[:, 1])
    full_cost = sum(np.linalg.svd(t, compute_uv=False))
    restricted_sum = np.linalg.norm(t[:, 0])+np.linalg.norm(t[:, 1])
    assert full_cost == pytest.approx(np.sqrt(2))
    assert restricted_sum == pytest.approx(2.)
    assert full_cost < restricted_sum


def test_exponential_matches_diagonal_nilpotent_and_rotation_closed_forms():
    j = np.array([[0., -1.], [1., 0.]])
    n = shear_generator()
    for t in [-1.2, 0., .4, 1.5]:
        assert np.allclose(taylor_exponential(np.diag([.5, -.3]), t), np.diag(np.exp(t*np.array([.5, -.3]))))
        assert np.allclose(taylor_exponential(n, t), np.eye(2)+t*n)
        assert np.allclose(taylor_exponential(j, t), [[np.cos(t), -np.sin(t)], [np.sin(t), np.cos(t)]])
    assert np.allclose(taylor_exponential(np.zeros((2, 2))), np.eye(2))


def test_euler_rotation_paths_approach_the_exact_flow_but_drift_outward():
    j = np.array([[0., -1.], [1., 0.]])
    errors = []
    for steps in [4, 32, 256]:
        path = euler_path(j, np.pi/2, steps, [1, 0])
        assert np.linalg.norm(path[-1]) > 1
        errors.append(np.linalg.norm(path[-1]-[0, 1]))
    assert errors[2] < errors[1] < errors[0]


def test_exponential_derivative_semigroup_and_inverse_for_a_nonnormal_matrix():
    a = np.array([[.2, 1.3], [0., -.4]])
    exp = taylor_exponential
    eps, t = 1e-6, .7
    derivative = (exp(a, t+eps)-exp(a, t-eps))/(2*eps)
    assert np.allclose(derivative, a @ exp(a, t), atol=1e-9)
    assert np.allclose(exp(a, .3) @ exp(a, .7), exp(a, 1.))
    assert np.allclose(exp(a, t) @ exp(a, -t), np.eye(2))


def test_skew_exponential_is_orthogonal_and_preserves_a_commuting_projector():
    b = np.zeros((4, 4))
    b[:2, :2] = [[0, -.7], [.7, 0]]
    b[2:, 2:] = [[0, .4], [-.4, 0]]
    p = np.diag([1., 1., 0., 0.])
    for t in [-1.1, .2, 1.5]:
        v = taylor_exponential(b, t)
        assert np.allclose(v.T @ v, np.eye(4))
        assert np.linalg.det(v) == pytest.approx(1.)
        assert np.allclose(v @ p, p @ v)


def test_different_noncommuting_generators_fail_exponential_factorization():
    a, b = noncommuting_generators()
    assert not np.allclose(a @ b, b @ a)
    product = taylor_exponential(a) @ taylor_exponential(b)
    combined = taylor_exponential(a+b)
    assert np.allclose(product, [[2, 1], [1, 1]])
    assert np.allclose(combined, [[np.cosh(1), np.sinh(1)], [np.sinh(1), np.cosh(1)]])
    assert not np.allclose(product, combined)


@pytest.mark.parametrize('time', [-.5, 0., .8, 1.5, 2.5])
def test_opening_flows_match_their_equations_and_matrix_exponential(time):
    scalar, state = opening_flow(time)
    generator = np.array([[0., -1.], [1., 0.]])
    assert scalar == pytest.approx(np.exp(.4*time))
    assert np.allclose(state, taylor_exponential(generator, time) @ [1., 0.])
    assert np.linalg.norm(state) == pytest.approx(1.)
    delta = 1e-6
    plus, minus = opening_flow(time+delta), opening_flow(time-delta)
    assert (plus[0]-minus[0])/(2*delta) == pytest.approx(.4*scalar, abs=1e-9)
    assert np.allclose((plus[1]-minus[1])/(2*delta), generator @ state, atol=1e-9)


def test_opening_flow_vectorized_values_and_initial_conditions():
    scalar, state = opening_flow(np.array([0., .5, 1.]))
    assert scalar.shape == (3,)
    assert state.shape == (3, 2)
    assert scalar[0] == 1
    assert np.allclose(state[0], [1., 0.])
