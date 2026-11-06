"""Validate the geometry and approximation claims used in the lecture."""
import numpy as np
from dkvis.learning.rayleigh_ritz.model import line_example, trial_example, ritz_pairs


def test_line_residual_is_the_perpendicular_output_component():
    for angle in [0, np.pi/18, np.pi/6, np.pi/2]:
        a, q, theta, r = line_example(angle)
        np.testing.assert_allclose(q @ r, 0, atol=1e-14)
        np.testing.assert_allclose(theta, 1+3*np.sin(angle)**2)
        np.testing.assert_allclose(np.linalg.norm(r), abs(3*np.sin(angle)*np.cos(angle)), atol=1e-14)
    # A residual can vanish at the unwanted exact direction.
    _, _, theta, r = line_example(np.pi/2)
    assert theta == 4 and np.linalg.norm(r) < 1e-14


def test_ritz_pairs_lift_and_have_the_displayed_residuals():
    a, q, b, r = trial_example()
    np.testing.assert_allclose(b, [[2, 1], [1, 2]])
    np.testing.assert_allclose(r, [[0, 0], [0, 0], [1, -1]])
    np.testing.assert_allclose(q.T @ r, 0)
    values, u, residuals = ritz_pairs(a, q)
    np.testing.assert_allclose(values, [1, 3])
    np.testing.assert_allclose(np.linalg.norm(residuals, axis=0), [np.sqrt(2), 0], atol=1e-14)
    np.testing.assert_allclose(residuals, r @ (q.T @ u), atol=1e-14)
    np.testing.assert_allclose(u.T @ u, np.eye(2), atol=1e-14)
    assert np.linalg.norm(r) > 0  # The full trial space is not invariant.


def test_fixed_space_pythagoras_and_coordinate_independence():
    a, q, b, r = trial_example()
    m = np.array([[0., 2.], [-1., 4.]])
    np.testing.assert_allclose(np.linalg.norm(a@q-q@m, 'fro')**2,
                               np.linalg.norm(r, 'fro')**2+np.linalg.norm(b-m, 'fro')**2)
    angle = .37
    z = np.array([[np.cos(angle), -np.sin(angle)], [np.sin(angle), np.cos(angle)]])
    values, u, residuals = ritz_pairs(a, q@z)
    np.testing.assert_allclose(values, [1, 3])
    np.testing.assert_allclose(np.linalg.norm(residuals, axis=0), [np.sqrt(2), 0], atol=1e-14)
    for theta, residual in zip(values, residuals.T):
        assert min(abs(np.linalg.eigvalsh(a)-theta)) <= np.linalg.norm(residual)+1e-14
    # The same statements work for a complex orthonormal change of trial coordinates.
    z = np.diag([1j, 1.])
    values, _, residuals = ritz_pairs(a.astype(complex), q@z)
    np.testing.assert_allclose(values, [1, 3])
    np.testing.assert_allclose(np.linalg.norm(residuals, axis=0), [np.sqrt(2), 0], atol=1e-14)
