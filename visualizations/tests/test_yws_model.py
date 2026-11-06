"""Numerical illustrations must satisfy the identities the lecture animates."""
import numpy as np
import pytest
from dkvis.learning.yws.model import mixed_gap_example, rotated_example


@pytest.mark.parametrize('theta', [0., .12, .6, 1.3, np.pi/2])
def test_rotation_residual_and_both_population_gap_bounds(theta):
    a, b, vhat, residual = rotated_example(theta)
    h = b-a
    np.testing.assert_allclose(b @ vhat, 3*vhat, atol=1e-14)
    np.testing.assert_allclose(residual, h @ vhat, atol=1e-14)
    sine = np.sin(theta)
    assert np.linalg.norm(residual) == pytest.approx(2*sine)
    assert np.linalg.norm(h, 2) == pytest.approx(2*sine)
    assert np.linalg.norm(vhat[:, 0]-[1.,0.]) == pytest.approx(2*np.sin(theta/2))
    numerator = min(np.linalg.norm(h, 2), np.linalg.norm(h, 'fro'))
    assert sine <= 2*numerator/2 + 1e-14
    assert 2*np.sin(theta/2) <= 2*np.sqrt(2)*numerator/2 + 1e-14


def test_published_example_has_positive_population_gap_and_zero_mixed_gap():
    population, sample, gap, mixed = mixed_gap_example()
    assert gap == 10 and mixed == 0
    assert sample[-1] > population[3]
    assert np.all(np.diff(population) < 0) and np.all(np.diff(sample) < 0)
