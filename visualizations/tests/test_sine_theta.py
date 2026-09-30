import math

import numpy as np
import pytest

from dkvis.sine_theta import SineThetaModel


@pytest.mark.parametrize("theta_degrees", [0.0, 5.0, 30.0, 45.0, 75.0, 90.0])
def test_sharp_model_is_equality(theta_degrees):
    model = SineThetaModel.from_degrees(theta_degrees, delta=2.5)
    model.verify()
    assert model.is_sharp
    assert model.residual_norm == pytest.approx(model.theorem_lhs)


def test_rectangular_block_is_perpendicular_component():
    model = SineThetaModel.from_degrees(37.0)
    expected = np.array([0.0, math.sin(math.radians(37.0))])
    np.testing.assert_allclose(model.sine_block_vector, expected)
    assert model.sin_theta == pytest.approx(np.linalg.norm(expected))


@pytest.mark.parametrize("lambda_desired", [-3.0, -0.5, 0.25, 4.0])
def test_nonsharp_model_satisfies_inequality(lambda_desired):
    model = SineThetaModel.from_degrees(
        41.0,
        delta=1.7,
        rho=0.25,
        lambda_desired=lambda_desired,
    )
    model.verify()
    assert model.theorem_lhs <= model.residual_norm + 1e-12


def test_residual_formula():
    model = SineThetaModel.from_degrees(
        32.0,
        delta=1.75,
        rho=-0.4,
        lambda_desired=0.6,
    )
    theta = math.radians(32.0)
    expected = np.array(
        [
            (0.6 - (-0.4)) * math.cos(theta),
            1.75 * math.sin(theta),
        ]
    )
    np.testing.assert_allclose(model.residual, expected)
