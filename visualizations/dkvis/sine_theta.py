"""Finite-dimensional model of the Davis--Kahan sine-theta theorem.

The Lean theorem is considerably more general: it permits unbounded
self-adjoint operators and where-defined unitarily invariant norms.  This file
chooses the smallest real model in which every geometric object in the public
sine-theta statement is visible.

Let

    U = span(e1),
    v_theta = (cos(theta), sin(theta)),
    V = span(v_theta),
    A = diag(lambda_desired, rho + delta),
    A0 = [rho].

The exact complementary spectral coordinate is e2, while ``v_theta`` is the
trial coordinate.  On the unit trial coordinate,

    S = (I - P_U) v_theta = (0, sin(theta)),

so the positive trial-coordinate sine operator is the scalar ``sin(theta)``.
The residual is

    r = A v_theta - rho v_theta
      = ((lambda_desired - rho) cos(theta), delta sin(theta)).

Therefore

    delta * sin(theta) <= ||r||_2.

When ``lambda_desired == rho`` (the default), equality holds.  That sharp case
is the default in both the VTK and Manim scenes.
"""

from __future__ import annotations

from dataclasses import dataclass
import argparse
import math

import numpy as np


@dataclass(frozen=True)
class SineThetaModel:
    """A rank-one real specialization of the sine-theta theorem.

    Parameters
    ----------
    theta:
        Principal angle in radians.  The visualization restricts this to the
        principal-angle range ``[0, pi / 2]``.
    delta:
        Spectral separation between the trial scalar ``rho`` and the exact
        complementary eigenvalue.
    rho:
        Scalar trial operator ``A0``.
    lambda_desired:
        Eigenvalue of ``A`` on the desired exact eigenspace.  Setting this
        equal to ``rho`` gives the sharp equality model.
    """

    theta: float
    delta: float = 1.0
    rho: float = 0.0
    lambda_desired: float = 0.0

    def __post_init__(self) -> None:
        if not 0.0 <= self.theta <= math.pi / 2 + 1e-12:
            raise ValueError("theta must lie in [0, pi/2]")
        if not self.delta > 0.0:
            raise ValueError("delta must be positive")

    @classmethod
    def from_degrees(
        cls,
        theta_degrees: float,
        *,
        delta: float = 1.0,
        rho: float = 0.0,
        lambda_desired: float = 0.0,
    ) -> "SineThetaModel":
        return cls(
            math.radians(theta_degrees),
            delta=delta,
            rho=rho,
            lambda_desired=lambda_desired,
        )

    @property
    def theta_degrees(self) -> float:
        return math.degrees(self.theta)

    @property
    def complement_eigenvalue(self) -> float:
        return self.rho + self.delta

    @property
    def operator(self) -> np.ndarray:
        return np.diag([self.lambda_desired, self.complement_eigenvalue])

    @property
    def trial_vector(self) -> np.ndarray:
        return np.array([math.cos(self.theta), math.sin(self.theta)], dtype=float)

    @property
    def desired_projection(self) -> np.ndarray:
        """``P_U v_theta`` for ``U = span(e1)``."""
        return np.array([math.cos(self.theta), 0.0], dtype=float)

    @property
    def sine_block_vector(self) -> np.ndarray:
        """``(I - P_U) v_theta``: the rectangular proof representative."""
        return self.trial_vector - self.desired_projection

    @property
    def sin_theta(self) -> float:
        """The literal positive ``sin Theta_0`` in this 1D trial coordinate."""
        return float(np.linalg.norm(self.sine_block_vector))

    @property
    def residual(self) -> np.ndarray:
        """``A v_theta - rho v_theta`` on the unit trial coordinate."""
        v = self.trial_vector
        return self.operator @ v - self.rho * v

    @property
    def residual_norm(self) -> float:
        return float(np.linalg.norm(self.residual))

    @property
    def theorem_lhs(self) -> float:
        return self.delta * self.sin_theta

    @property
    def slack(self) -> float:
        return self.residual_norm - self.theorem_lhs

    @property
    def is_sharp(self) -> bool:
        return math.isclose(self.slack, 0.0, rel_tol=1e-12, abs_tol=1e-12)

    def verify(self, *, atol: float = 1e-12) -> None:
        """Check the elementary identities used by the rendered scene."""
        v = self.trial_vector
        p = self.desired_projection
        s = self.sine_block_vector
        r = self.residual

        np.testing.assert_allclose(v, p + s, atol=atol)
        np.testing.assert_allclose(s, [0.0, math.sin(self.theta)], atol=atol)
        np.testing.assert_allclose(
            r,
            [
                (self.lambda_desired - self.rho) * math.cos(self.theta),
                self.delta * math.sin(self.theta),
            ],
            atol=atol,
        )
        if self.theorem_lhs > self.residual_norm + atol:
            raise AssertionError(
                f"sine-theta inequality failed: {self.theorem_lhs} > {self.residual_norm}"
            )

    def summary(self) -> str:
        relation = "=" if self.is_sharp else "<="
        return "\n".join(
            [
                f"theta              = {self.theta_degrees:.3f} deg",
                f"sin(theta)         = {self.sin_theta:.6f}",
                f"delta              = {self.delta:.6f}",
                f"trial vector       = {np.array2string(self.trial_vector, precision=6)}",
                f"sine block vector  = {np.array2string(self.sine_block_vector, precision=6)}",
                f"residual           = {np.array2string(self.residual, precision=6)}",
                f"||residual||_2     = {self.residual_norm:.6f}",
                f"delta sin(theta)   = {self.theorem_lhs:.6f}",
                f"theorem            : {self.theorem_lhs:.6f} {relation} {self.residual_norm:.6f}",
            ]
        )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--theta", type=float, default=35.0, help="angle in degrees")
    parser.add_argument("--delta", type=float, default=1.0, help="positive spectral gap")
    parser.add_argument("--rho", type=float, default=0.0, help="trial scalar A0")
    parser.add_argument(
        "--lambda-desired",
        type=float,
        default=0.0,
        help="eigenvalue of A on the desired eigenspace",
    )
    return parser


def main() -> None:
    args = _parser().parse_args()
    model = SineThetaModel.from_degrees(
        args.theta,
        delta=args.delta,
        rho=args.rho,
        lambda_desired=args.lambda_desired,
    )
    model.verify()
    print(model.summary())


if __name__ == "__main__":
    main()
