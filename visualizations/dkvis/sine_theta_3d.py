"""Checked three-dimensional models of the sine-theta theorem.

The smallest setting in which the *subspace* (not just vector) content of the
theorem is visible is ``R^3`` with a two-dimensional exact invariant subspace:

* ``A`` is symmetric with eigenvectors ``f1, f2, f3``;
* the exact subspace is ``range(F0) = span(f1, f2)``, and ``F1 = f3`` with
  ``Lambda1 = [lambda3]`` is the unwanted part;
* the trial subspace is a plane ``range(E0)`` with orthonormal basis ``E0``
  and a symmetric 2x2 trial matrix ``A0``;
* ``R = A E0 - E0 A0`` and ``sin Theta0`` has the singular values of
  ``F1^T E0``, a 1x2 matrix, so ``||sin Theta0|| = ||F1^T E0||_2`` in every
  normalized unitarily invariant norm.

Two planes in ``R^3`` always share a line, so their principal angles are
``(0, theta)``: one of the two sines is always zero.

Because ``spec(Lambda1) = {lambda3}`` is a single point, the separation hypothesis in
its exchanged form (``spec(Lambda1)`` in an interval, ``spec(A0)`` outside its
``delta``-neighbourhood) holds exactly with

    delta = min_i |mu_i - lambda3|,    mu_i in spec(A0),

wherever ``lambda3`` sits relative to the other eigenvalues.

Two configurations are provided, sharing :class:`Configuration`:

* :func:`tilted_trial` -- ``A`` diagonal and fixed; the trial plane ``range(E0)`` is the exact ``range(F0)``
  tilted by ``theta`` about a hinge line in that exact plane; ``A0 = E0^T A E0``
  (Rayleigh--Ritz), so ``E0^T R = 0``: the residual leaves ``range(E0)`` at right
  angles.
* :func:`perturbed` -- the trial plane is the *old* eigenspace
  ``span(e1, e2)`` with ``A0 = diag(lambda1, lambda2)``, and the operator is
  ``Ahat = A + eps H``; then ``R = eps H E0`` and the exact plane moves instead.
"""

from __future__ import annotations

from dataclasses import dataclass
import math

import numpy as np

DEFAULT_EIGENVALUES = (1.0, 1.6, 2.8)
"""``lambda1, lambda2`` (wanted) and ``lambda3`` (unwanted)."""

PERTURBATION_DIRECTION = np.array(
    [
        [0.10, 0.35, 0.60],
        [0.35, -0.20, 0.45],
        [0.60, 0.45, 0.15],
    ]
)
"""A fixed symmetric perturbation shape, normalized to operator norm 1 below."""


def _unit_operator(H: np.ndarray) -> np.ndarray:
    return H / np.linalg.norm(H, 2)


H_UNIT = _unit_operator(PERTURBATION_DIRECTION)


@dataclass(frozen=True)
class Configuration:
    """Everything the 3D scene draws, computed from ``(A, E0, A0)``.

    ``unwanted`` is the index (into ``eigh(A)``) of the eigenvector that plays
    the role of ``F1``; the other two span the exact wanted plane ``range(F0)``.
    """

    A: np.ndarray
    E0: np.ndarray
    A0: np.ndarray
    unwanted: int

    # -- exact spectral data ---------------------------------------------------
    @property
    def _eig(self) -> tuple[np.ndarray, np.ndarray]:
        return np.linalg.eigh(self.A)

    @property
    def eigenvalues(self) -> np.ndarray:
        return self._eig[0]

    @property
    def eigenvectors(self) -> np.ndarray:
        return self._eig[1]

    @property
    def F1(self) -> np.ndarray:
        return self.eigenvectors[:, self.unwanted]

    @property
    def F0(self) -> np.ndarray:
        keep = [i for i in range(3) if i != self.unwanted]
        return self.eigenvectors[:, keep]

    @property
    def lambda_unwanted(self) -> float:
        return float(self.eigenvalues[self.unwanted])

    @property
    def lambda_wanted(self) -> np.ndarray:
        keep = [i for i in range(3) if i != self.unwanted]
        return self.eigenvalues[keep]

    @property
    def normal_U(self) -> np.ndarray:
        """Unit normal of the exact wanted plane ``range(F0)`` (namely ``F1``)."""
        return self.F1

    # -- trial data ------------------------------------------------------------
    @property
    def normal_V(self) -> np.ndarray:
        n = np.cross(self.E0[:, 0], self.E0[:, 1])
        return n / np.linalg.norm(n)

    @property
    def ritz_values(self) -> np.ndarray:
        """``spec(A0)``."""
        return np.linalg.eigvalsh(self.A0)

    @property
    def R(self) -> np.ndarray:
        return self.A @ self.E0 - self.E0 @ self.A0

    @property
    def residual_norm_2(self) -> float:
        return float(np.linalg.norm(self.R, 2))

    @property
    def residual_norm_F(self) -> float:
        return float(np.linalg.norm(self.R, "fro"))

    # -- angles ----------------------------------------------------------------
    @property
    def sine_block(self) -> np.ndarray:
        """``F1^T E0`` (1x2): its singular value is the nonzero ``sin theta``."""
        return self.F1 @ self.E0

    @property
    def sin_theta(self) -> float:
        """``||sin Theta0||``; equal in every normalized unitarily invariant norm."""
        return float(np.linalg.norm(self.sine_block))

    @property
    def principal_angles(self) -> np.ndarray:
        """Principal angles between ``range(F0)`` and ``range(E0)``, largest first."""
        cos = np.linalg.svd(self.F0.T @ self.E0, compute_uv=False)
        return np.sort(np.arccos(np.clip(cos, -1.0, 1.0)))[::-1]

    @property
    def principal_vectors(self) -> tuple[np.ndarray, np.ndarray]:
        """Orthonormal ``(hinge, tilted)`` basis of ``range(E0)``.

        ``hinge`` spans the intersection of the exact and trial planes (the zero principal angle) and ``tilted`` is
        the direction of ``range(E0)`` that makes the angle ``theta`` with ``range(F0)``.
        """
        _, _, vt = np.linalg.svd(self.F0.T @ self.E0)
        coords = vt.T  # columns: right singular vectors, largest cosine first
        hinge = self.E0 @ coords[:, 0]
        tilted = self.E0 @ coords[:, 1]
        # Orient ``tilted`` away from range(F0) along +F1 so pictures are stable.
        if tilted @ self.F1 < 0:
            tilted = -tilted
        return hinge, tilted

    # -- gap and theorem -------------------------------------------------------
    @property
    def delta(self) -> float:
        """``min_i |mu_i - lambda3|`` (exchanged form of the separation hypothesis)."""
        return float(np.min(np.abs(self.ritz_values - self.lambda_unwanted)))

    @property
    def nearest_ritz(self) -> float:
        mu = self.ritz_values
        return float(mu[np.argmin(np.abs(mu - self.lambda_unwanted))])

    @property
    def theorem_lhs(self) -> float:
        return self.delta * self.sin_theta

    def verify(self, *, atol: float = 1e-10) -> None:
        E0, A0 = self.E0, self.A0
        np.testing.assert_allclose(E0.T @ E0, np.eye(2), atol=atol)
        np.testing.assert_allclose(A0, A0.T, atol=atol)
        np.testing.assert_allclose(self.A, self.A.T, atol=atol)
        # F1 spans U-perp and is an eigenvector.
        np.testing.assert_allclose(self.A @ self.F1, self.lambda_unwanted * self.F1, atol=atol)
        # sin Theta0 agrees with the largest principal angle, and with
        # ||(I - F0 F0^T) E0||_2.
        assert math.isclose(self.sin_theta, math.sin(self.principal_angles[0]), abs_tol=1e-7)
        P0 = self.F0 @ self.F0.T
        assert math.isclose(
            self.sin_theta, float(np.linalg.norm((np.eye(3) - P0) @ E0, 2)), abs_tol=atol
        )
        # Two planes in R^3 share a line: the smaller principal angle is 0.
        assert self.principal_angles[1] <= 1e-6
        # The theorem, in the operator and Frobenius norms.
        assert self.theorem_lhs <= self.residual_norm_2 + atol
        assert self.residual_norm_2 <= self.residual_norm_F + atol


def hinge_axis(phi: float) -> np.ndarray:
    return np.array([math.cos(phi), math.sin(phi), 0.0])


def tilted_trial(
    theta: float,
    phi: float = 0.0,
    eigenvalues: tuple[float, float, float] = DEFAULT_EIGENVALUES,
) -> Configuration:
    """``A = diag(eigenvalues)`` with exact ``range(F0)=span(e1,e2)`` and trial ``range(E0)`` tilted by ``theta``.

    The hinge line shared by the exact and trial planes points along ``(cos phi, sin phi, 0)``.  ``A0`` is
    the Rayleigh--Ritz matrix ``E0^T A E0``.
    """
    if not 0.0 <= theta <= math.pi / 2 + 1e-12:
        raise ValueError("theta must lie in [0, pi/2]")
    A = np.diag(np.asarray(eigenvalues, dtype=float))
    a = hinge_axis(phi)
    b = np.array([-math.sin(phi), math.cos(phi), 0.0])
    e3 = np.array([0.0, 0.0, 1.0])
    E0 = np.column_stack([a, math.cos(theta) * b + math.sin(theta) * e3])
    A0 = E0.T @ A @ E0
    # eigh sorts eigenvalues; locate e3 among the eigenvectors.
    _, vecs = np.linalg.eigh(A)
    unwanted = int(np.argmax(np.abs(vecs[2, :])))
    return Configuration(A=A, E0=E0, A0=A0, unwanted=unwanted)


def perturbed(
    eps: float,
    eigenvalues: tuple[float, float, float] = DEFAULT_EIGENVALUES,
    H: np.ndarray = H_UNIT,
) -> Configuration:
    """``A + eps H`` against the old eigenspace ``E0 = [e1 e2]``, ``A0 = diag(l1, l2)``.

    Then ``R = eps H E0``, so ``||R|| <= eps ||H|| = eps``.  The unwanted
    eigenvector of ``A + eps H`` is tracked as the one closest to ``e3``.
    """
    lam = np.asarray(eigenvalues, dtype=float)
    A = np.diag(lam) + eps * H
    E0 = np.eye(3)[:, :2]
    A0 = np.diag(lam[:2])
    _, vecs = np.linalg.eigh(A)
    unwanted = int(np.argmax(np.abs(vecs[2, :])))
    return Configuration(A=A, E0=E0, A0=A0, unwanted=unwanted)
