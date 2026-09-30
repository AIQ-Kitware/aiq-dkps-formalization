"""Exact numerical model for the Davis--Kahan Proposition 4.4 counterexample.

The Lean development proves that the printed Proposition 4.4 is false using an
explicit configuration in R^4.  This module encodes the same matrices and the
same invariants so the VTK and Manim visualizations share one checked source of
numerical truth.

The source subspace is U = span(e0, e1).  The competitor is

    W = 1/2 * [[ 1, -1, -1, -1],
               [ 1,  1,  1, -1],
               [-1, -1,  1, -1],
               [ 1, -1,  1,  1]],

and V = W(U).  The direct rotation is

    R = 1/sqrt(2) * [[ 1,  0,  0, -1],
                     [ 0,  1,  1,  0],
                     [ 0, -1,  1,  0],
                     [ 1,  0,  0,  1]].

Both principal angles are pi/4.  Yet the full-displacement trace norm satisfies

    ||I - W||_* = 2 sqrt(2)
        < 4 sqrt(2 - sqrt(2)) = ||I - R||_*.

Thus W is an admissible orthogonal map carrying U onto V that beats the direct
rotation in a unitarily invariant norm, refuting the printed claim.
"""

from __future__ import annotations

from dataclasses import dataclass
import argparse
import math

import numpy as np


SQRT2 = math.sqrt(2.0)


def _rotation_block(angle: float) -> np.ndarray:
    """Counterclockwise 2D rotation matrix."""
    c = math.cos(angle)
    s = math.sin(angle)
    return np.array([[c, -s], [s, c]], dtype=float)


def _givens4(i: int, j: int, angle: float) -> np.ndarray:
    """A 4D Givens rotation in coordinate plane ``(i, j)``."""
    out = np.eye(4)
    c = math.cos(angle)
    s = math.sin(angle)
    out[i, i] = c
    out[j, j] = c
    out[i, j] = -s
    out[j, i] = s
    return out


@dataclass(frozen=True)
class Prop44Model:
    """Exact finite-dimensional witness used by the Lean refutation."""

    @property
    def identity(self) -> np.ndarray:
        return np.eye(4)

    @property
    def u_basis(self) -> np.ndarray:
        """Orthonormal columns spanning U = span(e0, e1)."""
        return np.eye(4)[:, :2]

    @property
    def W(self) -> np.ndarray:
        return 0.5 * np.array(
            [
                [1, -1, -1, -1],
                [1, 1, 1, -1],
                [-1, -1, 1, -1],
                [1, -1, 1, 1],
            ],
            dtype=float,
        )

    @property
    def R(self) -> np.ndarray:
        return (1.0 / SQRT2) * np.array(
            [
                [1, 0, 0, -1],
                [0, 1, 1, 0],
                [0, -1, 1, 0],
                [1, 0, 0, 1],
            ],
            dtype=float,
        )

    @property
    def v_basis(self) -> np.ndarray:
        return self.W @ self.u_basis

    @property
    def P_U(self) -> np.ndarray:
        return self.u_basis @ self.u_basis.T

    @property
    def P_V(self) -> np.ndarray:
        return self.v_basis @ self.v_basis.T

    @property
    def canonical_intertwiner(self) -> np.ndarray:
        I = self.identity
        return self.P_V @ self.P_U + (I - self.P_V) @ (I - self.P_U)

    @property
    def m_basis(self) -> np.ndarray:
        """Columns (m0,m1,m2,m3), the invariant basis for the competitor."""
        e = np.eye(4)
        return np.column_stack(
            [
                (e[:, 0] + e[:, 2]) / SQRT2,
                (e[:, 1] + e[:, 3]) / SQRT2,
                (e[:, 0] - e[:, 2]) / SQRT2,
                (e[:, 1] - e[:, 3]) / SQRT2,
            ]
        )

    @property
    def principal_cosines(self) -> np.ndarray:
        return np.linalg.svd(self.u_basis.T @ self.v_basis, compute_uv=False)

    @property
    def principal_angles(self) -> np.ndarray:
        return np.arccos(np.clip(self.principal_cosines, -1.0, 1.0))

    @property
    def principal_angles_degrees(self) -> np.ndarray:
        return np.degrees(self.principal_angles)

    def displacement_singular_values(self, operator: np.ndarray) -> np.ndarray:
        return np.linalg.svd(self.identity - operator, compute_uv=False)

    def trace_displacement(self, operator: np.ndarray) -> float:
        return float(self.displacement_singular_values(operator).sum())

    @property
    def direct_singular_values(self) -> np.ndarray:
        return self.displacement_singular_values(self.R)

    @property
    def competitor_singular_values(self) -> np.ndarray:
        return self.displacement_singular_values(self.W)

    @property
    def direct_trace_displacement(self) -> float:
        return self.trace_displacement(self.R)

    @property
    def competitor_trace_displacement(self) -> float:
        return self.trace_displacement(self.W)

    def direct_rotation_at(self, t: float) -> np.ndarray:
        """Geodesic animation path from I to R.

        This path rotates span(e0,e3) by +t*pi/4 and span(e1,e2) by
        -t*pi/4.  It is used only to animate the endpoint R.
        """
        t = float(np.clip(t, 0.0, 1.0))
        a = t * math.pi / 4.0
        c = math.cos(a)
        s = math.sin(a)
        return np.array(
            [
                [c, 0, 0, -s],
                [0, c, s, 0],
                [0, -s, c, 0],
                [s, 0, 0, c],
            ],
            dtype=float,
        )

    def competitor_at(self, t: float) -> np.ndarray:
        """Animation path from I to W in the competitor invariant basis.

        In the m-basis this is rot(t*pi/2) direct-sum I_2.  Intermediate
        values are for explaining the endpoint motion; only t=1 is the
        admissible competitor used in Proposition 4.4.
        """
        t = float(np.clip(t, 0.0, 1.0))
        local = np.eye(4)
        local[:2, :2] = _rotation_block(t * math.pi / 2.0)
        M = self.m_basis
        return M @ local @ M.T

    def direct_trace_at(self, t: float) -> float:
        return self.trace_displacement(self.direct_rotation_at(t))

    def competitor_trace_at(self, t: float) -> float:
        return self.trace_displacement(self.competitor_at(t))

    @property
    def base_view_basis(self) -> np.ndarray:
        """Orthogonal 4D change of coordinates used before dropping one axis.

        The first three rows span the familiar 3D hyperplane orthogonal to
        (1,1,1,1); the last row is the hidden coordinate.  This avoids simply
        erasing one of the original coordinate axes.
        """
        return np.array(
            [
                [1, -1, 0, 0],
                [1, 1, -2, 0],
                [1, 1, 1, -3],
                [1, 1, 1, 1],
            ],
            dtype=float,
        ) / np.array([[SQRT2], [math.sqrt(6.0)], [math.sqrt(12.0)], [2.0]])

    def projection_4d_to_3d(self, view_angle: float = 0.0) -> np.ndarray:
        """Return a 3x4 orthogonal projection matrix for viewing R^4 in R^3.

        ``view_angle`` rotates the third visible coordinate into the hidden
        fourth coordinate before the latter is dropped.  No 4D->3D projection
        preserves all distances or angles; the VTK scene therefore displays
        true 4D displacement values separately from the projected geometry.
        """
        view_rotation = _givens4(2, 3, view_angle)
        view_coordinates = view_rotation @ self.base_view_basis
        return view_coordinates[:3, :]

    def project(self, points: np.ndarray, view_angle: float = 0.0) -> np.ndarray:
        """Project one 4-vector or a collection of row 4-vectors into R^3."""
        P = self.projection_4d_to_3d(view_angle)
        points = np.asarray(points, dtype=float)
        if points.ndim == 1:
            return P @ points
        return points @ P.T

    def circle_in_u(self, count: int = 96) -> np.ndarray:
        angles = np.linspace(0.0, 2.0 * math.pi, count, endpoint=True)
        return np.outer(np.cos(angles), self.u_basis[:, 0]) + np.outer(
            np.sin(angles), self.u_basis[:, 1]
        )

    def verify(self, atol: float = 1e-10) -> None:
        I = self.identity
        M = self.m_basis
        assert np.allclose(self.W.T @ self.W, I, atol=atol)
        assert np.allclose(self.R.T @ self.R, I, atol=atol)
        assert np.allclose(M.T @ M, I, atol=atol)
        assert np.allclose(self.canonical_intertwiner.T @ self.canonical_intertwiner, 0.5 * I, atol=atol)
        assert np.allclose(self.R, SQRT2 * self.canonical_intertwiner, atol=atol)
        assert np.allclose(self.R @ self.P_U @ self.R.T, self.P_V, atol=atol)
        assert np.allclose(self.W @ self.P_U @ self.W.T, self.P_V, atol=atol)
        assert np.allclose(self.principal_angles, np.full(2, math.pi / 4.0), atol=atol)

        expected_w_local = np.eye(4)
        expected_w_local[:2, :2] = _rotation_block(math.pi / 2.0)
        assert np.allclose(M.T @ self.W @ M, expected_w_local, atol=atol)

        chord = math.sqrt(2.0 - SQRT2)
        assert np.allclose(self.direct_singular_values, np.full(4, chord), atol=atol)
        assert np.allclose(self.competitor_singular_values, np.array([SQRT2, SQRT2, 0.0, 0.0]), atol=atol)
        assert math.isclose(self.direct_trace_displacement, 4.0 * chord, abs_tol=atol)
        assert math.isclose(self.competitor_trace_displacement, 2.0 * SQRT2, abs_tol=atol)
        assert self.competitor_trace_displacement < self.direct_trace_displacement

        assert np.allclose(self.direct_rotation_at(0.0), I, atol=atol)
        assert np.allclose(self.direct_rotation_at(1.0), self.R, atol=atol)
        assert np.allclose(self.competitor_at(0.0), I, atol=atol)
        assert np.allclose(self.competitor_at(1.0), self.W, atol=atol)

        for angle in [0.0, 0.2, 1.0, 2.3]:
            P = self.projection_4d_to_3d(angle)
            assert np.allclose(P @ P.T, np.eye(3), atol=atol)

    def summary(self) -> str:
        direct_sv = ", ".join(f"{x:.6f}" for x in self.direct_singular_values)
        comp_sv = ", ".join(f"{x:.6f}" for x in self.competitor_singular_values)
        return "\n".join(
            [
                "Davis--Kahan Proposition 4.4 counterexample (R^4)",
                f"principal angles = {self.principal_angles_degrees[0]:.6f} deg, "
                f"{self.principal_angles_degrees[1]:.6f} deg",
                f"pi/3 threshold   = {60.0:.6f} deg",
                f"sigma(I-R)       = [{direct_sv}]",
                f"sigma(I-W)       = [{comp_sv}]",
                f"||I-R||_*        = {self.direct_trace_displacement:.9f}",
                f"||I-W||_*        = {self.competitor_trace_displacement:.9f}",
                f"strict gap       = {self.direct_trace_displacement - self.competitor_trace_displacement:.9f}",
                "REFUTATION        = ||I-W||_* < ||I-R||_*",
            ]
        )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="run all numerical identity checks")
    return parser


def main() -> None:
    args = _parser().parse_args()
    model = Prop44Model()
    if args.verify:
        model.verify()
    print(model.summary())


if __name__ == "__main__":
    main()
