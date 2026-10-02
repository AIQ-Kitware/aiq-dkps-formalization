"""Checked numerical models for the sine-theta intuition deck.

Every quantity drawn by :mod:`dkvis.slides_sine_theta` is computed here, and each
model has a ``verify`` method that checks the closed forms the slides quote
against a direct numerical computation.  The sharp rank-one model used by the
existing VTK scenes lives in :mod:`dkvis.sine_theta` and is reused unchanged.

Notation follows Davis--Kahan (1970), Sections 1--2, with the operator whose
exact spectral decomposition is known written ``A`` (the paper's ``A + H``):

* ``E0``: orthonormal trial vectors, ``A0``: the trial (Ritz) operator;
* ``F0, F1``: exact spectral isometries of ``A``, with ``A F1 = F1 Lambda1``;
* ``R = A E0 - E0 A0``: the residual;
* ``sin Theta0``: the operator whose singular values are those of ``F1^* E0``.

The theorem is ``delta * ||sin Theta0|| <= ||R||`` whenever ``spec(A0)`` lies in
an interval ``[beta, alpha]`` and ``spec(Lambda1)`` avoids
``(beta - delta, alpha + delta)``, or the same with the roles exchanged.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import math

import numpy as np


def rotation(angle: float) -> np.ndarray:
    """Counter-clockwise rotation of the plane by ``angle`` radians."""
    c, s = math.cos(angle), math.sin(angle)
    return np.array([[c, -s], [s, c]])


def unit(angle: float) -> np.ndarray:
    return np.array([math.cos(angle), math.sin(angle)])


def line_angle(u: np.ndarray, v: np.ndarray) -> float:
    """Angle in ``[0, pi/2]`` between the lines spanned by ``u`` and ``v``."""
    cos = abs(float(u @ v)) / (np.linalg.norm(u) * np.linalg.norm(v))
    return math.acos(min(1.0, cos))


@dataclass(frozen=True)
class PerturbedPair:
    """The canonical 2x2 picture of eigenvector rotation.

    ``A = diag(c + g/2, c - g/2)`` has eigenvalue gap ``g`` and eigenvectors
    ``e1, e2``.  The symmetric, trace-free perturbation

        H = eps * [[cos phi, sin phi], [sin phi, -cos phi]]

    has operator norm ``eps`` for every ``phi`` (its eigenvalues are ``+-eps``),
    and its own top eigenvector points along the line at angle ``phi / 2``.  The
    default ``phi = pi/2`` is ``eps * [[0, 1], [1, 0]]``, whose eigenvectors lie
    on the diagonals.

    With ``a = g/2 + eps cos phi``, ``b = eps sin phi`` and ``s = hypot(a, b)``,
    the perturbed matrix ``A + H`` has eigenvalues ``c +- s`` and its top
    eigenvector spans the line at the signed angle

        theta = 1/2 * atan2(b, a)      in (-pi/2, pi/2]

    from ``e1``.  For ``phi = pi/2`` this is ``1/2 atan2(2 eps, g)``, which tends
    to 45 degrees as ``g -> 0`` however small ``eps`` is, while the eigenvalues
    move by at most ``eps`` (Weyl).  Turning ``phi`` once round shows the
    instability outright: when ``g/2 > eps`` the line only wobbles, by at most
    ``1/2 asin(2 eps / g)``, but when ``g/2 < eps`` it turns through every
    direction, following the line of ``H``.

    For the sine-theta theorem take the trial vector ``E0 = e1`` with
    ``A0 = [c + g/2]`` (the unperturbed eigenpair).  Then ``R = H e1 = (0, eps)``
    and the relevant gap is between ``A0`` and the *perturbed* unwanted
    eigenvalue ``c - s``:

        delta = g/2 + s,     sin(theta) <= eps / delta.
    """

    gap: float
    eps: float
    center: float = 1.5
    phi: float = math.pi / 2

    def __post_init__(self) -> None:
        if self.gap < 0.0:
            raise ValueError("gap must be nonnegative")
        if self.eps < 0.0:
            raise ValueError("eps must be nonnegative")

    @property
    def A(self) -> np.ndarray:
        return np.diag([self.center + self.gap / 2, self.center - self.gap / 2])

    @property
    def H(self) -> np.ndarray:
        c, s = math.cos(self.phi), math.sin(self.phi)
        return self.eps * np.array([[c, s], [s, -c]])

    @property
    def perturbation_direction(self) -> np.ndarray:
        """Unit vector along the top eigenvector of ``H`` (angle ``phi / 2``)."""
        return unit(self.phi / 2)

    @property
    def perturbed(self) -> np.ndarray:
        return self.A + self.H

    @property
    def _split(self) -> tuple[float, float]:
        return self.gap / 2 + self.eps * math.cos(self.phi), self.eps * math.sin(self.phi)

    @property
    def half_split(self) -> float:
        return math.hypot(*self._split)

    @property
    def perturbed_eigenvalues(self) -> tuple[float, float]:
        return (self.center + self.half_split, self.center - self.half_split)

    @property
    def eigenvalue_shift(self) -> float:
        """Largest eigenvalue movement; Weyl bounds it by ``||H||_2 = eps``."""
        return abs(self.half_split - self.gap / 2)

    @property
    def theta(self) -> float:
        """Signed angle in ``(-pi/2, pi/2]`` from ``e1`` to the top eigenvector line of ``A + H``."""
        a, b = self._split
        return 0.5 * math.atan2(b, a)

    @property
    def line_angle(self) -> float:
        """Angle in ``[0, pi/2]`` between the top eigenvector lines of ``A`` and ``A + H``."""
        return abs(self.theta)

    @property
    def perturbed_top_eigenvector(self) -> np.ndarray:
        return unit(self.theta)

    @property
    def sin_theta(self) -> float:
        return math.sin(self.line_angle)

    @property
    def residual(self) -> np.ndarray:
        """``(A + H) e1 - e1 (c + g/2) = H e1``."""
        return self.H @ np.array([1.0, 0.0])

    @property
    def residual_norm(self) -> float:
        return float(np.linalg.norm(self.residual))

    @property
    def delta(self) -> float:
        """Distance from ``spec(A0) = {c + g/2}`` to the unwanted ``c - s``."""
        return self.gap / 2 + self.half_split

    @property
    def bound(self) -> float:
        """The sine-theta bound ``||R|| / delta`` on ``sin(theta)``."""
        return self.residual_norm / self.delta if self.delta > 0 else math.inf

    # -- the other three Section 2 theorems on the same example ------------------
    # Each measures its gap between a different pair of eigenvalues.  With the
    # default off-diagonal ``H`` (``phi = pi/2``) the tan theta, sin 2theta and
    # tan 2theta bounds hold with equality; the sin theta bound is strict.

    @property
    def off_diagonal(self) -> bool:
        """``H_0 = H_1 = 0``: ``H`` only couples ``e1`` with ``e2``."""
        return abs(math.cos(self.phi)) < 1e-12

    @property
    def tan_theta(self) -> float:
        return math.tan(self.line_angle)

    @property
    def sin_two_theta(self) -> float:
        return abs(math.sin(2 * self.line_angle))

    @property
    def tan_two_theta(self) -> float:
        return abs(math.tan(2 * self.line_angle))

    @property
    def delta_tan(self) -> float:
        """tan theta: Ritz value ``c + g/2`` (Rayleigh--Ritz when ``H_0 = 0``) to the
        unwanted eigenvalue ``c - s`` of ``A + H``, all on one side."""
        return self.delta

    @property
    def delta_sin_two(self) -> float:
        """sin 2theta: between the two eigenvalues of ``A + H`` itself, ``2 s``."""
        return 2 * self.half_split

    @property
    def delta_tan_two(self) -> float:
        """tan 2theta: between the two eigenvalues of ``A`` itself, ``g``."""
        return self.gap

    @property
    def reflected(self) -> np.ndarray:
        """``A + XHX`` with ``X = diag(1, -1)``: the coupling flips sign, the eigenvalues do not move.

        Its top eigenvector is the mirror image of that of ``A + H``, at ``-theta``, so
        the two are ``2 theta`` apart (the reflection step of the sin 2theta proof).
        """
        X = np.diag([1.0, -1.0])
        return self.A + X @ self.H @ X

    def coupling(self, turn: float) -> float:
        """Off-diagonal entry of ``A + H`` in the basis turned by ``turn``.

        ``(a1 - a0) sin(turn) cos(turn) + b cos(2 turn)``; it vanishes at the Jacobi angle,
        the eigenvector angle ``theta`` (for the off-diagonal ``H``).
        """
        a0, a1 = self.A.diagonal()
        b = float(self.H[0, 1])
        return 0.5 * (a1 - a0) * math.sin(2 * turn) + b * math.cos(2 * turn)

    def family(self) -> dict[str, tuple[float, float, float]]:
        """``name -> (delta, delta * f(theta), bound)`` for the four theorems."""
        eps = self.residual_norm
        return {
            "sin": (self.delta, self.delta * self.sin_theta, eps),
            "tan": (self.delta_tan, self.delta_tan * self.tan_theta, eps),
            "sin2": (self.delta_sin_two, self.delta_sin_two * self.sin_two_theta, 2 * eps),
            "tan2": (self.delta_tan_two, self.delta_tan_two * self.tan_two_theta, 2 * eps),
        }

    def verify(self, *, atol: float = 1e-12) -> None:
        evals, evecs = np.linalg.eigh(self.perturbed)
        np.testing.assert_allclose(
            sorted(evals, reverse=True), self.perturbed_eigenvalues, atol=atol
        )
        if self.half_split > 1e-9:
            top = evecs[:, int(np.argmax(evals))]
            assert math.isclose(
                line_angle(top, np.array([1.0, 0.0])), self.line_angle, abs_tol=1e-9
            )
            assert math.isclose(line_angle(top, unit(self.theta)), 0.0, abs_tol=1e-6)
        weyl = np.max(np.abs(np.sort(evals) - np.sort(np.diag(self.A))))
        assert weyl <= np.linalg.norm(self.H, 2) + atol
        assert math.isclose(weyl, self.eigenvalue_shift, abs_tol=1e-9)
        assert self.sin_theta <= self.bound + atol
        lhs_sin2 = self.delta_sin_two * self.sin_two_theta
        assert lhs_sin2 <= 2 * self.residual_norm + 1e-9
        if self.off_diagonal and self.gap > 0:
            assert math.isclose(self.delta_tan * self.tan_theta, self.residual_norm, rel_tol=1e-9)
            assert math.isclose(lhs_sin2, 2 * self.residual_norm, rel_tol=1e-9)
            assert math.isclose(self.delta_tan_two * self.tan_two_theta, 2 * self.residual_norm, rel_tol=1e-9)
            assert self.line_angle <= math.pi / 4 + 1e-12


@dataclass(frozen=True)
class RayleighResidual:
    """Residual of a trial vector for ``A = diag(lam1, lam2)``.

    For ``v = (cos phi, sin phi)`` and the Rayleigh quotient ``rho = v^T A v``,

        r = A v - rho v = (lam1 - lam2) sin(phi) cos(phi) * (sin(phi), -cos(phi)),

    so ``r`` is orthogonal to ``v``, has length ``|lam1 - lam2| |sin 2phi| / 2``,
    and vanishes exactly when ``v`` is an eigenvector.
    """

    lam1: float
    lam2: float
    phi: float

    @property
    def A(self) -> np.ndarray:
        return np.diag([self.lam1, self.lam2])

    @property
    def v(self) -> np.ndarray:
        return unit(self.phi)

    @property
    def Av(self) -> np.ndarray:
        return self.A @ self.v

    @property
    def rho(self) -> float:
        return float(self.v @ self.A @ self.v)

    @property
    def rho_v(self) -> np.ndarray:
        return self.rho * self.v

    @property
    def residual(self) -> np.ndarray:
        return self.Av - self.rho_v

    @property
    def residual_norm(self) -> float:
        return float(np.linalg.norm(self.residual))

    def verify(self, *, atol: float = 1e-12) -> None:
        c, s = math.cos(self.phi), math.sin(self.phi)
        closed = (self.lam1 - self.lam2) * s * c * np.array([s, -c])
        np.testing.assert_allclose(self.residual, closed, atol=atol)
        assert abs(float(self.residual @ self.v)) <= atol
        assert math.isclose(
            self.residual_norm,
            abs(self.lam1 - self.lam2) * abs(math.sin(2 * self.phi)) / 2,
            abs_tol=atol,
        )


@dataclass(frozen=True)
class SpectralComponents:
    """The one-vector sine-theta proof, written in the eigenbasis of ``A``.

    ``A`` is diagonal with eigenvalues ``eigenvalues`` and eigenvectors ``f_j``;
    the unit trial vector is ``v = sum_j c_j f_j`` and the trial scalar is
    ``A0 = [rho]``.  The exact subspace ``U = ran F0`` is spanned by the
    eigenvectors whose eigenvalues lie in the window ``(rho - delta, rho + delta)``;
    the others form ``F1``, so the gap hypothesis holds by construction.

    Then ``r = A v - rho v = sum_j (lambda_j - rho) c_j f_j`` and

        ||r||^2 >= sum_{j in F1} (lambda_j - rho)^2 c_j^2
                >= delta^2 sum_{j in F1} c_j^2 = delta^2 sin^2(theta).
    """

    eigenvalues: tuple[float, ...]
    coefficients: tuple[float, ...]
    rho: float
    delta: float
    _c: np.ndarray = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        if len(self.eigenvalues) != len(self.coefficients):
            raise ValueError("need one coefficient per eigenvalue")
        if not self.delta > 0:
            raise ValueError("delta must be positive")
        c = np.asarray(self.coefficients, dtype=float)
        object.__setattr__(self, "_c", c / np.linalg.norm(c))

    @property
    def lam(self) -> np.ndarray:
        return np.asarray(self.eigenvalues, dtype=float)

    @property
    def c(self) -> np.ndarray:
        """Unit-normalized coordinates of ``v`` in the eigenbasis."""
        return self._c

    @property
    def wanted(self) -> np.ndarray:
        """Mask of eigenvalues in the open window, i.e. spanning ``U``."""
        return np.abs(self.lam - self.rho) < self.delta

    @property
    def weights(self) -> np.ndarray:
        """``|lambda_j - rho|``: how much ``A - rho`` stretches ``f_j``."""
        return np.abs(self.lam - self.rho)

    @property
    def residual_coefficients(self) -> np.ndarray:
        return (self.lam - self.rho) * self.c

    @property
    def residual_norm(self) -> float:
        return float(np.linalg.norm(self.residual_coefficients))

    @property
    def sin_theta(self) -> float:
        """``||F1^* v||``: the part of ``v`` outside ``U``."""
        return float(np.linalg.norm(self.c[~self.wanted]))

    @property
    def unwanted_residual_norm(self) -> float:
        return float(np.linalg.norm(self.residual_coefficients[~self.wanted]))

    @property
    def theorem_lhs(self) -> float:
        return self.delta * self.sin_theta

    def verify(self, *, atol: float = 1e-12) -> None:
        A = np.diag(self.lam)
        v = self.c
        r = A @ v - self.rho * v
        np.testing.assert_allclose(r, self.residual_coefficients, atol=atol)
        assert np.all(self.weights[~self.wanted] >= self.delta - atol)
        # sin(theta) is the distance from v to U = span{f_j : j wanted}.
        P_U = np.diag(self.wanted.astype(float))
        assert math.isclose(
            float(np.linalg.norm(v - P_U @ v)), self.sin_theta, abs_tol=atol
        )
        assert self.theorem_lhs <= self.unwanted_residual_norm + atol
        assert self.unwanted_residual_norm <= self.residual_norm + atol


@dataclass(frozen=True)
class SylvesterGrid:
    """The block proof in eigencoordinates.

    With ``Lambda1 = diag(lam)`` and ``A0 = diag(a)``, the Sylvester map
    ``X -> Lambda1 X - X A0`` multiplies entry ``x_ij`` by ``lam_i - a_j``.  If
    every such factor has modulus at least ``delta`` then
    ``||Lambda1 X - X A0||_F >= delta ||X||_F`` entry by entry.  (Other
    unitarily invariant norms need the interval/exterior form of the gap.)
    """

    lam: tuple[float, ...]
    a: tuple[float, ...]
    X: np.ndarray
    delta: float

    @property
    def factors(self) -> np.ndarray:
        return np.subtract.outer(np.asarray(self.lam), np.asarray(self.a))

    @property
    def C(self) -> np.ndarray:
        return self.factors * self.X

    def verify(self, *, atol: float = 1e-12) -> None:
        L, A0 = np.diag(self.lam), np.diag(self.a)
        np.testing.assert_allclose(L @ self.X - self.X @ A0, self.C, atol=atol)
        assert np.all(np.abs(self.factors) >= self.delta - atol)
        assert np.linalg.norm(self.C) >= self.delta * np.linalg.norm(self.X) - atol


@dataclass(frozen=True)
class TwoDirections:
    """The one-vector argument with one wanted and one unwanted eigendirection.

    ``A = diag(lam_u, lam_w)`` with wanted eigenvector ``u = e1`` and unwanted
    eigenvector ``w = e2``; the trial vector is ``v = cos(theta) u + sin(theta) w``
    and ``rho = v^T A v`` (Rayleigh quotient).  Then

        r = (A - rho) v = (lam_u - rho) cos(theta) u + (lam_w - rho) sin(theta) w,

    the gap is ``delta = |lam_w - rho|`` (the single unwanted eigenvalue's
    distance from ``spec(A0) = {rho}``), and

        ||r|| >= |w-part of r| = |lam_w - rho| sin(theta) >= delta sin(theta).

    ``rho`` is not ``lam_u``, so ``r`` also has a ``u``-part: the first
    inequality is strict, which is the honest general picture.
    """

    lam_u: float
    lam_w: float
    theta: float

    @property
    def model(self) -> "RayleighResidual":
        return RayleighResidual(self.lam_u, self.lam_w, self.theta)

    @property
    def rho(self) -> float:
        return self.model.rho

    @property
    def r(self) -> np.ndarray:
        return self.model.residual

    @property
    def u_part(self) -> float:
        return float(self.r[0])

    @property
    def w_part(self) -> float:
        return float(self.r[1])

    @property
    def delta(self) -> float:
        return abs(self.lam_w - self.rho)

    @property
    def sin_theta(self) -> float:
        return math.sin(self.theta)

    @property
    def tan_theta(self) -> float:
        return math.tan(self.theta)

    @property
    def residual_norm(self) -> float:
        return self.model.residual_norm

    def verify(self, *, atol: float = 1e-12) -> None:
        self.model.verify(atol=atol)
        # The tan theta theorem's hypotheses hold (Rayleigh--Ritz value, the one
        # unwanted eigenvalue on one side), and in two dimensions it is an equality:
        # delta = (lam_w - lam_u) cos^2 theta and ||r|| = (lam_w - lam_u) sin theta cos theta.
        if 0 <= self.theta < math.pi / 2:
            assert math.isclose(self.delta * self.tan_theta, self.residual_norm, rel_tol=1e-9, abs_tol=atol)
        assert math.isclose(self.w_part, (self.lam_w - self.rho) * self.sin_theta, abs_tol=atol)
        assert math.isclose(self.u_part, (self.lam_u - self.rho) * math.cos(self.theta), abs_tol=atol)
        assert abs(self.w_part) >= self.delta * self.sin_theta - atol
        assert self.model.residual_norm >= abs(self.w_part) - atol


@dataclass(frozen=True)
class TwoSidedTrial:
    """Why the tan theta theorem needs the unwanted spectrum on one side.

    ``A = diag(-1, 0, 1)``; the wanted eigenvector is ``e2`` (eigenvalue 0) and the
    unwanted eigenvalues ``-1`` and ``+1`` sit on *both* sides of it.  The trial
    vector ``v = cos(theta) e2 + sin(theta) (e1 + e3) / sqrt 2`` has Rayleigh
    quotient ``rho = 0`` and residual ``r = sin(theta) (e3 - e1) / sqrt 2``.

    Every hypothesis of the tan theta theorem holds except one-sidedness
    (``spec A0 = {0}``, ``delta = 1``), and its conclusion ``delta tan(theta) <=
    ||r|| = sin(theta)`` fails for every ``0 < theta < pi/2``.  The sin theta
    theorem, whose gap may be two-sided, holds with equality.  (Davis and Kahan
    make the same point with their Example 6.1.)
    """

    theta: float
    delta: float = 1.0

    @property
    def A(self) -> np.ndarray:
        return np.diag([-self.delta, 0.0, self.delta])

    @property
    def v(self) -> np.ndarray:
        c, s = math.cos(self.theta), math.sin(self.theta)
        return np.array([s / math.sqrt(2), c, s / math.sqrt(2)])

    @property
    def rho(self) -> float:
        return float(self.v @ self.A @ self.v)

    @property
    def residual(self) -> np.ndarray:
        return self.A @ self.v - self.rho * self.v

    @property
    def residual_norm(self) -> float:
        return float(np.linalg.norm(self.residual))

    @property
    def mixed_unwanted_rayleigh(self) -> float:
        """Rayleigh quotient of ``A`` along ``y = (e3 - e1)/sqrt 2``, the unwanted direction ``v`` leans
        into: it averages the unwanted eigenvalues ``-delta`` and ``+delta`` to ``0``, the trial value."""
        y = np.array([-1.0, 0.0, 1.0]) / math.sqrt(2)
        return float(y @ self.A @ y)

    def verify(self, *, atol: float = 1e-12) -> None:
        assert abs(self.rho) <= atol
        assert abs(self.mixed_unwanted_rayleigh - self.rho) <= atol
        assert math.isclose(line_angle(self.v, np.array([0.0, 1.0, 0.0])), self.theta, abs_tol=1e-9)
        assert math.isclose(self.residual_norm, self.delta * math.sin(self.theta), abs_tol=atol)
        if 0 < self.theta < math.pi / 2:
            assert self.delta * math.tan(self.theta) > self.residual_norm


# The concrete instances drawn on the slides.  Keeping them here lets the tests
# check exactly the numbers the audience sees.

ELLIPSE_EIGENVALUES = (2.0, 1.0)
PERTURBATION_EPS = 0.12
PERTURBATION_START_GAP = 1.0
PERTURBATION_END_GAP = 0.02

RESIDUAL_EIGENVALUES = (1.9, 0.7)

COMPONENT_EXAMPLE = SpectralComponents(
    eigenvalues=(-2.5, -1.7, -0.9, -0.3, 0.25, 1.35, 2.1, 2.7),
    coefficients=(0.10, -0.16, 0.30, 0.62, 0.55, -0.26, 0.20, -0.12),
    rho=0.0,
    delta=0.9,
)

SHARP_DELTA = 1.25

TWO_DIRECTIONS = TwoDirections(lam_u=0.8, lam_w=2.6, theta=math.radians(35.0))
TWO_SIDED = TwoSidedTrial(theta=math.pi / 4)
# The family comparison slide uses the gap example at g = 0.1, where the four
# theorems' gaps (0.18, 0.18, 0.26, 0.10) are far enough apart to see.
FAMILY_EXAMPLE_GAP = 0.1
# The reflection and Jacobi slides use a larger gap, so the two ellipses differ visibly.
REFLECT_EXAMPLE_GAP = 0.3
# The "price of doubling" slide: a bound sin 2theta <= 0.6 allows two angle ranges.
SIN2_PRICE_BOUND = 0.6

SYLVESTER_EXAMPLE = SylvesterGrid(
    lam=(-1.9, -1.35, 1.4, 2.05),
    a=(-0.45, 0.05, 0.5),
    X=np.array(
        [
            [0.10, -0.22, 0.05],
            [0.30, 0.12, -0.18],
            [-0.08, 0.26, 0.20],
            [0.14, -0.05, 0.09],
        ]
    ),
    delta=0.9,
)


def gap_picture_example() -> dict[str, tuple[float, ...] | float]:
    """Spectra for the gap slide: ``spec(A0)`` inside, ``spec(Lambda1)`` outside."""
    return {
        "ritz": (-0.45, 0.05, 0.5),
        "beta": -0.45,
        "alpha": 0.5,
        "delta": 0.9,
        "unwanted": (-2.6, -1.9, -1.35, 1.4, 2.05, 2.7),
    }
