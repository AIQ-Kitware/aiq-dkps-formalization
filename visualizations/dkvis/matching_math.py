"""Finite matrix examples for the real matching proof study deck.

These computations illustrate existing Lean results, rather than supply proofs.
Nuclear matching weights and the three-angle example remain in novelty_math.
"""
from __future__ import annotations

import math
import numpy as np


def rotation(theta: float) -> np.ndarray:
    c, s = math.cos(theta), math.sin(theta)
    return np.array([[c, -s], [s, c]])


def source_generator(a: float, b: float) -> np.ndarray:
    """An explicitly constructed skew direction on K + K-perp, each rank two."""
    j = np.array([[0., -1.], [1., 0.]])
    zero = np.zeros((2, 2))
    return np.block([[a*j, zero], [zero, b*j]])


def source_variation(a: float, b: float, t: float) -> np.ndarray:
    """Its actual exponential: independent rotations within the two spaces."""
    zero = np.zeros((2, 2))
    return np.block([[rotation(a*t), zero], [zero, rotation(b*t)]])


def source_plane_wiggle(t: float, tilt: float = .65) -> tuple[np.ndarray, np.ndarray]:
    """Fixed W and a source-preserving V(t) for the three-dimensional picture.

    K is the xy plane; W tilts it about the x axis. W V(t) has the same image
    plane for every t, although the images of the individual basis vectors move.
    """
    w = np.eye(3)
    w[1:, 1:] = rotation(tilt)
    v = np.eye(3)
    v[:2, :2] = rotation(t)
    return w, v


def phase_cost(theta, p: float):
    if p < 1:
        raise ValueError("the study examples use p >= 1")
    t = np.asarray(theta)
    if np.any((t < 0) | (t > math.pi)):
        raise ValueError("phase must be in [0, pi]")
    return (2 * np.sin(t / 2)) ** p


def phase_derivative(theta, p: float):
    if p <= 1:
        raise ValueError("the smooth proof requires p > 1")
    t = np.asarray(theta)
    if np.any((t < 0) | (t > math.pi)):
        raise ValueError("phase must be in [0, pi]")
    value = p * (2 * np.sin(t / 2)) ** (p - 1) * np.cos(t / 2)
    return np.where((t == 0) | (t == math.pi), 0., value)


def phase_level_roots(p: float, level: float) -> tuple[float, ...]:
    critical = 2 * math.atan(math.sqrt(p - 1)) if p > 1 else 0.
    peak = float(phase_derivative(critical, p))
    if not 0 < level <= peak:
        raise ValueError("choose a positive level at most the derivative maximum")
    if math.isclose(level, peak, rel_tol=1e-12):
        return (critical,)
    roots = []
    for lo, hi, increasing in [(0., critical, True), (critical, math.pi, False)]:
        for _ in range(55):
            mid = (lo + hi) / 2
            if (float(phase_derivative(mid, p)) < level) == increasing:
                lo = mid
            else:
                hi = mid
        roots.append((lo + hi) / 2)
    return tuple(roots)


def pair_parameters(theta: float, psi: float) -> tuple[float, float]:
    if not (0 <= theta <= math.pi / 2 and 0 <= psi <= math.pi / 2):
        raise ValueError("principal angles must be in [0, pi/2]")
    return (theta + psi) / 2, abs(theta - psi) / 2


def paired_power_cost(theta: float, psi: float, tau, p: float):
    h, d = pair_parameters(theta, psi)
    tau = np.asarray(tau)
    if np.any((tau < d - 1e-12) | (tau > h + 1e-12)):
        raise ValueError("pair parameter must be in [d,h]")
    return 2 * (phase_cost(np.clip(h + tau, 0, math.pi), p)
                + phase_cost(np.clip(h - tau, 0, math.pi), p))


def pair_direct_rotation(theta: float, psi: float) -> np.ndarray:
    pair_parameters(theta, psi)
    c, s = np.diag(np.cos([theta, psi])), np.diag(np.sin([theta, psi]))
    return np.block([[c, -s], [s, c]])


def pair_transporter(theta: float, psi: float, tau: float) -> np.ndarray:
    h, d = pair_parameters(theta, psi)
    if not d - 1e-12 <= tau <= h + 1e-12:
        raise ValueError("pair parameter must be in [d,h]")
    gamma = math.acos(float(np.clip(math.cos(tau) / math.cos(d), 0, 1)))
    r, zero = rotation(gamma), np.zeros((2, 2))
    return pair_direct_rotation(theta, psi) @ np.block([[r, zero], [zero, r]])


def phase_rectangle_edge(x: float, y: float, h: float, d: float) -> tuple[float, float, float]:
    """Fold a phase point, then return x,y,tau for the cost-decreasing edge step."""
    if not (0 <= d <= h and h + d <= math.pi / 2 + 1e-12):
        raise ValueError("invalid principal-angle half-sum and half-difference")
    if not (h <= x <= math.pi - h and d <= y <= math.pi - d):
        raise ValueError("point is outside the phase rectangle")
    if x + y > math.pi:
        x, y = math.pi - x, math.pi - y
    return x, y, max(d, h - abs(x - y))


def displacement_power(w: np.ndarray, p: float) -> float:
    return float(np.sum(np.linalg.svd(np.eye(len(w)) - w, compute_uv=False) ** p))


def skew_gradient(w: np.ndarray, p: float) -> np.ndarray:
    """Real right-variation gradient G, so the derivative is -tr(G B)."""
    if p <= 1:
        raise ValueError("gradient requires p > 1")
    if not np.allclose(w.T @ w, np.eye(len(w)), atol=1e-10):
        raise ValueError("W must be orthogonal")
    u, singular, vt = np.linalg.svd(np.eye(len(w)) - w)
    ambient = p * (u * singular ** (p - 1)) @ vt
    product = ambient.T @ w
    return (product - product.T) / 2
