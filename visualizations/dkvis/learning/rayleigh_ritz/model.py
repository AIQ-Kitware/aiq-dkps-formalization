"""Finite examples: geometric leakage and a two-dimensional trial compression."""
import numpy as np


def line_example(angle):
    a = np.diag([1., 4.])
    q = np.array([np.cos(angle), np.sin(angle)])
    theta = q @ a @ q
    return a, q, theta, a @ q - theta*q


def trial_example():
    a = np.array([[2., 1., 1.], [1., 2., -1.], [1., -1., 5.]])
    q = np.eye(3)[:, :2]
    b = q.T @ a @ q
    r = a @ q - q @ b
    return a, q, b, r


def ritz_pairs(a, q):
    values, y = np.linalg.eigh(q.conj().T @ a @ q)
    u = q @ y
    return values, u, a @ u - u*values


def trial_action(coordinates):
    """One input, its true output, the retained output, and the escaping output."""
    a, q, b, r = trial_example()
    y = np.asarray(coordinates)
    return q@y, a@q@y, q@b@y, r@y


def trial_quotient(angle):
    a, q, b, r = trial_example()
    y = np.array([np.cos(angle), np.sin(angle)])
    return y, q@y, float(y@b@y)


def nested_extrema():
    """First-coordinate line, first-two-coordinate plane, and full ambient space."""
    a, _, _, _ = trial_example()
    return [(np.linalg.eigvalsh(a[:k, :k])[0], np.linalg.eigvalsh(a[:k, :k])[-1])
            for k in [1, 2, 3]]
