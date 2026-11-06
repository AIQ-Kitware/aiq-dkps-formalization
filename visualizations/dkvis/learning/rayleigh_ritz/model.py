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
