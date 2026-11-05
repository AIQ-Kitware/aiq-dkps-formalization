"""Checked finite illustrations of accepted operator-theory APIs."""
import numpy as np


def rayleigh_example(angle):
    a = np.diag([5., 2.])
    x = np.array([np.cos(angle), np.sin(angle)])
    return a, x, float(x @ a @ x)


def polar_example(angle=.6):
    rotation = np.array([[np.cos(angle), -np.sin(angle)],
                         [np.sin(angle), np.cos(angle)]])
    modulus = np.diag([2., 0.])
    partial = rotation @ np.diag([1., 0.])
    return partial @ modulus, modulus, partial


def sylvester_example():
    a, b = np.diag([3., 4.]), np.diag([0., 1.])
    residual = np.array([[1., 2.], [3., 4.]])
    gaps = np.diag(a)[:, None]-np.diag(b)[None, :]
    return a, b, residual, residual/gaps
