"""Finite projection examples; no rendering dependencies."""
import numpy as np


def projection_example(angle=0.):
    u = np.array([np.cos(angle), np.sin(angle)])
    x = np.array([2., 1.2])
    p = np.outer(u, u)
    return x, p, p @ x, (np.eye(2)-p) @ x


def plane_frame(angle=0.):
    c, s = np.cos(angle), np.sin(angle)
    return np.array([[c, -s], [s, c], [0., 0.]])
