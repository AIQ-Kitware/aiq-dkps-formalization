"""Checked matrix examples used by the singular-value-norm lesson."""
import numpy as np
from dkvis.learning.matching.model import rotation


def ellipse_example():
    u, v = rotation(.55), rotation(.4)
    singular = np.array([2., .75])
    return u @ np.diag(singular) @ v.T, u, singular, v


def competing_displacements():
    reflection = np.diag([-1., 1.])
    turn = rotation(2*np.arcsin(.55))
    return tuple(np.linalg.svd(np.eye(2)-w, compute_uv=False) for w in [reflection, turn])


def overlapping_restrictions():
    return np.array([[1., 1.], [0., 0.]])


def block_displacement():
    first = np.eye(2)-rotation(np.pi/3)
    second = np.diag([2., 0.])
    zero = np.zeros((2, 2))
    return first, second, np.block([[first, zero], [zero, second]])
