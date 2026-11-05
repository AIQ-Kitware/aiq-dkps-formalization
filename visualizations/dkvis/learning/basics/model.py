"""Small exact-form examples shared by the refresher's diagrams."""
import numpy as np


def matrix_action(x):
    return np.array([[2., 1.], [0., 1.]]) @ np.asarray(x)


def unit_direction(theta):
    return np.array([np.cos(theta), np.sin(theta)])


def eigen_action(x):
    return np.diag([2., 1.]) @ np.asarray(x)


def square_slope(t):
    return t*t, 2*t
