"""Small real matrix examples for teaching the exponential.

Taylor truncation illustrates the definition at modest matrix norms. It is not
an implementation of a production scaling-and-squaring algorithm.
"""
import numpy as np


def taylor_exponential(a, t=1., terms=40):
    a = np.asarray(a, dtype=float)
    if a.ndim != 2 or a.shape[0] != a.shape[1]:
        raise ValueError('the exponential requires a square matrix')
    if terms < 0:
        raise ValueError('terms must be nonnegative')
    result = np.eye(a.shape[0])
    term = result.copy()
    for k in range(1, terms+1):
        term = (term @ (t*a))/k
        result += term
    return result


def euler_path(a, t, steps, initial):
    if steps < 1:
        raise ValueError('steps must be positive')
    a = np.asarray(a, dtype=float)
    step = np.eye(a.shape[0])+(t/steps)*a
    states = [np.asarray(initial, dtype=float)]
    for _ in range(steps):
        states.append(step @ states[-1])
    return np.asarray(states)


def shear_generator():
    return np.array([[0., 1.], [0., 0.]])


def noncommuting_generators():
    a = shear_generator()
    return a, a.T


def opening_flow(time):
    """Scalar growth and a coupled two-coordinate flow at the same real time.

    The matrix generator is J = [[0, -1], [1, 0]], with initial state (1, 0).
    This closed form supplies the graph, independently of Taylor truncation.
    """
    time = np.asarray(time, dtype=float)
    return np.exp(.4*time), np.stack([np.cos(time), np.sin(time)], axis=-1)
