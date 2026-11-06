"""Small real examples illustrating the deterministic population-gap bound."""
import numpy as np


def rotation(theta):
    c, s = np.cos(theta), np.sin(theta)
    return np.array([[c, -s], [s, c]])


def rotated_example(theta):
    population = np.diag([3., 1.])
    q = rotation(theta)
    sample = q @ population @ q.T
    frame = q[:, :1]
    residual = 3*frame - population @ frame
    return population, sample, frame, residual


def mixed_gap_example():
    population = np.array([50., 40., 30., 20., 10.])
    sample = np.array([54., 37., 32., 23., 21.])
    # Published example: indices 2..4 (one-based) have population interval [20,40].
    gap = min(population[0]-population[1], population[3]-population[4])
    mixed_gap = max(0., min(sample[0]-population[1], population[3]-sample[4]))
    return population, sample, gap, mixed_gap
