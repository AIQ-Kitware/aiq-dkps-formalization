"""Exact formulas behind the uniform-band and moving-dip illustrations."""
import numpy as np

def band_cost(x, epsilon):
    return np.asarray(x)**2 + epsilon*np.sin(3*np.asarray(x))

def moving_dip(x, n):
    return -np.maximum(0.,1.-3*n*np.abs(np.asarray(x)-1/n))
