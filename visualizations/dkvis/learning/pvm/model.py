"""Finite spectral example used to illustrate the PVM laws, with multiplicity."""
import numpy as np

EIGENVALUES=np.array([1.,2.,2.,4.])


def eigenbasis():
    angle=np.pi/6
    q=np.eye(4)
    q[:2,:2]=[[np.cos(angle),-np.sin(angle)],[np.sin(angle),np.cos(angle)]]
    return q


def spectral_function(values):
    values=np.asarray(values)
    q=eigenbasis()
    return (q*values) @ q.T


def projection(lower,upper):
    return spectral_function((lower<=EIGENVALUES)&(EIGENVALUES<=upper))


def atom_masses(x):
    coefficients=eigenbasis().T @ np.asarray(x)
    return np.array([np.sum(np.abs(coefficients[EIGENVALUES==value])**2)
                     for value in [1.,2.,4.]])


def example_vector():
    return eigenbasis() @ np.full(4,.5)
