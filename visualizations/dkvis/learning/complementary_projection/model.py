"""Geometric projection errors and orthogonal-motion displacement examples."""
import numpy as np


def line_error(angle):
    p = np.diag([1., 0.])
    v = np.array([np.cos(angle), np.sin(angle)])
    return p, v, p @ v, (np.eye(2)-p) @ v


def rotation_displacement(angle):
    c, s = np.cos(angle), np.sin(angle)
    w = np.array([[c, -s], [s, c]])
    u = np.array([1., 0.])
    return w, u, w @ u, (np.eye(2)-w) @ u


def frame_error(angles):
    angles = np.asarray(angles, dtype=float)
    rank = len(angles)
    p = np.diag(np.r_[np.ones(rank), np.zeros(rank)])
    frame = np.vstack([np.diag(np.cos(angles)), np.diag(np.sin(angles))])
    complement = np.vstack([np.zeros((rank, rank)), np.eye(rank)])
    lifted = (np.eye(2*rank)-p) @ frame
    coordinates = complement.T @ frame
    return p, frame, complement, lifted, coordinates
