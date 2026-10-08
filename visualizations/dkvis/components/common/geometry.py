"""Shared 2D geometry primitives for Davis--Kahan slide scenes."""

from __future__ import annotations

import math as pymath

import numpy as np
from manim import ORIGIN, TAU, Arc, Arrow, Circle, Line, VMobject

from dkvis import sine_theta_story as story
from dkvis.slide_style import FG, MUTED

DEFAULT_ELLIPSE_ROTATION = np.radians(20.0)


def p3(xy) -> np.ndarray:
    return np.array([xy[0], xy[1], 0.0])


class Plane:
    """Maps model coordinates to the frame: ``origin + scale * rot @ xy``."""

    def __init__(self, origin, scale: float, rotate: float = 0.0):
        self.origin = np.asarray(origin, dtype=float)
        self.scale = scale
        self.rot = story.rotation(rotate)

    def __call__(self, xy) -> np.ndarray:
        return self.origin + p3(self.scale * (self.rot @ np.asarray(xy, dtype=float)))

    def direction_angle(self, xy) -> float:
        d = self.rot @ np.asarray(xy, dtype=float)
        return pymath.atan2(d[1], d[0])


def vec(start, end, color: str, width: float = 6.0) -> VMobject:
    """An arrow from ``start`` to ``end``; empty when too short to draw."""
    length = float(np.linalg.norm(np.asarray(end) - np.asarray(start)))
    if length < 0.03:
        return VMobject()
    return Arrow(
        start,
        end,
        buff=0,
        color=color,
        stroke_width=width,
        max_tip_length_to_length_ratio=min(0.35, 0.28 / max(length, 1e-6) * 1.0),
        max_stroke_width_to_length_ratio=12,
    )


def segment(start, end, color: str, width: float = 6.0) -> Line:
    return Line(start, end, color=color, stroke_width=width)


def through_origin(plane: Plane, direction, half_length: float, color: str, width=3.0, opacity=1.0):
    d = np.asarray(direction, dtype=float)
    d = d / np.linalg.norm(d)
    return Line(
        plane(-half_length * d), plane(half_length * d), color=color, stroke_width=width
    ).set_opacity(opacity)


def ellipse(plane: Plane, M: np.ndarray, color: str = FG, width: float = 3.0) -> Circle:
    """The image ``{plane(M u) : |u| = 1}`` of the unit circle under ``M``."""
    linear = np.eye(3)
    linear[:2, :2] = plane.scale * plane.rot @ np.asarray(M, dtype=float)
    curve = Circle(radius=1.0, color=color, stroke_width=width)
    return curve.apply_matrix(linear, about_point=ORIGIN).shift(plane.origin)


def angle_arc(plane: Plane, start_dir, end_dir, radius: float, color: str, width=3.0) -> Arc:
    a0 = plane.direction_angle(start_dir)
    a1 = plane.direction_angle(end_dir)
    sweep = (a1 - a0 + np.pi) % TAU - np.pi
    return Arc(radius=radius, start_angle=a0, angle=sweep, arc_center=plane.origin, color=color, stroke_width=width)


def right_angle(corner, dir_a, dir_b, size: float = 0.18, color: str = MUTED) -> VMobject:
    a = p3(np.asarray(dir_a, dtype=float) / np.linalg.norm(dir_a)) * size
    b = p3(np.asarray(dir_b, dtype=float) / np.linalg.norm(dir_b)) * size
    mob = VMobject(color=color, stroke_width=2)
    mob.set_points_as_corners([corner + a, corner + a + b, corner + b])
    return mob
