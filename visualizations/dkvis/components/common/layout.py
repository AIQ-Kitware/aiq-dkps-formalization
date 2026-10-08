"""Shared layout constants and helpers for slide components."""

from __future__ import annotations

from manim import LEFT

RIGHT_COL_X = 0.75
RIGHT_COL_W = 6.0
RIGHT_LIMIT = 6.85


def fit_right(mob, right: float = RIGHT_LIMIT):
    """Shrink ``mob`` about its left edge if it would cross ``right``."""
    overflow = mob.get_right()[0] - right
    if overflow > 0:
        mob.scale((mob.width - overflow) / mob.width, about_edge=LEFT)
    return mob
