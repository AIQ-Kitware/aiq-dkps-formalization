"""Manim animation for the rank-one Davis--Kahan sine-theta theorem.

Render from ``visualizations/`` with:

    uv run --extra manim manim -pql dkvis/manim_sine_theta.py SineThetaScene

The animation uses the same mathematical model as the VTK explorer.
"""

from __future__ import annotations

import math

import numpy as np
from manim import (
    BLUE,
    DOWN,
    FadeIn,
    GREEN,
    LEFT,
    Line,
    MathTex,
    NumberPlane,
    ORIGIN,
    PINK,
    RED,
    RIGHT,
    Scene,
    Text,
    UP,
    ValueTracker,
    WHITE,
    YELLOW,
    always_redraw,
    Create,
)

from dkvis.sine_theta import SineThetaModel


class SineThetaScene(Scene):
    """Animate the sharp rank-one specialization ``delta sin(theta) = ||R||``."""

    delta = 1.0

    def construct(self) -> None:
        plane = NumberPlane(
            x_range=[-1.4, 1.4, 0.5],
            y_range=[-1.15, 1.45, 0.5],
            x_length=7.0,
            y_length=6.0,
            background_line_style={"stroke_opacity": 0.22},
        ).shift(LEFT * 2.0)
        self.play(Create(plane))

        title = Text("Davis--Kahan sin theta", font_size=38).to_edge(UP)
        subtitle = MathTex(r"\delta\,\|\sin\Theta_0\| \le \|R\|").next_to(title, DOWN)
        self.play(FadeIn(title), FadeIn(subtitle))

        theta = ValueTracker(math.radians(12.0))

        exact = Line(plane.c2p(-1.25, 0), plane.c2p(1.25, 0), color=WHITE, stroke_width=6)
        exact_label = MathTex(r"U").next_to(plane.c2p(1.15, 0), DOWN)
        self.play(Create(exact), FadeIn(exact_label))

        def model() -> SineThetaModel:
            return SineThetaModel(theta.get_value(), delta=self.delta)

        trial_line = always_redraw(
            lambda: Line(
                plane.c2p(*(-1.25 * model().trial_vector)),
                plane.c2p(*(1.25 * model().trial_vector)),
                color=YELLOW,
                stroke_width=5,
            )
        )
        vector = always_redraw(
            lambda: Line(
                plane.c2p(0, 0),
                plane.c2p(*model().trial_vector),
                color=YELLOW,
                stroke_width=8,
            )
        )
        projection = always_redraw(
            lambda: Line(
                plane.c2p(0, 0),
                plane.c2p(*model().desired_projection),
                color=GREEN,
                stroke_width=7,
            )
        )
        sine_block = always_redraw(
            lambda: Line(
                plane.c2p(*model().desired_projection),
                plane.c2p(*model().trial_vector),
                color=PINK,
                stroke_width=8,
            )
        )
        residual = always_redraw(
            lambda: Line(
                plane.c2p(0, 0),
                plane.c2p(*model().residual),
                color=BLUE,
                stroke_width=6,
            )
        )

        self.play(Create(trial_line), Create(vector), Create(projection), Create(sine_block))
        self.play(Create(residual))

        labels = (
            MathTex(r"v_\theta", color=YELLOW),
            MathTex(r"P_Uv_\theta", color=GREEN),
            MathTex(r"(I-P_U)v_\theta", color=PINK),
            MathTex(r"R=A v_\theta-A_0v_\theta", color=BLUE),
        )
        labels[0].to_corner(RIGHT + UP).shift(DOWN * 1.6)
        labels[1].next_to(labels[0], DOWN, aligned_edge=LEFT)
        labels[2].next_to(labels[1], DOWN, aligned_edge=LEFT)
        labels[3].next_to(labels[2], DOWN, aligned_edge=LEFT)
        self.play(*[FadeIn(item) for item in labels])

        identity = MathTex(
            r"(I-P_U)v_\theta=(0,\sin\theta)",
            r"\quad\Rightarrow\quad",
            r"\|\sin\Theta_0\|=\sin\theta",
        ).scale(0.82).to_edge(DOWN).shift(RIGHT * 1.6)
        residual_formula = MathTex(
            r"A=\operatorname{diag}(0,\delta),\ A_0=0",
            r"\quad\Rightarrow\quad",
            r"R=(0,\delta\sin\theta)",
        ).scale(0.78).next_to(identity, UP)
        sharp = MathTex(r"\boxed{\delta\sin\theta=\|R\|}").scale(1.1).next_to(
            residual_formula, UP
        )
        self.play(FadeIn(identity), FadeIn(residual_formula), FadeIn(sharp))

        self.play(theta.animate.set_value(math.radians(65.0)), run_time=5.0)
        self.play(theta.animate.set_value(math.radians(28.0)), run_time=3.0)
        self.wait(1.0)
