"""Manim explanation of the Proposition 4.4 counterexample.

Render from ``visualizations/`` with:

    uv run --extra manim python -m manim -pql dkvis/manim_prop44.py Prop44Scene

The scene uses exact invariant-plane decompositions of the endpoint operators:

* the direct rotation R is +pi/4 on span(e0,e3) and -pi/4 on span(e1,e2);
* the competitor W is +pi/2 on span(m0,m1) and the identity on span(m2,m3).

These are different decompositions of R^4.  The animation intentionally labels
them separately rather than pretending that W rotates one of R's principal
planes by 90 degrees.
"""

from __future__ import annotations

import math

from manim import (
    BLUE,
    Circle,
    Create,
    Dot,
    DOWN,
    FadeIn,
    FadeOut,
    GREEN,
    LEFT,
    Line,
    MathTex,
    ORANGE,
    RED,
    RIGHT,
    Rotate,
    Scene,
    Text,
    UP,
    VGroup,
    WHITE,
    YELLOW,
)

from dkvis.prop44 import Prop44Model


class Prop44Scene(Scene):
    """Show why the trace norm favors the Proposition 4.4 competitor."""

    def _plane_panel(self, center, *, title: str, color):
        circle = Circle(radius=0.72, color=WHITE, stroke_opacity=0.38).move_to(center)
        axis = Line(center + LEFT * 0.78, center + RIGHT * 0.78, color=WHITE, stroke_opacity=0.20)
        arrow = Line(center, center + RIGHT * 0.62, color=color, stroke_width=8)
        start = Dot(center + RIGHT * 0.62, radius=0.045, color=WHITE, fill_opacity=0.7)
        label = Text(title, font_size=22).next_to(circle, UP, buff=0.12)
        return VGroup(circle, axis, label, start), arrow, start

    def construct(self) -> None:
        model = Prop44Model()
        model.verify()

        title = Text("Davis--Kahan Proposition 4.4 counterexample", font_size=36).to_edge(UP)
        hypothesis = MathTex(
            r"\theta_1=\theta_2=\pi/4<\pi/3,\qquad R\mathcal U=W\mathcal U=\mathcal V"
        ).scale(0.78).next_to(title, DOWN, buff=0.16)
        self.play(FadeIn(title), FadeIn(hypothesis))

        left_title = Text("Direct rotation R", font_size=29, color=BLUE).move_to(LEFT * 3.4 + UP * 2.15)
        right_title = Text("Competitor W", font_size=29, color=ORANGE).move_to(RIGHT * 3.4 + UP * 2.15)
        self.play(FadeIn(left_title), FadeIn(right_title))

        d1_group, d1_arrow, d1_start = self._plane_panel(
            LEFT * 3.4 + UP * 0.85,
            title="span(e0,e3)",
            color=BLUE,
        )
        d2_group, d2_arrow, d2_start = self._plane_panel(
            LEFT * 3.4 + DOWN * 1.15,
            title="span(e1,e2)",
            color=GREEN,
        )
        w1_group, w1_arrow, w1_start = self._plane_panel(
            RIGHT * 3.4 + UP * 0.85,
            title="span(m0,m1)",
            color=ORANGE,
        )
        w2_group, w2_arrow, w2_start = self._plane_panel(
            RIGHT * 3.4 + DOWN * 1.15,
            title="span(m2,m3)",
            color=YELLOW,
        )
        panels = VGroup(d1_group, d2_group, w1_group, w2_group)
        arrows = VGroup(d1_arrow, d2_arrow, w1_arrow, w2_arrow)
        self.play(FadeIn(panels), Create(arrows))

        d1_center = d1_group[0].get_center()
        d2_center = d2_group[0].get_center()
        w1_center = w1_group[0].get_center()
        self.play(
            Rotate(d1_arrow, angle=math.pi / 4, about_point=d1_center),
            Rotate(d2_arrow, angle=-math.pi / 4, about_point=d2_center),
            Rotate(w1_arrow, angle=math.pi / 2, about_point=w1_center),
            run_time=2.0,
        )

        d1_end = d1_arrow.get_end()
        d2_end = d2_arrow.get_end()
        w1_end = w1_arrow.get_end()
        w2_end = w2_arrow.get_end()
        chords = VGroup(
            Line(d1_start.get_center(), d1_end, color=RED, stroke_width=5),
            Line(d2_start.get_center(), d2_end, color=RED, stroke_width=5),
            Line(w1_start.get_center(), w1_end, color=RED, stroke_width=5),
            Line(w2_start.get_center(), w2_end, color=RED, stroke_width=5),
        )
        angle_labels = VGroup(
            MathTex(r"+45^\circ").scale(0.55).next_to(d1_group[0], RIGHT, buff=0.08),
            MathTex(r"-45^\circ").scale(0.55).next_to(d2_group[0], RIGHT, buff=0.08),
            MathTex(r"+90^\circ").scale(0.55).next_to(w1_group[0], LEFT, buff=0.08),
            MathTex(r"0^\circ").scale(0.55).next_to(w2_group[0], LEFT, buff=0.08),
        )
        self.play(Create(chords), FadeIn(angle_labels))

        explanation = Text(
            "R moves every direction by the same chord length; W concentrates\n"
            "the displacement into one invariant 2-plane and fixes the other.",
            font_size=22,
            line_spacing=0.9,
        ).to_edge(DOWN, buff=0.38)
        self.play(FadeIn(explanation))
        self.wait(1.0)

        self.play(
            FadeOut(panels),
            FadeOut(arrows),
            FadeOut(chords),
            FadeOut(angle_labels),
            FadeOut(left_title),
            FadeOut(right_title),
            FadeOut(explanation),
        )

        c = math.sqrt(2.0 - math.sqrt(2.0))
        singular_title = Text("Full-displacement singular values", font_size=30).shift(UP * 1.65)
        direct_sv = MathTex(
            r"\sigma(I-R)=(c,c,c,c),\qquad c=\sqrt{2-\sqrt2}\approx",
            f"{c:.3f}",
        ).scale(0.80).shift(UP * 0.72)
        competitor_sv = MathTex(
            r"\sigma(I-W)=(\sqrt2,\sqrt2,0,0)"
        ).scale(0.85).shift(DOWN * 0.15)
        self.play(FadeIn(singular_title), FadeIn(direct_sv), FadeIn(competitor_sv))

        trace_direct = model.direct_trace_displacement
        trace_comp = model.competitor_trace_displacement
        comparison = MathTex(
            r"\|I-W\|_* = 2\sqrt2 \approx",
            f"{trace_comp:.3f}",
            r"\;<\;",
            r"4\sqrt{2-\sqrt2}\approx",
            f"{trace_direct:.3f}",
            r"=\|I-R\|_*",
        ).scale(0.78).shift(DOWN * 1.12)
        verdict = Text(
            "The admissible competitor has smaller trace displacement.",
            font_size=25,
            color=RED,
        ).next_to(comparison, DOWN, buff=0.34)
        self.play(FadeIn(comparison), FadeIn(verdict))
        self.wait(2.0)
