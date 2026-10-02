"""Slides: Davis--Kahan Proposition 4.4 is false as printed.

The printed claim: over a real space, if every principal angle between ``U``
and ``V`` is at most ``pi/3``, then among all orthogonal ``W`` with
``W(U) = V`` the direct rotation minimizes ``||I - W||`` in every unitarily
invariant norm.  The repository refutes it with an explicit ``R^4`` witness
(both principal angles ``pi/4``) and proves the repair for ``Q``-norms.

Every number comes from :class:`dkvis.prop44.Prop44Model`, the same checked
model the VTK and Manim Proposition 4.4 scenes use.
"""

from __future__ import annotations

import math as pymath

import numpy as np
from manim import (
    DOWN,
    LEFT,
    RIGHT,
    UP,
    Arc,
    Arrow,
    Axes,
    Circle,
    Create,
    DashedLine,
    Dot,
    FadeIn,
    Line,
    Rectangle,
    Transform,
    ValueTracker,
    VGroup,
    always_redraw,
    rate_functions,
)

from dkvis.prop44 import Prop44Model
from dkvis.slide_style import (
    EXACT,
    FAINT,
    FG,
    MUTED,
    PANEL,
    SINE,
    TRIAL,
    DeckSlide,
    boxed,
    math,
    mono,
    para,
    tex,
)

MODEL = Prop44Model()


def chord(alpha: float) -> float:
    """Either singular value of ``I - Rot(alpha)`` on a real 2-plane."""
    return MODEL.rotation_plane_singular_value(alpha)


def norms(singular_values: np.ndarray) -> dict[str, float]:
    sv = np.asarray(singular_values)
    return {"op": float(sv.max()), "fro": float(np.sqrt((sv**2).sum())), "trace": float(sv.sum())}


R_NORMS = norms(MODEL.direct_singular_values)
W_NORMS = norms(MODEL.competitor_singular_values)


def arrow(start, end, color, width=6.0):
    return Arrow(start, end, buff=0, color=color, stroke_width=width, max_tip_length_to_length_ratio=0.22)


def p3(x, y) -> np.ndarray:
    return np.array([x, y, 0.0])


class P4Slide(DeckSlide):
    section = "Davis--Kahan Proposition 4.4 $\\cdot$ a printed claim that is false"


# ----------------------------------------------------------------------------
# The claim
# ----------------------------------------------------------------------------


class P01Claim(P4Slide):
    title = "A second result: Proposition 4.4 is false"
    kicker = "Which orthogonal map carries one subspace onto another with the least motion?"

    def body(self) -> None:
        theta = np.radians(35.0)
        scale = 1.2

        def panel(center):
            c = np.asarray(center, float)
            U = Line(c + p3(-1.35, 0) * scale, c + p3(1.35, 0) * scale, color=EXACT, stroke_width=4)
            d = np.array([np.cos(theta), np.sin(theta), 0.0])
            V = Line(c - 1.35 * scale * d, c + 1.35 * scale * d, color=TRIAL, stroke_width=4)
            lu = math(r"U", size=28, color=EXACT).next_to(c + p3(1.35, 0) * scale, DOWN, buff=0.08)
            lv = math(r"V", size=28, color=TRIAL).next_to(c + 1.35 * scale * d, UP, buff=0.05)
            return VGroup(U, V, lu, lv)

        top_c, bot_c = p3(-3.9, 0.85), p3(-3.9, -2.05)
        top, bot = panel(top_c), panel(bot_c)
        top_lbl = tex(r"direct rotation", size=26, color=FG).move_to(top_c + p3(-2.3, 1.5), aligned_edge=LEFT)
        bot_lbl = tex(r"a reflection", size=26, color=FG).move_to(bot_c + p3(-2.3, 1.5), aligned_edge=LEFT)

        e1, e2 = np.array([1.0, 0.0]), np.array([0.0, 1.0])
        rot = np.array([[np.cos(theta), -np.sin(theta)], [np.sin(theta), np.cos(theta)]])
        refl = np.array([[np.cos(theta), np.sin(theta)], [np.sin(theta), -np.cos(theta)]])

        def frame(center, M=np.eye(2)):
            c = np.asarray(center, float)
            a = arrow(c, c + scale * p3(*(M @ e1)), FG)
            b = arrow(c, c + scale * p3(*(M @ e2)), MUTED)
            return VGroup(a, b)

        def moves(center, M):
            c = np.asarray(center, float)
            return VGroup(
                *[
                    DashedLine(c + scale * p3(*x), c + scale * p3(*(M @ x)), color=SINE, stroke_width=4, dash_length=0.07)
                    for x in (e1, e2)
                ]
            )

        x_text, w_text = 0.2, 6.6
        t1 = para(
            r"Many orthogonal maps carry the subspace $\cx{exact}{U}$ onto $\cx{trial}{V}$. "
            r"The \emph{direct rotation} turns by exactly the principal angles and does nothing else.",
            width=w_text,
            size=25,
        )
        t2 = para(
            r"A reflection also carries $U$ onto $V$, but it moves other vectors much further. "
            r"(\cx{sine}{Pink}: how far each vector moves.)",
            width=w_text,
            size=25,
        )
        claim = boxed(
            para(
                r"\textbf{Proposition 4.4 (as printed).} Over $\mathbb{R}$, if every principal angle is "
                r"at most $\pi/3$, then among all orthogonal $W$ with $W(U)=V$ the direct rotation "
                r"minimizes $\norm{I-W}$, in \emph{every} unitarily invariant norm.",
                width=w_text - 0.4,
                size=25,
            ),
            color=FG,
            pad=0.2,
        )
        t3 = para(
            r"$\norm{I-W}$ measures how much $W$ moves space. Plausible: in the plane the direct rotation "
            r"beats the reflection below $\pi/3$ (checked in Lean for the paper's example).",
            width=w_text,
            size=22,
            color=MUTED,
        )
        verdict = boxed(
            tex(r"False as printed: there is a counterexample in $\mathbb{R}^4$.", size=27),
            color=SINE,
            pad=0.2,
        )
        col = VGroup(t1, t2, claim, t3, verdict).arrange(DOWN, aligned_edge=LEFT, buff=0.26)
        col.move_to([x_text, self.content_top - 0.1, 0], aligned_edge=UP + LEFT)
        for m in col:
            if m.get_right()[0] > 6.85:
                m.scale((6.85 - x_text) / (m.get_right()[0] - x_text), about_edge=LEFT)

        self.say(
            "The second result of the project. Take two subspaces U and V. Many orthogonal maps carry U onto V. "
            "Davis and Kahan single out the direct rotation: it turns by exactly the principal angles."
        )
        f_top = frame(top_c)
        self.play(FadeIn(top), FadeIn(top_lbl), FadeIn(f_top), FadeIn(t1))
        self.play(Transform(f_top, frame(top_c, rot)), FadeIn(moves(top_c, rot)), run_time=1.5)

        self.say(
            "A reflection across the bisector also carries U onto V, but the other direction gets thrown "
            "across the plane. The pink segments show how far each vector moved."
        )
        f_bot = frame(bot_c)
        self.play(FadeIn(bot), FadeIn(bot_lbl), FadeIn(f_bot), FadeIn(t2))
        self.play(Transform(f_bot, frame(bot_c, refl)), FadeIn(moves(bot_c, refl)), run_time=1.5)

        self.say(
            "Proposition 4.4 says the direct rotation always moves space the least, measured by any "
            "unitarily invariant norm of I minus W, provided the angles are at most pi over 3. "
            "In the plane this is right, which makes it believable."
        )
        self.play(FadeIn(claim), FadeIn(t3))

        self.say("But as printed it is false, and we can exhibit the counterexample.")
        self.play(FadeIn(verdict, shift=UP * 0.1))


# ----------------------------------------------------------------------------
# The counterexample
# ----------------------------------------------------------------------------

PLANES = [
    # (column, row, label, angle, colour)
    (0, 0, r"plane $\langle e_0,e_3\rangle$", np.pi / 4, EXACT),
    (0, 1, r"plane $\langle e_1,e_2\rangle$", np.pi / 4, EXACT),
    (1, 0, r"moving plane", np.pi / 2, TRIAL),
    (1, 1, r"fixed plane", 0.0, TRIAL),
]


class P02Counterexample(P4Slide):
    title = r"The counterexample in $\mathbb{R}^4$"
    kicker = r"Both principal angles are $\pi/4$; two maps carry $U$ onto $V$"

    def body(self) -> None:
        radius = 0.78
        centers = {(0, 0): p3(-5.35, 0.75), (0, 1): p3(-5.35, -1.65), (1, 0): p3(-2.55, 0.75), (1, 1): p3(-2.55, -1.65)}
        t = ValueTracker(0.0)

        heads = VGroup(
            tex(r"direct rotation $\mathcal R$", size=26, color=EXACT).move_to(centers[(0, 0)] + p3(0, 1.3)),
            tex(r"competitor $W$", size=26, color=TRIAL).move_to(centers[(1, 0)] + p3(0, 1.3)),
        )
        panels = VGroup()
        for col, row, label, alpha, color in PLANES:
            c = centers[(col, row)]
            circ = Circle(radius=radius, color=FAINT, stroke_width=2).move_to(c)
            start = c + radius * p3(1, 0)
            base = Line(c, start, color=MUTED, stroke_width=3)

            def tip(c=c, alpha=alpha):
                a = alpha * t.get_value()
                return c + radius * p3(np.cos(a), np.sin(a))

            spoke = always_redraw(lambda c=c, color=color, tip=tip: Line(c, tip(), color=color, stroke_width=5))
            ch = always_redraw(lambda start=start, tip=tip: Line(start, tip(), color=SINE, stroke_width=6))
            arc = always_redraw(
                lambda c=c, alpha=alpha: Arc(
                    radius=0.3, start_angle=0, angle=max(alpha * t.get_value(), 1e-3), arc_center=c, color=FG, stroke_width=2.5
                )
            )
            deg = tex(rf"${pymath.degrees(alpha):.0f}^\circ$", size=24, color=FG).move_to(c + p3(0, -radius - 0.25))
            lbl = tex(label, size=20, color=MUTED).move_to(c + p3(0, radius + 0.22))
            panels.add(VGroup(circ, base, spoke, ch, arc, deg, lbl))

        x0, w = 0.05, 6.7
        intro = para(
            r"Each map turns two perpendicular planes. A plane turned by $\alpha$ contributes two "
            r"singular values of $I-W$, both equal to the \cx{sine}{chord} $2\sin(\alpha/2)$.",
            width=w,
            size=24,
        )
        intro.move_to([x0, self.content_top - 0.15, 0], aligned_edge=UP + LEFT)

        self.say(
            "Here are both maps, one 2-plane at a time. The direct rotation turns two planes by 45 degrees "
            "each. The competitor turns one plane by 90 degrees and leaves the other fixed. Both carry U onto V."
        )
        self.play(FadeIn(heads), *[FadeIn(p) for p in panels], FadeIn(intro))
        self.play(t.animate.set_value(1.0), run_time=2.5, rate_func=rate_functions.ease_in_out_sine)

        # Trace norm = sum of all chords: stack them end to end.
        unit = 1.55
        bar_h = 0.3

        def stacked(lengths, color, y):
            segs, x = VGroup(), x0 + 0.55
            for L in lengths:
                if L < 1e-9:
                    continue
                seg = Rectangle(width=unit * L, height=bar_h, fill_color=color, fill_opacity=0.85, stroke_color=PANEL, stroke_width=2)
                seg.move_to([x, y, 0], aligned_edge=LEFT)
                segs.add(seg)
                x += unit * L
            return segs

        y_r, y_w = intro.get_bottom()[1] - 0.65, intro.get_bottom()[1] - 1.1
        r_sv, w_sv = MODEL.direct_singular_values, MODEL.competitor_singular_values
        bars = VGroup(
            tex(r"$\mathcal R$", size=26, color=EXACT).move_to([x0 + 0.2, y_r, 0]),
            stacked(r_sv, EXACT, y_r),
            tex(rf"${R_NORMS['trace']:.3f}$", size=26, color=EXACT).move_to([x0 + 0.75 + unit * R_NORMS["trace"], y_r, 0], aligned_edge=LEFT),
            tex(r"$W$", size=26, color=TRIAL).move_to([x0 + 0.2, y_w, 0]),
            stacked(w_sv, TRIAL, y_w),
            tex(rf"${W_NORMS['trace']:.3f}$", size=26, color=TRIAL).move_to([x0 + 0.75 + unit * W_NORMS["trace"], y_w, 0], aligned_edge=LEFT),
        )
        bars_title = tex(r"trace norm $=$ all chords laid end to end", size=24, color=MUTED).move_to(
            [x0, y_r + 0.45, 0], aligned_edge=LEFT
        )

        self.say(
            "The trace norm adds up all the singular values: lay every chord end to end. The direct "
            "rotation has four chords of 0.765; the competitor has two of 1.414 and two of zero. "
            "The competitor's total is shorter."
        )
        self.play(FadeIn(bars_title), FadeIn(bars, lag_ratio=0.15))

        rows = [
            (r"largest chord (operator)", "op", False),
            (r"root sum of squares (Frobenius)", "fro", False),
            (r"sum of chords (trace)", "trace", True),
        ]
        body = r"\renewcommand{\arraystretch}{1.3}\begin{array}{l|cc|c}"
        body += r"\norm{I-\,\cdot\,} & \cx{exact}{\mathcal R} & \cx{trial}{W} & \text{less motion}\\ \hline"
        for label, key, flip in rows:
            winner = r"\cx{trial}{W}" if W_NORMS[key] < R_NORMS[key] else r"\cx{exact}{\mathcal R}"
            body += rf"\text{{{label}}} & {R_NORMS[key]:.3f} & {W_NORMS[key]:.3f} & {winner}\\"
        body += r"\end{array}"
        table = math(body, size=24)
        table.move_to([x0, y_w - 0.35, 0], aligned_edge=UP + LEFT)
        if table.get_right()[0] > 6.85:
            table.scale((6.85 - x0) / (table.get_right()[0] - x0), about_edge=LEFT)
        hl = Rectangle(width=table.width + 0.16, height=0.42, stroke_color=SINE, stroke_width=2).move_to(
            [table.get_center()[0], table.get_bottom()[1] + 0.22, 0]
        )

        self.say(
            "In the operator and Frobenius norms the direct rotation still wins. In the trace norm the "
            "competitor moves space less. The angles are 45 degrees, below the pi over 3 threshold, so "
            "Proposition 4.4 as printed is false."
        )
        self.play(FadeIn(table), Create(hl))

        lean = VGroup(
            tex(r"In Lean (standard axioms only): \texttt{proposition4\_4\_refuted}, and the repair "
                r"\texttt{directRotation\_fullDisplacement\_qnorm}:", size=20, color=MUTED),
            para(
                r"for every $Q$-norm (e.g.\ operator, Frobenius) the direct rotation \emph{does} minimize "
                r"$\norm{I-W}$ for acute pairs, with no $\pi/3$ threshold, over $\mathbb{R}$ or $\mathbb{C}$.",
                width=w,
                size=21,
                color=FG,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08)
        lean.move_to([x0, table.get_bottom()[1] - 0.18, 0], aligned_edge=UP + LEFT)
        for m in lean:
            if m.get_right()[0] > 6.85:
                m.scale((6.85 - x0) / (m.get_right()[0] - x0), about_edge=LEFT)

        self.say(
            "We proved the refutation in Lean, and a repair: for Q-norms, which include the operator "
            "and Frobenius norms, the direct rotation really is optimal. The repair removes the printed "
            "60-degree cutoff completely; the usual acuteness condition, under which the direct rotation is "
            "defined, remains."
        )
        self.play(FadeIn(lean))


# ----------------------------------------------------------------------------
# Why, and details
# ----------------------------------------------------------------------------


class P03Why(P4Slide):
    title = "Why the trace norm prefers the competitor"
    kicker = r"Chord length is concave in the angle; squared chord length is not"
    depth = "*"

    def body(self) -> None:
        axes = Axes(
            x_range=[0, 180, 45],
            y_range=[0, 2.1, 0.5],
            x_length=6.2,
            y_length=4.2,
            tips=False,
            axis_config={"color": MUTED, "stroke_width": 2},
        ).move_to([-3.4, -0.55, 0])
        xt = VGroup(*[tex(rf"${v}^\circ$", size=20, color=MUTED).next_to(axes.c2p(v, 0), DOWN, buff=0.1) for v in (45, 90, 135, 180)])
        yt = VGroup(*[tex(rf"${v:g}$", size=20, color=MUTED).next_to(axes.c2p(0, v), LEFT, buff=0.1) for v in (0.5, 1.0, 1.5, 2.0)])
        f = axes.plot(lambda a: chord(np.radians(a)), x_range=[0, 180], color=SINE, stroke_width=4)
        f_lbl = math(r"2\sin(\alpha/2)", size=26, color=SINE).next_to(axes.c2p(150, chord(np.radians(150))), UP, buff=0.1)
        x_lbl = math(r"\alpha", size=26, color=MUTED).next_to(axes.x_axis, RIGHT, buff=0.1)

        c45, c90 = chord(np.pi / 4), chord(np.pi / 2)
        pts = VGroup(
            Dot(axes.c2p(0, 0), color=TRIAL),
            Dot(axes.c2p(90, c90), color=TRIAL),
            Dot(axes.c2p(45, c45), color=EXACT),
        )
        secant = DashedLine(axes.c2p(0, 0), axes.c2p(90, c90), color=TRIAL, stroke_width=3)
        mid = Dot(axes.c2p(45, c90 / 2), color=TRIAL, radius=0.06)
        gap_line = Line(axes.c2p(45, c90 / 2), axes.c2p(45, c45), color=FG, stroke_width=3)

        x0, w = 0.35, 6.4
        t1 = para(
            rf"At the level of invariant planes, the direct rotation spreads the turn as $45^\circ+45^\circ$; "
            rf"the competitor concentrates it as $90^\circ+0^\circ$. Each plane contributes its chord twice, "
            rf"so drop that common factor and compare $2\times{c45:.3f}={2 * c45:.3f}$ with ${c90:.3f}+0$.",
            width=w,
            size=26,
        )
        t2 = para(
            r"Because the chord is \emph{concave} in the angle (it lies above the dashed secant), splitting "
            r"a turn evenly costs more than concentrating it. A norm that \emph{adds} chords, like the "
            r"trace norm, rewards the competitor.",
            width=w,
            size=26,
        )
        t3 = para(
            rf"Squared chords $4\sin^2(\alpha/2)=2(1-\cos\alpha)$ are convex here: "
            rf"$2\times{c45**2:.3f}<{c90**2:.3f}+0$. For a $Q$-norm, squaring the norm turns the comparison "
            r"into a unitarily invariant norm of the squared displacement $(I-W)^{*}(I-W)$, which rewards "
            r"spreading; that is why the repair holds. Its Lean proof goes through the paper's "
            r"squared-displacement result (Proposition 4.3).",
            width=w,
            size=24,
            color=MUTED,
        )
        col = VGroup(t1, t2, t3).arrange(DOWN, aligned_edge=LEFT, buff=0.35)
        col.move_to([x0, self.content_top - 0.2, 0], aligned_edge=UP + LEFT)

        self.say(
            "Why does this happen? Each rotated plane contributes chord lengths 2 sin of half the angle. "
            "Each plane contributes its chord twice, so compare plane by plane: the direct rotation turns "
            "45 and 45 degrees, the competitor 90 and 0."
        )
        self.play(Create(axes), FadeIn(xt, yt, x_lbl), Create(f), FadeIn(f_lbl), FadeIn(pts), FadeIn(t1))
        self.say(
            "The chord is concave: the secant from 0 to 90 degrees lies below the curve, so its midpoint is "
            "below the 45-degree chord. Splitting evenly costs more. Adding chords rewards concentration."
        )
        self.play(Create(secant), FadeIn(mid), Create(gap_line), FadeIn(t2))
        self.say(
            "Squared chords behave the other way. For a Q-norm, squaring the norm turns the comparison into one "
            "about the squared displacement, so the direct rotation wins. That is the repair we proved."
        )
        self.play(FadeIn(t3))


class P04Details(P4Slide):
    title = r"The $\mathbb{R}^4$ witness, explicitly"
    kicker = r"$U=\langle e_0,e_1\rangle$, $\ V=W(U)$; both principal angles $\pi/4$"
    depth = "**"

    def body(self) -> None:
        W = math(
            r"W=\tfrac12\begin{pmatrix}1&-1&-1&-1\\1&1&1&-1\\-1&-1&1&-1\\1&-1&1&1\end{pmatrix}",
            size=34,
        )
        R = math(
            r"\mathcal R=\tfrac1{\sqrt2}\begin{pmatrix}1&0&0&-1\\0&1&1&0\\0&-1&1&0\\1&0&0&1\end{pmatrix}",
            size=34,
        )
        mats = VGroup(R, W).arrange(RIGHT, buff=0.9).move_to([-2.3, self.content_top - 1.35, 0])
        pa = MODEL.principal_angles_degrees
        facts = VGroup(
            math(
                rf"\text{{principal angles}}(U,V)=({pa[0]:.0f}^\circ,{pa[1]:.0f}^\circ)\le60^\circ,\qquad W(U)=\mathcal R(U)=V",
                size=28,
            ),
            math(
                rf"\sigma(I-\mathcal R)=({chord(np.pi / 4):.3f})^{{\times4}},\qquad \sigma(I-W)=({chord(np.pi / 2):.3f},{chord(np.pi / 2):.3f},0,0)",
                size=28,
            ),
            math(
                rf"\norm{{I-W}}_{{*}}=2\sqrt2={W_NORMS['trace']:.4f}\ <\ 4\sqrt{{2-\sqrt2}}={R_NORMS['trace']:.4f}=\norm{{I-\mathcal R}}_{{*}}",
                size=30,
                color=FG,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.25)
        facts.next_to(mats, DOWN, buff=0.4).align_to(mats, LEFT)
        lean = VGroup(
            mono("TauCeti.DavisKahan1970.proposition4_4_printedStatement   -- the claim, as a Prop", size=13),
            mono("TauCeti.DavisKahan1970.proposition4_4_refuted            -- ¬ printed statement", size=13),
            mono("TauCeti.DavisKahan1970.proposition4_4_refutingPair       -- this witness", size=13),
            mono("TauCeti.DavisKahan.FiniteDimensional.directRotation_fullDisplacement_qnorm  -- the repair", size=13),
            mono("TauCeti.DavisKahan.FiniteDimensional.kyFan_not_isQNorm  -- the trace norm on R^4 is not a Q-norm", size=13),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.1)
        lean.next_to(facts, DOWN, buff=0.35).align_to(mats, LEFT)
        if lean.get_right()[0] > 6.8:
            lean.scale((6.8 - lean.get_left()[0]) / lean.width, about_edge=LEFT)
        page = VGroup(mats, facts, lean).arrange(DOWN, aligned_edge=LEFT, buff=0.35)
        page.move_to([-6.45, self.content_top - 0.25, 0], aligned_edge=UP + LEFT)
        floor = -3.35
        if page.get_bottom()[1] < floor:
            page.scale((page.get_top()[1] - floor) / page.height, about_edge=UP + LEFT)
        bg = Rectangle(width=lean.width + 0.3, height=lean.height + 0.25, fill_color=PANEL, fill_opacity=1, stroke_width=0).move_to(lean)

        self.say(
            "For the record: the explicit matrices, the angles, the singular values, and the Lean "
            "declarations. The same model drives the VTK four-plane explorer."
        )
        self.play(FadeIn(mats), FadeIn(facts))
        self.play(FadeIn(bg), FadeIn(lean))


SCENES = [P01Claim, P02Counterexample, P03Why, P04Details]
