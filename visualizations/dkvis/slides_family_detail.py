"""Slides: teaching the tan Theta, sin 2Theta and tan 2Theta theorems.

Full deck, part 3.  Each theorem has a one-slide summary in
:mod:`dkvis.slides_family`; these slides follow it and explain what the theorem
buys and why it holds.  The arguments follow Davis and Kahan's own proofs
(Sections 6--8 of the 1970 paper; see
``ForMathlib/prose/non-distributable/davis-kahan-1970-modernized-transcription.tex``):

* tan Theta: equation (6.6) along paired principal vectors, and Example 6.1;
* sin 2Theta: the symmetric perturbation ``A + Sigma H Sigma`` (Davis and Kahan's ``A + XHX``) and (7.5);
* tan 2Theta: equation (7.6), which "imitates the tan theta proof";
* Theorems 8.1 and 8.2: branch selection and eigenvalue repulsion.

Every number comes from the checked models in :mod:`dkvis.sine_theta_story`.
"""

from __future__ import annotations

import math as pymath

import numpy as np
from manim import (
    DOWN,
    LEFT,
    RIGHT,
    UP,
    Axes,
    Circle,
    Create,
    DashedLine,
    DashedVMobject,
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

from dkvis import sine_theta_story as story
from dkvis.notation import concept_color
from dkvis.slide_style import (
    CURRENT,
    FG,
    GAP,
    MUTED,
    OLD,
    PANEL,
    RESID,
    SINE,
    TRIAL,
    UNWANTED,
    WANTED,
    DeckSlide,
    boxed,
    math,
    para,
    tex,
)
from dkvis.slides_family import TEXT_W, axis, gap_mark, text_column
from dkvis.components.common.geometry import Plane, angle_arc, ellipse, through_origin
from dkvis.components.common.readouts import readout_rows

SIZE = 21


def band(X, lo: float, hi: float, color: str, height: float = 0.26, opacity: float = 0.22) -> Rectangle:
    """A translucent band over ``[lo, hi]`` of a number line."""
    a, b = X(lo), X(hi)
    return Rectangle(
        width=max(b[0] - a[0], 0.06), height=height, stroke_width=0, fill_color=color, fill_opacity=opacity
    ).move_to((a + b) / 2)


# ----------------------------------------------------------------------------
# tan Theta, 2/3: what it buys
# ----------------------------------------------------------------------------


class F02bTanBuys(DeckSlide):
    depth = "*"
    title = r"What $\tan\Theta$ buys over $\sin\Theta$"
    kicker = r"The same number $\norm{R}/\delta$ bounds $\sin\theta$ in one theorem and $\tan\theta$ in the other"

    def body(self) -> None:
        axes = Axes(
            x_range=[0, 2.5, 0.5], y_range=[0, 90, 15], x_length=5.6, y_length=3.7, tips=False,
            axis_config={"color": MUTED, "stroke_width": 2},
        ).move_to([-3.45, -0.2, 0])
        x_lbl = math(r"t=\norm{R}/\delta", size=24, color=MUTED).next_to(axes.c2p(2.5, 0), DOWN, buff=0.3).shift(LEFT * 0.4)
        y_lbl = tex(r"largest angle allowed", size=20, color=MUTED).next_to(axes.c2p(0, 90), UP, buff=0.15, aligned_edge=LEFT)
        ticks = VGroup(
            *[math(rf"{v}^\circ", size=19, color=MUTED).next_to(axes.c2p(0, v), LEFT, buff=0.1) for v in (30, 45, 60, 90)],
            *[math(f"{v:g}", size=19, color=MUTED).next_to(axes.c2p(v, 0), DOWN, buff=0.1) for v in (0.5, 1, 1.5, 2)],
        )
        sin_curve = axes.plot(lambda t: pymath.degrees(pymath.asin(min(t, 1.0))), x_range=[0, 1.0, 0.005], color=FG, stroke_width=4)
        sin_none = DashedLine(axes.c2p(1.0, 90), axes.c2p(2.5, 90), color=FG, stroke_width=3, dash_length=0.1)
        tan_curve = axes.plot(lambda t: pymath.degrees(pymath.atan(t)), x_range=[0, 2.5], color=SINE, stroke_width=4)
        sin_lbl = tex(r"$\sin\Theta$ theorem: $\theta\le\arcsin t$", size=20).next_to(axes.c2p(1.0, 72), RIGHT, buff=0.12)
        none_lbl = tex(r"no information", size=19).next_to(axes.c2p(1.75, 90), DOWN, buff=0.1)
        tan_lbl = tex(r"\cx{sine}{$\tan\Theta$ theorem: $\theta\le\arctan t$}", size=20).move_to(axes.c2p(1.85, 40))

        def mark(t: float) -> VGroup:
            ys = [pymath.degrees(pymath.asin(min(t, 1.0))), pymath.degrees(pymath.atan(t))]
            return VGroup(
                DashedLine(axes.c2p(t, 0), axes.c2p(t, 90), color=MUTED, stroke_width=1.5, dash_length=0.06),
                Dot(axes.c2p(t, ys[0]), radius=0.07, color=FG),
                Dot(axes.c2p(t, ys[1]), radius=0.07, color=SINE),
            )

        marks = VGroup(mark(0.5), mark(1.0))

        w = TEXT_W
        p_same = para(
            r"Both theorems turn one computable number, $t=\norm{R}/\delta$, into a bound on the angle: "
            r"$\sin\theta\le t$, or $\tan\theta\le t$ (in the operator norm).",
            width=w, size=SIZE,
        )
        p_small = para(
            r"For small $t$ they agree, since $\sin\theta\approx\tan\theta\approx\theta$. At $t=1/2$: "
            r"$\theta\le30^\circ$ against $\theta\le26.6^\circ$. Davis and Kahan call the improvement slight when all "
            r"angles are small, and possibly important in exceptional applications.",
            width=w, size=SIZE,
        )
        p_large = para(
            r"For $t\ge1$ the $\sin\Theta$ theorem says nothing, while $\tan\Theta$ still gives $\theta\le\arctan t$, "
            r"below $90^\circ$; at $t=1$ it gives $45^\circ$.",
            width=w, size=SIZE,
        )
        p_price = para(
            r"\textbf{The price:} Rayleigh--Ritz trial values ($\sym{H0}=0$) and every unwanted eigenvalue on one side. "
            r"That is the usual situation when an eigensolver computes the lowest (or highest) eigenvalues: whatever "
            r"has not been computed lies above (below).",
            width=w, size=SIZE,
        )
        p_amb = para(
            r"The same estimate on both off-diagonal corners of the rotation gives the ambient form "
            r"$\delta\norm{\tan\Theta}\le\norm{\sym{H}}$.",
            width=w, size=SIZE - 1, color=MUTED,
        )
        col = text_column(p_same, p_small, p_large, p_price, p_amb, top=self.content_top - 0.1)

        self.say(
            "What does tan buy? Both theorems start from the same computable number, the residual over the gap. "
            "One bounds sin theta by it, the other tan theta. Plot the largest angle each one allows."
        )
        self.play(Create(axes), FadeIn(x_lbl, y_lbl, ticks), FadeIn(col[0]))
        self.play(Create(sin_curve), FadeIn(sin_lbl), Create(tan_curve), FadeIn(tan_lbl))

        self.say(
            "For small t they agree: 30 against 26.6 degrees at one half. Davis and Kahan call the gain slight when "
            "the angles are small. Past t equals 1 the sin theorem says nothing, while tan still gives a real bound, "
            "45 degrees at t equals 1."
        )
        self.play(FadeIn(marks), Create(sin_none), FadeIn(none_lbl), FadeIn(col[1]), FadeIn(col[2]))

        self.say(
            "The price is the hypotheses: Rayleigh-Ritz values and all unwanted eigenvalues on one side, which is the "
            "situation of an eigensolver computing the lowest eigenvalues. There is also an ambient form with H."
        )
        self.play(FadeIn(col[3]), FadeIn(col[4]))


# ----------------------------------------------------------------------------
# tan Theta, 3/3: why it holds
# ----------------------------------------------------------------------------


class F02cTanWhy(DeckSlide):
    depth = "*"
    title = r"Why the $\tan\Theta$ theorem holds"
    kicker = r"One equation per pair of principal vectors, and why the gap must be one-sided"

    def body(self) -> None:
        bad = story.TWO_SIDED
        bad.verify()
        top = self.content_top - 0.15

        two = VGroup(
            tex(r"In $2\times2$, with the trial value $a_0$ below the unwanted eigenvalue $\lambda_1$:", size=20, color=MUTED),
            math(
                r"(\sym{A}+\sym{H})\begin{pmatrix}-\sin\theta\\ \cos\theta\end{pmatrix}=\lambda_1\begin{pmatrix}-\sin\theta\\ \cos\theta\end{pmatrix}"
                r"\ \Rightarrow",
                size=26,
            ),
            math(r"\cos\theta\,|\sym{b}|=\sin\theta\,(\lambda_1-a_0)", size=26),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        general = VGroup(
            tex(r"In general, along each pair of principal vectors $x_j$ (trial side), $y_j$ (unwanted side), (6.6):", size=20, color=MUTED),
            math(
                r"\cos\theta_j\,y_j^*\sym{B}x_j=\sin\theta_j\,\bigl(\like{Lambda1}{y_j^*\Lambda_1y_j}-\like{A0}{x_j^*A_0x_j}\bigr)"
                r"\ \ge\ \sym{delta}\sin\theta_j",
                size=26,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        VGroup(two, general).arrange(DOWN, aligned_edge=LEFT, buff=0.35).move_to([-6.85, top, 0], aligned_edge=UP + LEFT)

        # Where the two Rayleigh quotients can lie: one-sided and two-sided.
        nl1, X1 = axis(-1.4, 2.8, -6.3, -0.9, -1.75)
        one_sided = VGroup(
            nl1,
            band(X1, 0.1, 0.5, TRIAL),
            band(X1, 1.4, 2.5, UNWANTED, opacity=0.16),
            *[Dot(X1(t), radius=0.07, color=TRIAL) for t in (0.1, 0.5)],
            *[Dot(X1(t), radius=0.07, color=UNWANTED) for t in (1.4, 1.9, 2.5)],
            math(r"\like{A0}{x^*A_0x}", size=19).next_to(X1(0.3), DOWN, buff=0.2),
            math(r"\like{Lambda1}{y^*\Lambda_1y}", size=19).next_to(X1(1.95), DOWN, buff=0.2),
            gap_mark(X1(0.5) + UP * 0.2, X1(1.4) + UP * 0.2, r"$\ge\delta$", size=19),
            tex(r"one-sided", size=19, color=MUTED).next_to(X1(2.8), RIGHT, buff=0.12),
        )
        nl2, X2 = axis(-1.4, 2.8, -6.3, -0.9, -2.95)
        two_sided = VGroup(
            nl2,
            band(X2, -1.0, 1.0, UNWANTED, opacity=0.16),
            Dot(X2(-1.0), radius=0.07, color=UNWANTED),
            Dot(X2(1.0), radius=0.07, color=UNWANTED),
            Dot(X2(0.0), radius=0.08, color=TRIAL),
            math(r"\like{A0}{x^*A_0x}=0=\like{Lambda1}{y^*\Lambda_1y}", size=19).next_to(X2(0.0), DOWN, buff=0.2),
            math(r"-1", size=18, color=concept_color("Lambda1")).next_to(X2(-1.0), UP, buff=0.12),
            math(r"1", size=18, color=concept_color("Lambda1")).next_to(X2(1.0), UP, buff=0.12),
            tex(r"two-sided", size=19, color=MUTED).next_to(X2(2.8), RIGHT, buff=0.12),
        )

        w = TEXT_W
        p_two = para(
            r"In $2\times2$, the unwanted eigenvector's first entry gives the identity on the left: $\tan\theta$ is the "
            r"coupling over the gap from the trial value to the unwanted eigenvalue.",
            width=w, size=SIZE,
        )
        p_gen = para(
            r"In general, Davis and Kahan read the same entry along each pair of principal vectors. "
            r"$\like{A0}{x^*A_0x}$ and $\like{Lambda1}{y^*\Lambda_1y}$ are Rayleigh quotients: weighted averages of eigenvalues.",
            width=w, size=SIZE,
        )
        p_one = para(
            r"\textbf{One-sided:} every average of $\sym{A0}$ is at most $\alpha$ and every average of $\sym{Lambda1}$ at least "
            r"$\alpha+\delta$, so $\cos\theta_j|y_j^*\sym{B}x_j|\ge\delta\sin\theta_j$. Then $\cos\theta_j>0$ and "
            r"$\tan\theta_j\le|y_j^*\sym{B}x_j|/\delta\le\norm{R}/\delta$ (with $\sym{H0}=0$, $\norm{R}=\norm{\sym{B}}$). Summing over "
            r"pairs (Ky Fan) gives every unitarily invariant norm.",
            width=w, size=SIZE,
        )
        p_two_sided = para(
            r"\textbf{Two-sided:} an average of unwanted eigenvalues below and above can equal the trial value, and the "
            rf"equation bounds nothing. In $\operatorname{{diag}}(-1,0,1)$ the direction $y=(e_3-e_1)/\sqrt2$ averages $-1$ "
            rf"and $1$ to $0$; at $45^\circ$, $\delta\tan\theta=1>{bad.residual_norm:.3f}=\norm{{R}}$ (Davis and Kahan's "
            r"Example 6.1 has these numbers).",
            width=w, size=SIZE,
        )
        p_sin = para(
            r"The $\sin\Theta$ argument (``Why it is true'') weighs each unwanted eigendirection separately, so the two "
            r"sides cannot cancel there.",
            width=w, size=SIZE - 1, color=MUTED,
        )
        col = text_column(p_two, p_gen, p_one, p_two_sided, p_sin, top=self.content_top - 0.1, buff=0.2)

        self.say(
            "Why does tan Theta hold? In two dimensions it is one entry of the eigenvector equation: cos theta times "
            "the coupling equals sin theta times the gap between the trial value and the unwanted eigenvalue."
        )
        self.play(FadeIn(two), FadeIn(col[0]))

        self.say(
            "Davis and Kahan read the same entry along each pair of principal vectors. Eigenvalues become Rayleigh "
            "quotients, averages of eigenvalues. With a one-sided gap the two averages are always at least delta apart, "
            "which gives tan theta at most the residual over delta for each pair, and Ky Fan sums do the rest."
        )
        self.play(FadeIn(general), FadeIn(col[1]))
        self.play(FadeIn(one_sided), FadeIn(col[2]))

        self.say(
            "Two-sided, the average of unwanted eigenvalues below and above can land right on the trial value, and the "
            "equation bounds nothing. That is the counterexample: minus 1 and plus 1 average to 0. The sin Theta proof "
            "never averages, which is why it allows both sides."
        )
        self.play(FadeIn(two_sided), FadeIn(col[3]), FadeIn(col[4]))


# ----------------------------------------------------------------------------
# sin 2Theta, 2/3: reflect
# ----------------------------------------------------------------------------


class F03bReflect(DeckSlide):
    depth = "*"
    title = r"Why the angle doubles: reflect the coupling"
    kicker = r"Davis and Kahan regard $\sym{A}+\sym{H}$ as a perturbation not of $\sym{A}$, but of $\sym{A}+\Sigma \sym{H}\Sigma$"

    def body(self) -> None:
        eps = story.PERTURBATION_EPS
        pair = story.PerturbedPair(gap=story.REFLECT_EXAMPLE_GAP, eps=eps)
        pair.verify()
        th = pair.line_angle
        l0, l1 = pair.perturbed_eigenvalues
        plane = Plane([-4.3, 0.15, 0], 1.2)
        reach = 2.15

        mirror = through_origin(plane, [1.0, 0.0], reach, TRIAL, width=3)
        mirror_lbl = tex(r"$V$, the mirror", size=20, color=concept_color("V")).next_to(plane([-reach, 0.0]), DOWN, buff=0.1).shift(RIGHT * 0.5)
        perp = DashedVMobject(through_origin(plane, [0.0, 1.0], 1.6, TRIAL, width=2), num_dashes=18)

        new = VGroup(
            ellipse(plane, pair.perturbed, color=CURRENT, width=3),
            through_origin(plane, story.unit(th), reach, WANTED, width=3.5),
        )
        new_lbl = tex(r"$\sym{A}+\sym{H}$", size=22, color=FG).next_to(plane(reach * story.unit(th)), RIGHT, buff=0.08)
        reflected = VGroup(
            DashedVMobject(ellipse(plane, pair.reflected, color=FG, width=3), num_dashes=56),
            through_origin(plane, story.unit(-th), reach, FG, width=3.5),
        )
        refl_lbl = tex(r"$\sym{A}+\Sigma \sym{H}\Sigma$", size=22, color=FG).next_to(plane(reach * story.unit(-th)), RIGHT, buff=0.08)
        arc = angle_arc(plane, story.unit(-th), story.unit(th), 1.35, SINE, width=4)
        arc_lbl = math(r"2\theta", size=28, color=concept_color("theta")).move_to(plane.origin + RIGHT * 0.95)

        mats = VGroup(
            math(r"\sym{A}+\sym{H}=\begin{pmatrix}a_0&\sym{b}\\ \sym{b}&a_1\end{pmatrix}", size=26, color=FG),
            math(r"\sym{A}+\Sigma \sym{H}\Sigma=\begin{pmatrix}a_0&-\sym{b}\\ -\sym{b}&a_1\end{pmatrix}", size=26),
        ).arrange(RIGHT, buff=0.5).move_to([-4.0, -2.65, 0])
        same = tex(rf"same eigenvalues ${l0:.2f}$ and ${l1:.2f}$; the eigenvectors are mirror images", size=19, color=MUTED).next_to(mats, DOWN, buff=0.12)

        w = TEXT_W
        p_x = para(
            r"$\Sigma=P-P^\perp$ is $+1$ on the old (trial) subspace $V$ and $-1$ on $V^\perp$: a mirror. Since "
            r"$\Sigma \sym{A}\Sigma=\sym{A}$, "
            r"$\sym{A}+\Sigma \sym{H}\Sigma=\Sigma(\sym{A}+\sym{H})\Sigma$ is $\sym{A}+\sym{H}$ seen in the mirror. In $\sym{A}$'s eigenbasis only the coupling block $\sym{B}$ changes sign.",
            width=w, size=SIZE,
        )
        p_same = para(
            r"So $\sym{A}+\Sigma \sym{H}\Sigma$ has the same eigenvalues as $\sym{A}+\sym{H}$, and mirror-image eigenvectors, at $\theta$ and $-\theta$: "
            r"$2\theta$ apart. In general, with $\mathcal R$ the direct rotation from $V$ to $U$, "
            r"$(\sym{A}+\sym{H})\mathcal R^2=\mathcal R^2(\sym{A}+\Sigma \sym{H}\Sigma)$, and $\mathcal R^2$ turns by $2\Theta$ (7.3--7.4).",
            width=w, size=SIZE,
        )
        p_apply = para(
            r"Now apply the two-gap $\sin\Theta$ theorem (Proposition 6.1) to this pair. Both matrices have the spectral "
            r"split $\sym{Lambda0}\,|\,\sym{Lambda1}$ with gap $\delta$, and they differ by $\sym{H}-\Sigma \sym{H}\Sigma$, the coupling twice:",
            width=w, size=SIZE,
        )
        box = boxed(
            math(r"\sym{delta}\norm{\like{theta}{\sin2\Theta}}\le\norm{\sym{H}-\Sigma \sym{H}\Sigma}\le2\norm{\sym{H}}", size=30), color=SINE, pad=0.15
        )
        p_two = para(
            r"In $2\times2$: $\norm{\sym{H}-\Sigma \sym{H}\Sigma}=2|\sym{b}|$ and the gap is $\lambda_0-\lambda_1$, so $\sin2\theta=2\sym{b}/(\lambda_0-\lambda_1)$ exactly. "
            r"For the directed form Section 7 obtains $\delta\norm{\sin2\Theta_0}\le\norm{\sym{B}}\le\norm{R}$; Section 2 prints "
            r"the weaker $2\norm{R}$.",
            width=w, size=SIZE - 1, color=MUTED,
        )
        col = text_column(p_x, p_same, p_apply, box, p_two, top=self.content_top - 0.1)

        self.say(
            "Why does the double angle appear, and why the gap of A plus H? Davis and Kahan's idea: reflect. Sigma is the "
            "mirror that fixes the old subspace and flips its complement. A plus Sigma H Sigma is A plus H seen in that mirror: "
            "only the coupling changes sign."
        )
        self.play(Create(mirror), Create(perp), FadeIn(mirror_lbl), Create(new), FadeIn(new_lbl), FadeIn(col[0]))

        self.say(
            "Watch the mirror image. Same eigenvalues, so the same ellipse shape, but the eigenvector is now at minus "
            "theta. The two matrices' eigenvectors are 2 theta apart."
        )
        ghost = new.copy()
        self.play(Transform(ghost, reflected), run_time=2.0)
        self.remove(ghost)
        self.add(reflected)
        self.play(FadeIn(refl_lbl), Create(arc), FadeIn(arc_lbl), FadeIn(mats, same), FadeIn(col[1]))

        self.say(
            "So treat A plus H as a perturbation of its own mirror image. The sin Theta theorem with two gaps applies, "
            "with the gap inside A plus H, and the angle it bounds is 2 Theta. The perturbation is the coupling twice, "
            "which is where the factor 2 comes from."
        )
        self.play(FadeIn(col[2]), FadeIn(col[3]), FadeIn(col[4]))


# ----------------------------------------------------------------------------
# sin 2Theta, 3/3: the price of doubling
# ----------------------------------------------------------------------------


class F03cPrice(DeckSlide):
    depth = "*"
    title = r"The price of doubling the angle"
    kicker = r"A bound on $\sin2\theta$ allows small angles, and also angles near $90^\circ$"

    def body(self) -> None:
        t = story.SIN2_PRICE_BOUND
        small = pymath.degrees(0.5 * pymath.asin(t))
        axes = Axes(
            x_range=[0, 90, 15], y_range=[0, 1, 0.25], x_length=5.8, y_length=3.4, tips=False,
            axis_config={"color": MUTED, "stroke_width": 2},
        ).move_to([-3.4, -0.1, 0])
        x_lbl = math(r"\theta", size=26, color=MUTED).next_to(axes.c2p(90, 0), RIGHT, buff=0.15)
        ticks = VGroup(
            *[math(rf"{v}^\circ", size=19, color=MUTED).next_to(axes.c2p(v, 0), DOWN, buff=0.1) for v in (0, 45, 90)],
            *[math(f"{v:g}", size=19, color=MUTED).next_to(axes.c2p(0, v), LEFT, buff=0.1) for v in (0.5, 1)],
        )
        curve = axes.plot(lambda d: pymath.sin(2 * pymath.radians(d)), x_range=[0, 90, 0.5], color=SINE, stroke_width=4)
        curve_lbl = math(r"\sin2\theta", size=24, color=concept_color("theta")).next_to(axes.c2p(45, 1), UP, buff=0.1)
        bound = DashedLine(axes.c2p(0, t), axes.c2p(90, t), color=RESID, stroke_width=3, dash_length=0.1)
        bound_lbl = tex(rf"\cx{{resid}}{{bound $t={t:g}$}}", size=20).next_to(axes.c2p(90, t), UP, buff=0.08).shift(LEFT * 0.4)

        def shade(d0: float, d1: float) -> Rectangle:
            a, b = axes.c2p(d0, 0), axes.c2p(d1, 1)
            return Rectangle(width=b[0] - a[0], height=b[1] - a[1], stroke_width=0, fill_color=FG, fill_opacity=0.08).move_to((a + b) / 2)

        allowed = VGroup(shade(0, small), shade(90 - small, 90))
        allowed_lbls = VGroup(
            tex(r"allowed", size=19, color=FG).move_to(axes.c2p(small / 2, 0.12)),
            tex(r"allowed", size=19, color=FG).move_to(axes.c2p(90 - small / 2, 0.12)),
            tex(r"excluded", size=19, color=MUTED).move_to(axes.c2p(45, 0.3)),
        )
        cut = VGroup(
            Dot(axes.c2p(small, t), radius=0.07, color=FG),
            Dot(axes.c2p(90 - small, t), radius=0.07, color=FG),
            math(rf"{small:.1f}^\circ", size=19).next_to(axes.c2p(small, t), UP + RIGHT * 0.3, buff=0.08),
            math(rf"{90 - small:.1f}^\circ", size=19).next_to(axes.c2p(90 - small, t), UP + LEFT * 0.3, buff=0.08),
        )

        w = TEXT_W
        p_sym = para(
            r"$\sin2\theta$ is symmetric about $45^\circ$. A bound $\sin2\theta\le t$ allows "
            r"$\theta\le\tfrac12\arcsin t$, but equally $\theta\ge90^\circ-\tfrac12\arcsin t$. Here $t=0.6$: "
            rf"$\theta\le{small:.1f}^\circ$ or $\theta\ge{90 - small:.1f}^\circ$.",
            width=w, size=SIZE,
        )
        p_which = para(
            r"Which one occurs depends on the invariant subspace $F_0$ of $\sym{A}+\sym{H}$ being compared. The theorem accepts any "
            r"subspace with the spectral split $\sym{Lambda0}\,|\,\sym{Lambda1}$; it does not require the ``right'' one, belonging "
            r"to eigenvalues near those of $\sym{A0}$. Even with $\sym{H}=0$ a mismatched $F_0$ can be $90^\circ$ away, and "
            r"different angles of $\Theta_0$ can fall on different sides.",
            width=w, size=SIZE,
        )
        p_82 = para(
            r"\textbf{Theorem 8.2} removes the ambiguity: if also $\norm{\sym{H}}_2<\delta/2$ (or $\norm{R}_2<\delta/2$) and "
            r"$\operatorname{spec}\sym{A0}\subset[\beta-\delta/2,\alpha+\delta/2]$, every angle is below $45^\circ$, so "
            r"$\theta\le\tfrac12\arcsin(2\norm{\sym{H}}_2/\delta)$.",
            width=w, size=SIZE,
        )
        p_proof = para(
            r"Its proof follows the path $\sym{A}+\sym{H}-\sigma \sym{H}$ from $\sym{A}+\sym{H}$ ($\sigma=0$) back to $\sym{A}$ ($\sigma=1$) and uses the "
            r"$\sin2\Theta$ bound along the way: the angle starts at $0$ and can never jump past $45^\circ$.",
            width=w, size=SIZE - 1, color=MUTED,
        )
        col = text_column(p_sym, p_which, p_82, p_proof, top=self.content_top - 0.1)

        self.say(
            "The price of doubling. sin 2 theta rises to 45 degrees and falls back. So a bound on it allows two ranges: "
            "small angles, and angles near 90 degrees."
        )
        self.play(Create(axes), FadeIn(x_lbl, ticks), Create(curve), FadeIn(curve_lbl))
        self.play(Create(bound), FadeIn(bound_lbl), FadeIn(allowed, allowed_lbls, cut), FadeIn(col[0]))

        self.say(
            "Which range you are in depends on which invariant subspace of A plus H you compare with, and the theorem "
            "lets you pick any with the right spectral split. Theorem 8.2 adds a smallness condition that forces the "
            "small branch; its proof follows the path from A plus H back to A and shows the angle never jumps past 45."
        )
        self.play(FadeIn(col[1]), FadeIn(col[2]), FadeIn(col[3]))


# ----------------------------------------------------------------------------
# tan 2Theta, 2/3: the Jacobi equation
# ----------------------------------------------------------------------------


class F04bJacobi(DeckSlide):
    depth = "*"
    title = r"Why the $\tan2\Theta$ theorem holds: the Jacobi equation"
    kicker = r"Turn the old eigenbasis until the coupling vanishes; the proof does this pair by pair"

    def body(self) -> None:
        eps = story.PERTURBATION_EPS
        pair = story.PerturbedPair(gap=story.REFLECT_EXAMPLE_GAP, eps=eps)
        pair.verify()
        th = pair.line_angle
        phi = ValueTracker(0.0)
        plane = Plane([-4.3, 0.25, 0], 1.2)
        reach = 2.1

        ell = ellipse(plane, pair.perturbed, color=CURRENT, width=3)
        old_axes = VGroup(
            DashedVMobject(through_origin(plane, [1.0, 0.0], reach, OLD, width=2), num_dashes=24),
            DashedVMobject(through_origin(plane, [0.0, 1.0], 1.7, OLD, width=2), num_dashes=20),
        )
        frame = always_redraw(
            lambda: VGroup(
                through_origin(plane, story.unit(phi.get_value()), reach, TRIAL, width=4),
                through_origin(plane, story.unit(phi.get_value() + np.pi / 2), 1.7, TRIAL, width=4),
            )
        )
        arc = always_redraw(lambda: angle_arc(plane, [1.0, 0.0], story.unit(max(phi.get_value(), 1e-3)), 1.0, SINE, width=4))
        key = VGroup(
            tex(r"\cx{current}{ellipse: $\sym{Ahat}$}", size=19),
            tex(r"\cx{trial}{the basis, turned by $\varphi$}", size=19),
            tex(r"\cx{old}{dashed: $\sym{A}$'s eigenbasis}", size=19),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.05).move_to([-6.9, 2.35, 0], aligned_edge=UP + LEFT)
        formula = math(
            r"\text{coupling}(\varphi)=\tfrac12(a_1-a_0)\sin2\varphi+\sym{b}\cos2\varphi",
            size=24,
        ).move_to([-4.0, -2.3, 0])
        rows = readout_rows(
            [
                (r"\varphi =", lambda: pymath.degrees(phi.get_value()), SINE, 1, r"^\circ"),
                (r"\text{coupling} =", lambda: pair.coupling(phi.get_value()), FG, 3, None),
            ],
            size=24,
        ).move_to([-4.0, -3.0, 0])

        w = TEXT_W
        p_turn = para(
            r"Write $\sym{A}+\sym{H}$ in $\sym{A}$'s eigenbasis turned by $\varphi$. Its off-diagonal (coupling) entry is "
            r"$\tfrac12(a_1-a_0)\sin2\varphi+\sym{b}\cos2\varphi$. The eigenvectors of $\sym{A}+\sym{H}$ are the basis where it "
            r"vanishes: $\tan2\theta=2\sym{b}/(a_0-a_1)$, the Jacobi rotation.",
            width=w, size=SIZE,
        )
        p_pair = para(
            r"Davis and Kahan's proof ``imitates the $\tan\theta$ proof'': it reads $F_0^*(\sym{A}+\sym{H})F_1=0$ along each pair "
            r"of principal vectors $x_j$, $y_j$ (7.6). Because $\sym{H0}=\sym{H1}=0$, the diagonal entries are Rayleigh "
            r"quotients of $\sym{A}$ itself, at least $\delta$ apart by the one-sided gap:",
            width=w, size=SIZE,
        )
        ineq = math(
            r"\pm2\cos2\theta_j\,\operatorname{Re}(y_j^*\sym{B}x_j)\ \ge\ \sym{delta}\sin2\theta_j",
            size=30,
        )
        p_concl = para(
            r"So $\cos2\theta_j\neq0$ (no angle equals $45^\circ$: a conclusion, not a hypothesis), and "
            r"$\delta|\tan2\theta_j|\le2|y_j^*\sym{B}x_j|\le2\norm{\sym{B}}=2\norm{R}$. Ky Fan sums give every unitarily invariant norm.",
            width=w, size=SIZE,
        )
        p_why = para(
            r"Without $\sym{H0}=\sym{H1}=0$ the diagonal blocks would be $\sym{A0}+\sym{H0}$ and $A_1+\sym{H1}$, whose gap $\sym{A}$'s gap does not "
            r"control. Without one-sidedness the two Rayleigh quotients could average to the same value, as for $\tan\Theta$.",
            width=w, size=SIZE - 1, color=MUTED,
        )
        col = text_column(p_turn, p_pair, ineq, p_concl, p_why, top=self.content_top - 0.1)

        self.say(
            "Why tan 2 Theta? In two dimensions it is Jacobi's method. Take A's eigenbasis and turn it. The coupling "
            "entry of A plus H in the turned basis starts at b and changes as you turn."
        )
        self.add(frame, arc)
        self.play(Create(ell), FadeIn(old_axes, key), FadeIn(frame), FadeIn(formula, rows), FadeIn(col[0]))

        self.say(
            "It vanishes exactly when the basis lines up with the ellipse's axes, the eigenvectors of A plus H. Setting "
            "it to zero is tan 2 theta equals 2b over the old gap."
        )
        self.play(phi.animate.set_value(th), run_time=4.0, rate_func=rate_functions.ease_in_out_sine)

        self.say(
            "Davis and Kahan do the same along each pair of principal vectors. With no diagonal perturbation, the "
            "diagonal entries are Rayleigh quotients of A itself, a gap delta apart. That forces cos 2 theta to be "
            "nonzero and bounds tan 2 theta by twice the coupling over delta."
        )
        self.play(FadeIn(col[1]), FadeIn(col[2]), FadeIn(col[3]), FadeIn(col[4]))


# ----------------------------------------------------------------------------
# tan 2Theta, 3/3: turning costs eigenvalue motion
# ----------------------------------------------------------------------------


class F04cRepulsion(DeckSlide):
    depth = "*"
    title = r"Turning eigenvectors pushes eigenvalues apart"
    kicker = r"Theorem 8.1: the matching subspace, the $45^\circ$ ceiling, and spectral repulsion"

    def body(self) -> None:
        eps = story.PERTURBATION_EPS
        g = ValueTracker(story.PERTURBATION_START_GAP)

        def pair() -> story.PerturbedPair:
            return story.PerturbedPair(gap=g.get_value(), eps=eps)

        line_old, X_old = axis(0.85, 2.15, -5.45, -0.9, 1.4)
        line_new, X_new = axis(0.85, 2.15, -5.45, -0.9, 0.2)

        def old_marks():
            a0, a1 = pair().A.diagonal()
            return VGroup(
                Dot(X_old(a0), radius=0.08, color=concept_color("a0")),
                Circle(radius=0.075, color=concept_color("a1"), stroke_width=3).move_to(X_old(a1)),
                math(r"\sym{a0}", size=22).next_to(X_old(a0), UP, buff=0.1).shift(RIGHT * 0.12),
                math(r"\sym{a1}", size=22).next_to(X_old(a1), UP, buff=0.1).shift(LEFT * 0.12),
            )

        def new_marks():
            l0, l1 = pair().perturbed_eigenvalues
            return VGroup(
                Dot(X_new(l0), radius=0.08, color=concept_color("lambda0")),
                Circle(radius=0.075, color=concept_color("lambda1"), stroke_width=3).move_to(X_new(l1)),
                math(r"\sym{lambda0}", size=22).next_to(X_new(l0), DOWN, buff=0.1),
                math(r"\sym{lambda1}", size=22).next_to(X_new(l1), DOWN, buff=0.1),
            )

        lines = VGroup(
            line_old, tex(r"old $\sym{A}$", size=20, color=FG).next_to(X_old(0.85), LEFT, buff=0.12),
            line_new, tex(r"new $\sym{A}+\sym{H}$", size=20, color=FG).next_to(X_new(0.85), LEFT, buff=0.12),
        )
        marks = VGroup(always_redraw(old_marks), always_redraw(new_marks))
        rows = readout_rows(
            [
                (r"\text{old gap } \sym{a0}-\sym{a1} =", lambda: g.get_value(), GAP, 3, None),
                (r"\text{new gap } \sym{lambda0}-\sym{lambda1} =", lambda: pair().delta_sin_two, GAP, 3, None),
                (r"\theta =", lambda: pymath.degrees(pair().line_angle), SINE, 1, r"^\circ"),
                (r"(\sym{lambda0}-\sym{lambda1})\cos2\sym{theta} =", lambda: pair().delta_sin_two * pymath.cos(2 * pair().line_angle), GAP, 3, None),
            ],
            size=24,
        ).move_to([-3.6, -1.85, 0])
        note = tex(rf"$\norm{{H}}_2={eps:g}$ throughout", size=19, color=MUTED).next_to(rows, DOWN, buff=0.2)

        w = TEXT_W
        p_rep = para(
            r"Divide the two double-angle identities: $\lambda_0-\lambda_1=(a_0-a_1)/\cos2\theta$. The more the "
            r"eigenvectors turn, the further the eigenvalues of $\sym{A}+\sym{H}$ are pushed apart: here the old gap shrinks "
            r"towards $0$ while the new gap stays above $2\norm{\sym{H}}_2$.",
            width=w, size=SIZE,
        )
        p_81 = para(
            r"\textbf{Theorem 8.1}, under the $\tan2\Theta$ hypotheses: every angle is at most $45^\circ$ exactly when "
            r"$F_0$ is the matching spectral subspace of $\sym{A}+\sym{H}$ ($\sym{Lambda0}\le\alpha$, $\sym{Lambda1}\ge\alpha+\delta$), "
            r"and that subspace always exists. This is the $45^\circ$ ceiling of the gap slides.",
            width=w, size=SIZE,
        )
        p_ii = para(
            r"For it, eigenvalues repel. In finite dimensions, with $\alpha_k$ and $\lambda_k$ the ordered eigenvalues "
            r"of $A_1$ and $\sym{Lambda1}$, and $\norm{C_1}_1$ the largest cosine of the angles:",
            width=w, size=SIZE,
        )
        ineq = math(r"\alpha_k-\alpha\ \le\ \norm{C_1}_1^2\,(\lambda_k-\alpha)", size=30)
        p_meaning = para(
            r"So an off-diagonal perturbation that turns all eigenvectors a lot (every cosine well below 1) must move "
            r"eigenvalues by a definite amount. Davis and Kahan note this runs opposite to an earlier result: a "
            r"perturbation that changes eigenvectors greatly cannot also change eigenvalues too much.",
            width=w, size=SIZE - 1, color=MUTED,
        )
        col = text_column(p_rep, p_81, p_ii, ineq, p_meaning, top=self.content_top - 0.1)

        self.say(
            "One more consequence of the tan 2 Theta setting. Divide the two double-angle identities: the new gap is "
            "the old gap divided by cos 2 theta. Watch it as the old gap closes with H fixed."
        )
        self.add(marks)
        self.play(FadeIn(lines, marks, rows, note), FadeIn(col[0]))
        self.play(g.animate.set_value(0.05), run_time=6.0, rate_func=rate_functions.ease_in_out_sine)

        self.say(
            "Theorem 8.1 makes this general. On the matching spectral subspace every angle is at most 45 degrees; "
            "that subspace always exists; and eigenvalues repel: a perturbation that turns every eigenvector a lot "
            "must also move the eigenvalues by a definite amount."
        )
        self.play(FadeIn(col[1]), FadeIn(col[2]), FadeIn(col[3]), FadeIn(col[4]))


# ----------------------------------------------------------------------------
# Which theorem when?
# ----------------------------------------------------------------------------


class F09WhichOne(DeckSlide):
    depth = "*"
    title = "Which theorem when?"
    kicker = r"None of the four implies another; each is best possible under its own hypotheses"

    ROWS = [
        (
            r"\sin\Theta",
            r"Trial vectors and any trial matrix; the unwanted eigenvalues of $\sym{A}+\sym{H}$ are outside an interval around the "
            r"trial values, on either side.",
            r"$\norm{\sin\Theta_0}\le\norm{R}/\delta$: residual over spectral separation.",
        ),
        (
            r"\tan\Theta",
            r"As above, with Rayleigh--Ritz trial values and every unwanted eigenvalue on one side (e.g.\ computing "
            r"the lowest eigenvalues).",
            r"$\norm{\tan\Theta_0}\le\norm{R}/\delta$: never $90^\circ$, tighter for large angles; also "
            r"$\norm{\tan\Theta}\le\norm{\sym{H}}/\delta$.",
        ),
        (
            r"\sin2\Theta",
            r"Only that the eigenvalues of $\sym{A}+\sym{H}$ split into $\sym{Lambda0}\,|\,\sym{Lambda1}$ with gap $\delta$; nothing about "
            r"the trial values.",
            r"$\norm{\sin2\Theta}\le2\norm{\sym{H}}/\delta$ (and with $R$): a small angle or one near $90^\circ$, unless "
            r"Theorem 8.2 applies.",
        ),
        (
            r"\tan2\Theta",
            r"Only $\sym{A}$'s spectrum, split on one side by $\delta$, and an $\sym{H}$ that only couples wanted with unwanted "
            r"directions.",
            r"$\norm{\tan2\Theta}\le2\norm{\sym{H}}/\delta$ before computing anything about $\sym{A}+\sym{H}$; at most $45^\circ$ on the "
            r"matching subspace (Theorem 8.1).",
        ),
    ]

    def body(self) -> None:
        top = self.content_top - 0.2
        xs = (-6.85, -5.05, 0.6)
        widths = (1.6, 5.4, 6.25)
        head = VGroup(
            tex(r"\textbf{theorem}", size=21, color=MUTED).move_to([xs[0], top, 0], aligned_edge=LEFT),
            tex(r"\textbf{what you know}", size=21, color=MUTED).move_to([xs[1], top, 0], aligned_edge=LEFT),
            tex(r"\textbf{what you get}", size=21, color=MUTED).move_to([xs[2], top, 0], aligned_edge=LEFT),
        )
        rule = Line([xs[0], top - 0.25, 0], [6.85, top - 0.25, 0], color=MUTED, stroke_width=1.5)
        rows = VGroup()
        y = top - 0.45
        for name, know, get in self.ROWS:
            cells = [
                math(name, size=30, color=SINE),
                para(know, width=widths[1], size=20),
                para(get, width=widths[2], size=20),
            ]
            h = max(c.height for c in cells) + 0.3
            bg = Rectangle(width=13.75, height=h, fill_color=PANEL, fill_opacity=0.6, stroke_width=0).move_to([0, y - h / 2, 0])
            for x, c in zip(xs, cells):
                c.move_to([x, y - h / 2, 0], aligned_edge=LEFT)
            rows.add(VGroup(bg, *cells))
            y -= h + 0.12
        foot = para(
            r"All four hold for every unitarily invariant norm, in infinite dimensions and for unbounded self-adjoint "
            r"operators, and all four are proved in Lean. Each bound is attained by a $2\times2$ example.",
            width=13.6, size=19, color=MUTED, align="centering",
        ).move_to([0, y - 0.25, 0], aligned_edge=UP)

        self.say(
            "Which theorem when? It depends on what you know. sin Theta: trial vectors and a gap to the unwanted "
            "eigenvalues of the new matrix, on either side."
        )
        self.play(FadeIn(head), Create(rule), FadeIn(rows[0]))
        self.say("tan Theta: the same with Rayleigh-Ritz values and a one-sided gap, as when computing the lowest eigenvalues.")
        self.play(FadeIn(rows[1]))
        self.say("sin 2 Theta: only that the new matrix's own eigenvalues split, at the price of the angle ambiguity.")
        self.play(FadeIn(rows[2]))
        self.say(
            "tan 2 Theta: only the old matrix's gap and a purely coupling perturbation: a bound before computing "
            "anything about A plus H. None of the four implies another, and each is sharp."
        )
        self.play(FadeIn(rows[3]), FadeIn(foot))
