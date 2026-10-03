"""Slides: the other three Davis--Kahan theorems (tan Theta, sin 2Theta, tan 2Theta).

Full deck only.  The four Section 2 theorems share one setup -- an old matrix
``A``, a new one ``A + H``, and an invariant subspace of each -- and differ in
*which* two parts of the spectrum the gap separates.  Every number on these
slides comes from the checked models in :mod:`dkvis.sine_theta_story`:

* :class:`~dkvis.sine_theta_story.TwoDirections` -- tan Theta is exact in two
  dimensions with a Rayleigh--Ritz value;
* :class:`~dkvis.sine_theta_story.TwoSidedTrial` -- tan Theta fails when the
  unwanted spectrum lies on both sides;
* :class:`~dkvis.sine_theta_story.PerturbedPair` -- the 2x2 example of the gap
  slides, where tan Theta, sin 2Theta and tan 2Theta are all equalities.

The statements follow the repository's source specification
(``prose/distilled_literature/DavisKahan1970_part_III.tex``, Section 2 and
Theorems 8.1--8.2).
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
    BraceBetweenPoints,
    Circle,
    Create,
    DashedVMobject,
    Dot,
    FadeIn,
    GrowArrow,
    Line,
    Rectangle,
    Triangle,
    ValueTracker,
    VGroup,
    always_redraw,
    rate_functions,
)

from dkvis import sine_theta_story as story
from dkvis.notation import concept_color
from dkvis.slide_style import (
    FAINT,
    FG,
    GAP,
    MUTED,
    RESID,
    SINE,
    TRIAL,
    UNWANTED,
    WANTED,
    DeckSlide,
    boxed,
    dashed,
    math,
    para,
    tex,
)
from dkvis.slides_sine_theta import (
    ELLIPSE_BASE,
    RIGHT_COL_X,
    RIGHT_COL_W,
    Plane,
    angle_arc,
    ellipse,
    fit_right,
    readout_rows,
    segment,
    through_origin,
    vec,
)

TEXT_X = RIGHT_COL_X - 0.2
TEXT_W = RIGHT_COL_W + 0.3
FLOOR = -3.4


def text_column(*mobs, top: float, buff: float = 0.24) -> VGroup:
    """The right-hand column, laid out once in its final form (builds only add)."""
    col = VGroup(*mobs).arrange(DOWN, aligned_edge=LEFT, buff=buff)
    col.move_to([TEXT_X, top, 0], aligned_edge=UP + LEFT)
    if col.get_bottom()[1] < FLOOR:
        col.scale((col.get_top()[1] - FLOOR) / col.height, about_edge=UP + LEFT)
    for m in col:
        fit_right(m)
    return col


def axis(lo: float, hi: float, x_lo: float, x_hi: float, y: float):
    """A number line and its value-to-point map."""

    def X(t: float) -> np.ndarray:
        return np.array([x_lo + (t - lo) / (hi - lo) * (x_hi - x_lo), y, 0.0])

    return Line(X(lo), X(hi), color=MUTED, stroke_width=2), X


def gap_mark(a: np.ndarray, b: np.ndarray, label: str, direction=UP, size: float = 22) -> VGroup:
    """A violet brace (or a bar when too short for a brace) labelled ``label``."""
    a, b = (a, b) if a[0] <= b[0] else (b, a)
    if b[0] - a[0] > 0.3:
        mark = BraceBetweenPoints(a, b, direction=direction, color=GAP)
    else:
        mark = Line(a + direction * 0.1, b + direction * 0.1, color=GAP, stroke_width=4)
    return VGroup(mark, tex(label, size=size, color=GAP).next_to(mark, direction, buff=0.05))


def rho_marker(point: np.ndarray) -> Triangle:
    return Triangle(color=TRIAL, fill_color=TRIAL, fill_opacity=1).scale(0.09).rotate(np.pi).move_to(point + UP * 0.13)


def two_by_two(plane: Plane, pair: story.PerturbedPair, reach: float = 2.3) -> VGroup:
    """The 2x2 example: both operators neutral (old ``A`` dashed); A's top eigenvector, the trial, amber;
    the target, ``A + H``'s top eigenvector, blue."""
    top = pair.perturbed_top_eigenvector
    return VGroup(
        DashedVMobject(ellipse(plane, pair.A, color=MUTED, width=2), num_dashes=56),
        through_origin(plane, [1.0, 0.0], reach, TRIAL, width=3, opacity=0.85),
        ellipse(plane, pair.perturbed, color=FG, width=3),
        through_origin(plane, top, reach, WANTED, width=3.5),
        angle_arc(plane, [1.0, 0.0], top, 0.9 * plane.scale, SINE, width=4),
    )


# ----------------------------------------------------------------------------
# F1. The shared setup
# ----------------------------------------------------------------------------


class F01Setup(DeckSlide):
    depth = "*"
    title = "Four theorems, one setup"
    kicker = r"An old matrix $A$, a new one $A+H$, and an invariant subspace of each"

    def body(self) -> None:
        line_old, X_old = axis(0.3, 3.2, -6.5, -0.9, 1.45)
        line_new, X_new = axis(0.3, 3.2, -6.5, -0.9, 0.05)

        def spectrum(line, X, wanted, rest, caption, w_key, r_key) -> VGroup:
            """The kept block filled and boxed, the rest hollow, each in its symbol's color."""
            color, r_color = concept_color(w_key), concept_color(r_key)
            y = X(0.0)[1]
            box = Rectangle(
                width=X(wanted[-1])[0] - X(wanted[0])[0] + 0.45, height=0.42,
                stroke_color=color, stroke_width=2, fill_color=color, fill_opacity=0.12,
            ).move_to((X(wanted[0]) + X(wanted[-1])) / 2)
            dots = VGroup(
                *[Dot(X(t), radius=0.08, color=color) for t in wanted],
                *[Circle(radius=0.075, color=r_color, stroke_width=3).move_to(X(t)) for t in rest],
            )
            cap = tex(caption, size=22, color=FG).move_to([X(0.3)[0], y + 0.5, 0], aligned_edge=LEFT)
            w = math(rf"\sym{{{w_key}}}", size=28).next_to(box, DOWN, buff=0.08)
            r = math(rf"\sym{{{r_key}}}", size=28).next_to((X(rest[0]) + X(rest[-1])) / 2, DOWN, buff=0.22)
            return VGroup(line, box, dots, cap, w, r)

        old = spectrum(line_old, X_old, (0.6, 0.95), (2.0, 2.45, 2.9), r"eigenvalues of the old $A$", "A0", "A1")
        new = spectrum(line_new, X_new, (0.7, 1.1), (1.85, 2.55, 2.8), r"eigenvalues of the new $A+H$", "Lambda0", "Lambda1")

        head = tex(r"Which eigenvalues each theorem keeps apart:", size=24)
        rows = [
            (r"$\sin\Theta$", r"$\sym{A0}$ vs $\sym{Lambda1}$", r"interval/exterior"),
            (r"$\tan\Theta$", r"$\sym{A0}$ vs $\sym{Lambda1}$", r"one-sided; $A_0$ Rayleigh--Ritz"),
            (r"$\sin2\Theta$", r"$\sym{Lambda0}$ vs $\sym{Lambda1}$", r"interval/exterior"),
            (r"$\tan2\Theta$", r"$\sym{A0}$ vs $A_1$", r"one-sided; $H_0=H_1=0$"),
        ]
        cells = [[tex(c, size=22, color=SINE if j == 0 else FG) for j, c in enumerate(r)] for r in rows]
        xs = (-6.4, -5.1, -3.3)
        table = VGroup()
        for i, row in enumerate(cells):
            for x, cell in zip(xs, row):
                cell.move_to([x, -1.45 - 0.45 * i, 0], aligned_edge=LEFT)
                table.add(cell)
        head.move_to([-6.4, -0.95, 0], aligned_edge=LEFT)

        size, w = 21, TEXT_W
        p_old = para(
            r"\textbf{The old $A$:} $\sym{E0}$ is an orthonormal basis of an invariant subspace "
            r"$\sym{V}$ of $A$ (its wanted eigenvectors), with block $\sym{A0}=E_0^*AE_0$; $A_1$ is the "
            r"rest of $A$.",
            width=w, size=size,
        )
        p_new = para(
            r"\textbf{The new $\tilde A=A+H$:} $\sym{F0}$ spans the corresponding invariant subspace "
            r"$\sym{U}$ of $\tilde A$, with block $\sym{Lambda0}$; $\sym{Lambda1}$ is the rest.",
            width=w, size=size,
        )
        p_ang = para(
            r"$\sym{Theta0}$: the angles between the two subspaces. $\sym{Theta}$: the same angles seen "
            r"from both subspaces, so each nonzero angle appears twice.",
            width=w, size=size,
        )
        p_res = para(
            r"The residual $\sym{R}=(A+H)E_0-E_0A_0$ equals $HE_0$. In $A$'s eigenbasis "
            r"$H=\left(\begin{smallmatrix}H_0&B^*\\ B&H_1\end{smallmatrix}\right)$: $B$ couples wanted with unwanted "
            r"directions, $H_0$ and $H_1$ act within them.",
            width=w, size=size,
        )
        p_forms = para(
            r"Each theorem has a \emph{directed} form, with $\Theta_0$ and $\norm{R}$; the last three also have an "
            r"\emph{ambient} form, with $\Theta$ and $\norm{H}$.",
            width=w, size=size,
        )
        p_bridge = para(
            r"Same notation as before: $\sym{U}$ is the target subspace of the matrix we have, $\tilde A$, and "
            r"$\sym{V}$ the trial subspace; in the trial reading $E_0$ is any orthonormal trial basis.",
            width=w, size=size - 1, color=MUTED,
        )
        col = text_column(p_old, p_new, p_ang, p_res, p_forms, p_bridge, top=self.content_top - 0.1)

        self.say(
            "The sin Theta theorem is the first of four in Section 2 of the paper. All four share one setup: "
            "an old matrix A with an invariant subspace spanned by E0, the trial side in amber, and a new matrix A + H "
            "with the corresponding invariant subspace spanned by F0, the wanted side in blue. Their blocks are A0, A1 "
            "and Lambda0, Lambda1; Lambda1, the unwanted part of the new matrix, is cyan."
        )
        self.play(FadeIn(old), FadeIn(new), FadeIn(col[0]), FadeIn(col[1]))

        self.say(
            "Theta0 is the angles between the two subspaces; the residual is H E0; and H splits into the part B "
            "that couples wanted with unwanted directions and the parts H0, H1 that act within them. "
            "Each theorem has a directed form with Theta0 and R, and three have an ambient form with Theta and H. "
            "Same notation as before: U is the target subspace of A tilde, the matrix we have, and V the "
            "trial subspace."
        )
        self.play(FadeIn(col[2]), FadeIn(col[3]), FadeIn(col[4]), FadeIn(col[5]))

        self.say(
            "What distinguishes the four theorems is which two parts of the spectrum the gap keeps apart. "
            "sin Theta and tan Theta compare the trial values A0 with the new unwanted eigenvalues; sin 2 Theta "
            "compares the new matrix with itself; tan 2 Theta compares the old matrix with itself."
        )
        self.play(FadeIn(head), FadeIn(table))


# ----------------------------------------------------------------------------
# F2. tan Theta
# ----------------------------------------------------------------------------


class F02TanTheta(DeckSlide):
    depth = "*"
    title = r"The $\tan\Theta$ theorem: a one-sided gap"
    kicker = r"Rayleigh--Ritz trial values, and every unwanted eigenvalue on the same side"

    def body(self) -> None:
        ex = story.TWO_DIRECTIONS
        ex.verify()
        bad = story.TWO_SIDED
        bad.verify()
        th = ex.theta
        plane = Plane([-5.75, -0.75, 0], 2.05)
        v = np.array([pymath.cos(th), pymath.sin(th)])
        tan_pt = np.array([1.0, ex.tan_theta])

        u_axis = Line(plane([-0.15, 0]), plane([1.3, 0]), color=WANTED, stroke_width=3)
        w_axis = Line(plane([0, -0.1]), plane([0, 1.15]), color=UNWANTED, stroke_width=3)
        u_lbl = tex(r"$u$: wanted eigenvector", size=20, color=concept_color("u")).next_to(plane([1.3, 0]), RIGHT, buff=0.1)
        w_lbl = tex(r"$w$: unwanted", size=20, color=concept_color("w")).next_to(plane([0, 1.15]), UP, buff=0.06)
        circle = Arc(radius=plane.scale, start_angle=0, angle=np.radians(62), arc_center=plane.origin, color=FAINT, stroke_width=2)
        v_arrow = vec(plane.origin, plane(v), TRIAL, width=6)
        v_lbl = math(r"\sym{v}", size=30).next_to(plane(v), UP, buff=0.08).shift(LEFT * 0.12)
        ray = dashed(plane(v), plane(tan_pt), TRIAL, 1.5)
        arc = angle_arc(plane, [1, 0], v, 0.42, FG, width=3)
        th_lbl = math(r"\theta", size=26).move_to(plane(0.3 * story.unit(th / 2)))
        sin_seg = segment(plane([v[0], 0]), plane(v), SINE, width=7)
        sin_lbl = math(r"\sym{sintheta}", size=24).next_to(plane([v[0], v[1] / 2]), LEFT, buff=0.08)
        tan_seg = segment(plane([1.0, 0]), plane(tan_pt), SINE, width=7)
        tan_lbl = math(r"\tan\theta", size=24, color=concept_color("theta")).next_to(plane([1.0, tan_pt[1] / 2]), RIGHT, buff=0.08)
        one = math(r"1", size=22, color=MUTED).next_to(plane([1.0, 0]), DOWN, buff=0.08)
        r_arrow = vec(plane.origin, plane(ex.r), RESID, width=5)
        r_lbl = math(r"\sym{r}", size=28).next_to(plane(ex.r), UP, buff=0.06)

        nl, X = axis(0.5, 2.9, -6.6, -1.3, -1.85)
        spectrum = VGroup(
            nl,
            Dot(X(ex.lam_u), radius=0.08, color=WANTED),
            Dot(X(ex.lam_w), radius=0.08, color=UNWANTED),
            math(r"\sym{lambdau}", size=22).next_to(X(ex.lam_u), DOWN, buff=0.1),
            math(r"\sym{lambdaw}", size=22).next_to(X(ex.lam_w), DOWN, buff=0.1),
            rho_marker(X(ex.rho)),
            math(r"\sym{rho}", size=22).next_to(X(ex.rho), DOWN, buff=0.1),
        )
        one_sided = VGroup(
            gap_mark(X(ex.rho) + UP * 0.25, X(ex.lam_w) + UP * 0.25, r"$\delta$", size=19),
            tex(r"one-sided", size=19, color=MUTED).next_to(X(2.9), RIGHT, buff=0.12),
        )

        # The two-sided counterexample, on its own small number line.
        nl2, X2 = axis(-1.35, 1.35, -6.4, -2.4, -3.0)
        both = VGroup(
            nl2,
            Dot(X2(-1.0), radius=0.08, color=UNWANTED),
            Dot(X2(0.0), radius=0.08, color=TRIAL),
            Dot(X2(1.0), radius=0.08, color=UNWANTED),
            rho_marker(X2(0.0)),
            math(r"-1", size=20, color=concept_color("Lambda1")).next_to(X2(-1.0), DOWN, buff=0.08),
            math(r"0", size=20, color=concept_color("rho")).next_to(X2(0.0), DOWN, buff=0.08),
            math(r"1", size=20, color=concept_color("Lambda1")).next_to(X2(1.0), DOWN, buff=0.08),
            gap_mark(X2(-1.0) + UP * 0.22, X2(0.0) + UP * 0.22, r"$\delta$", size=19),
            gap_mark(X2(0.0) + UP * 0.22, X2(1.0) + UP * 0.22, r"$\delta$", size=19),
            tex(r"two-sided", size=19, color=MUTED).next_to(X2(1.35), RIGHT, buff=0.12),
        )

        size, w = 22, TEXT_W
        hyp = para(
            r"\textbf{Hypotheses.} The trial matrix is the Rayleigh--Ritz one, $\sym{A0}=E_0^*(A+H)E_0$ "
            r"(equivalently $H_0=0$), with eigenvalues in $[\beta,\alpha]$, and every unwanted eigenvalue of $A+H$ "
            r"is at least $\alpha+\delta$: all on one side. This is the situation when Rayleigh--Ritz targets the "
            r"lowest (or, mirrored, the highest) eigenvalues.",
            width=w, size=size,
        )
        box = boxed(
            math(
                r"\sym{delta}\norm{\like{theta}{\tan\Theta_0}}\le\norm{\sym{R}},\qquad"
                r"\sym{delta}\norm{\like{theta}{\tan\Theta}}\le\norm{H}",
                size=32,
            ),
            color=SINE,
            pad=0.18,
        )
        why = para(
            r"$\tan\theta\ge\sin\theta$, so this is stronger than the $\sin\Theta$ theorem, by a lot for large angles, "
            r"and it rules out $\theta=90^\circ$. In two dimensions it is exact:",
            width=w, size=size,
        )
        nums = math(
            rf"\delta\sin\theta={ex.delta * ex.sin_theta:.3f}\ <\ \delta\tan\theta={ex.delta * ex.tan_theta:.3f}"
            rf"\ =\ \norm{{\cx{{resid}}{{r}}}}={ex.residual_norm:.3f}",
            size=28,
        )
        bad_txt = para(
            r"\textbf{One-sidedness is essential.} Take $A=\operatorname{diag}(-1,0,1)$, wanted eigenvalue $0$, and "
            r"$v=\cos\theta\,e_2+\sin\theta\,(e_1+e_3)/\sqrt2$. Then $\rho=0$, $\delta=1$ on \emph{both} sides and "
            rf"$\norm{{r}}=\sin\theta$: the $\sin\Theta$ bound is an equality, but $\delta\tan\theta\le\norm{{r}}$ fails "
            rf"for every $\theta>0$ (at $45^\circ$: $1>{bad.residual_norm:.3f}$).",
            width=w, size=size - 1,
        )
        cite = para(r"Davis and Kahan make the same point with their Example~6.1.", width=w, size=size - 2, color=MUTED)
        col = text_column(hyp, box, VGroup(why, nums).arrange(DOWN, aligned_edge=LEFT, buff=0.12), VGroup(bad_txt, cite).arrange(DOWN, aligned_edge=LEFT, buff=0.08), top=self.content_top - 0.1)

        self.say(
            "The tan Theta theorem. One wanted eigenvector u and one unwanted w, a trial vector v at angle theta. "
            "On the unit circle sin theta is the height of v; tan theta is the height where the ray through v "
            "meets the vertical line at 1. tan theta is always the larger, and it blows up at 90 degrees."
        )
        self.play(Create(u_axis), Create(w_axis), FadeIn(u_lbl, w_lbl, circle))
        self.play(GrowArrow(v_arrow), FadeIn(v_lbl, arc, th_lbl, sin_seg, sin_lbl, ray, tan_seg, tan_lbl, one), FadeIn(col[0]))

        self.say(
            "The hypotheses: the trial value is the Rayleigh quotient, and all unwanted eigenvalues lie on one side, "
            "at least delta beyond it. Then tan replaces sin, both for the residual and for H."
        )
        self.play(FadeIn(spectrum), FadeIn(one_sided), FadeIn(col[1]))

        self.say(
            "In two dimensions the tan Theta bound is exact: delta tan theta equals the length of the residual, "
            "while delta sin theta falls short."
        )
        self.play(GrowArrow(r_arrow), FadeIn(r_lbl), FadeIn(col[2]))

        self.say(
            "Why one-sided? Put unwanted eigenvalues on both sides, at minus 1 and plus 1, and a trial vector "
            "leaning equally toward both. The Rayleigh quotient stays at 0, the residual is sin theta, so the sin "
            "Theta theorem holds with equality, but tan theta is bigger than sin theta, so the tan Theta "
            "conclusion fails. Davis and Kahan's Example 6.1 makes the same point."
        )
        self.play(FadeIn(both), FadeIn(col[3]))


# ----------------------------------------------------------------------------
# F3. sin 2Theta
# ----------------------------------------------------------------------------


class F03SinTwoTheta(DeckSlide):
    depth = "*"
    title = r"The $\sin2\Theta$ theorem: a gap inside the new matrix"
    kicker = r"No condition on the trial values; the price is the double angle"

    def body(self) -> None:
        eps = story.PERTURBATION_EPS
        pair = story.PerturbedPair(gap=story.PERTURBATION_START_GAP, eps=eps)
        pair.verify()
        plane = Plane([-4.2, 0.55, 0], 0.82, rotate=ELLIPSE_BASE)
        picture = two_by_two(plane, pair)
        th_lbl = math(r"\sym{theta}", size=26).move_to(plane(1.2 * story.unit(pair.theta / 2 + 0.12)))
        key = VGroup(
            tex(r"dashed: old $A$; \cx{trial}{amber: its top eigenvector}", size=18),
            tex(r"solid: new $A+H$; \cx{wanted}{blue: its top eigenvector}", size=18),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.05).move_to([-6.9, 2.3, 0], aligned_edge=UP + LEFT)

        lam1, lam0 = pair.perturbed_eigenvalues[1], pair.perturbed_eigenvalues[0]
        nl, X = axis(0.8, 2.2, -6.5, -1.9, -1.45)
        spectrum = VGroup(
            nl,
            Dot(X(lam0), radius=0.08, color=WANTED),
            Dot(X(lam1), radius=0.08, color=UNWANTED),
            math(r"\sym{Lambda0}", size=24).next_to(X(lam0), DOWN, buff=0.1),
            math(r"\sym{Lambda1}", size=24).next_to(X(lam1), DOWN, buff=0.1),
            tex(r"eigenvalues of $A+H$", size=19, color=MUTED).next_to(X(2.2), RIGHT, buff=0.1),
        )
        sep = gap_mark(X(lam1) + UP * 0.22, X(lam0) + UP * 0.22, rf"$\delta={pair.delta_sin_two:.3f}$", size=20)

        # theta and 90 - theta have the same sin 2theta.
        small = Plane([-6.45, -3.2, 0], 1.05)
        a, b = np.radians(20.0), np.radians(70.0)
        twin = VGroup(
            Line(small([0, 0]), small([1.25, 0]), color=WANTED, stroke_width=3),
            Line(small([0, 0]), small(1.15 * story.unit(a)), color=TRIAL, stroke_width=3),
            Line(small([0, 0]), small(1.15 * story.unit(b)), color=TRIAL, stroke_width=3),
            angle_arc(small, [1, 0], story.unit(a), 0.55, SINE, width=3),
            angle_arc(small, [1, 0], story.unit(b), 0.32, SINE, width=3),
            math(r"20^\circ", size=19, color=concept_color("theta")).next_to(small(1.15 * story.unit(a)), RIGHT, buff=0.06),
            math(r"70^\circ", size=19, color=concept_color("theta")).next_to(small(1.15 * story.unit(b)), RIGHT, buff=0.06),
        )
        twin_txt = para(
            rf"$\theta$ and $90^\circ-\theta$ have the same $\sin2\theta$ (here ${pymath.sin(2 * a):.2f}$)",
            width=3.4, size=20, color=MUTED,
        ).move_to([-4.6, -2.75, 0], aligned_edge=LEFT)

        size, w = 22, TEXT_W
        hyp = para(
            r"\textbf{Hypotheses.} Only the new matrix's own spectrum: $\sym{Lambda0}$ in $[\beta,\alpha]$ and "
            r"$\sym{Lambda1}$ outside $(\beta-\delta,\alpha+\delta)$. Nothing about the trial values $\sym{A0}$: useful when "
            r"the new matrix's eigenvalues are known to split but the trial values are not controlled.",
            width=w, size=size,
        )
        box = boxed(
            math(
                r"\sym{delta}\norm{\like{theta}{\sin2\Theta_0}}\le2\norm{\sym{R}},\qquad"
                r"\sym{delta}\norm{\like{theta}{\sin2\Theta}}\le2\norm{H}",
                size=32,
            ),
            color=SINE,
            pad=0.18,
        )
        _, lhs, rhs = pair.family()["sin2"]
        example = para(
            rf"In the $2\times2$ example ($g={pair.gap:g}$, $\varepsilon={eps:g}$) the gap of $A+H$ is "
            rf"$\delta={pair.delta_sin_two:.3f}$, and $\delta\sin2\theta={lhs:.3f}=2\norm{{R}}$: an equality.",
            width=w, size=size,
        )
        price = para(
            r"\textbf{The price.} $\sin2\theta$ cannot tell $\theta$ from $90^\circ-\theta$, and the theorem accepts "
            r"\emph{any} invariant subspace $F_0$ of $A+H$ whose spectrum splits this way. Even with $H=0$ a "
            r"mismatched $F_0$ can be $90^\circ$ away, where $\sin2\theta=0$.",
            width=w, size=size,
        )
        thm82 = para(
            r"Theorem 8.2 adds $\norm{H}_2<\delta/2$ (or $\norm{R}_2<\delta/2$) and "
            r"$\operatorname{spec}\sym{A0}\subset[\beta-\delta/2,\alpha+\delta/2]$. Then every angle is below $45^\circ$, "
            r"so a small $\sin2\Theta$ does mean a small $\Theta$.",
            width=w, size=size - 1, color=MUTED,
        )
        col = text_column(hyp, box, example, price, thm82, top=self.content_top - 0.1)

        self.say(
            "The sin 2 Theta theorem asks for a gap inside the new matrix alone: its wanted eigenvalues Lambda0 "
            "separated from the rest, Lambda1. Nothing is assumed about the trial values. The conclusion bounds "
            "sin 2 Theta, with a factor 2."
        )
        self.play(FadeIn(picture, th_lbl, key), FadeIn(col[0]))
        self.play(FadeIn(spectrum), FadeIn(sep), FadeIn(col[1]))

        self.say(
            "On the 2 by 2 example from the gap slides the bound is an equality: delta here is the gap between "
            "the two eigenvalues of A + H."
        )
        self.play(FadeIn(col[2]))

        self.say(
            "The price of the double angle: sin 2 theta is the same for theta and 90 minus theta. And the theorem "
            "lets F0 be any invariant subspace with that spectral split, so a small sin 2 Theta does not by itself "
            "say the angle is small. Theorem 8.2 adds a smallness condition that pins it to the acute branch."
        )
        self.play(FadeIn(twin, twin_txt), FadeIn(col[3]), FadeIn(col[4]))


# ----------------------------------------------------------------------------
# F4. tan 2Theta
# ----------------------------------------------------------------------------


class F04TanTwoTheta(DeckSlide):
    depth = "*"
    title = r"The $\tan2\Theta$ theorem: a gap in the old matrix"
    kicker = r"An a priori bound: only $A$'s spectrum matters, and $H$ is off-diagonal"

    def body(self) -> None:
        eps = story.PERTURBATION_EPS
        g = ValueTracker(story.PERTURBATION_START_GAP)
        plane = Plane([-4.2, 0.6, 0], 0.82, rotate=ELLIPSE_BASE)

        def pair() -> story.PerturbedPair:
            return story.PerturbedPair(gap=g.get_value(), eps=eps)

        picture = always_redraw(lambda: two_by_two(plane, pair()))
        th_lbl = always_redraw(
            lambda: math(r"\sym{theta}", size=26).move_to(plane(1.1 * story.unit(max(pair().theta, 0.2) / 2)))
        )
        key = VGroup(
            tex(r"dashed: old $A$; \cx{trial}{amber: its top eigenvector}", size=18),
            tex(r"solid: new $A+H$; \cx{wanted}{blue: its top eigenvector}", size=18),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.05).move_to([-6.9, 2.3, 0], aligned_edge=UP + LEFT)

        nl, X = axis(0.8, 2.2, -6.5, -1.9, -1.45)

        def old_spectrum():
            lam0, lam1 = pair().A.diagonal()
            return VGroup(
                Dot(X(lam0), radius=0.08, color=TRIAL),
                Circle(radius=0.075, color=concept_color("A1"), stroke_width=3).move_to(X(lam1)),
                math(r"\sym{A0}", size=24).next_to(X(lam0), DOWN, buff=0.1).shift(RIGHT * 0.2),
                math(r"\sym{A1}", size=24).next_to(X(lam1), DOWN, buff=0.1).shift(LEFT * 0.2),
                gap_mark(X(lam1) + UP * 0.22, X(lam0) + UP * 0.22, r"$\delta=g$", size=20),
            )

        spectrum = VGroup(nl, always_redraw(old_spectrum), tex(r"eigenvalues of $A$", size=19, color=MUTED).next_to(X(2.2), RIGHT, buff=0.1))
        rows_l = readout_rows([(r"g =", lambda: g.get_value(), FG, 2, None), (r"\norm{H}_2 =", lambda: eps, FG, 2, None)], size=24)
        rows_r = readout_rows(
            [
                (r"\theta =", lambda: pymath.degrees(pair().line_angle), SINE, 1, r"^\circ"),
                (r"g\tan2\theta =", lambda: g.get_value() * pair().tan_two_theta, FG, 3, None),
            ],
            size=24,
        )
        rows_l.move_to([-5.4, -2.65, 0])
        rows_r.move_to([-2.5, -2.65, 0])

        size, w = 22, TEXT_W
        hyp = para(
            r"\textbf{Hypotheses.} Only the old matrix's own spectrum, one-sided: every eigenvalue of $A_1$ at least "
            r"$\delta$ beyond those of $\sym{A0}$. And $H_0=H_1=0$: in $A$'s eigenbasis $H$ only couples "
            r"wanted with unwanted directions.",
            width=w, size=size,
        )
        box = boxed(
            math(
                r"\sym{delta}\norm{\like{theta}{\tan2\Theta_0}}\le2\norm{\sym{R}},\qquad"
                r"\sym{delta}\norm{\like{theta}{\tan2\Theta}}\le2\norm{H}",
                size=32,
            ),
            color=SINE,
            pad=0.18,
        )
        prior = para(r"Nothing is assumed about $A+H$: an \emph{a priori} bound, from $A$ and $H$ alone.", width=w, size=size)
        example = para(
            r"The gap example from the start is exactly this case. In $2\times2$ the bound is the Jacobi rotation "
            r"formula $\tan2\theta=2b/(a_0-a_1)$, an equality at every gap: "
            rf"$g\tan2\theta=2\varepsilon={2 * eps:.2f}$. As $g\to0$, $\tan2\theta\to\infty$, so $2\theta\to90^\circ$ "
            r"and $\theta\to45^\circ$, never beyond.",
            width=w, size=size,
        )
        thm81 = para(
            r"Theorem 8.1: if $F_0$ is the matching spectral subspace of $A+H$ (its wanted eigenvalues on $\sym{A0}$'s side "
            r"of the gap, the rest on $A_1$'s), every angle is at most $45^\circ$, however large $H$ is. That is the "
            r"$45^\circ$ ceiling seen at the start.",
            width=w, size=size - 1, color=MUTED,
        )
        col = text_column(hyp, box, prior, example, thm81, top=self.content_top - 0.1)

        self.say(
            "The tan 2 Theta theorem needs a gap in the old matrix only, one-sided, and a perturbation with no "
            "diagonal blocks: it only couples wanted with unwanted directions. Then tan 2 Theta is bounded by "
            "2 norm H over delta. Nothing about the new spectrum is needed: an a priori bound."
        )
        self.add(picture, th_lbl)
        self.play(FadeIn(picture, th_lbl, key), FadeIn(spectrum), FadeIn(rows_l, rows_r), FadeIn(col[0]), FadeIn(col[1]), FadeIn(col[2]))

        self.say(
            "This is the example from the gap slides. Close the gap of A: g times tan 2 theta stays at 0.24, "
            "twice the size of H, the whole way down. The bound is an equality. tan 2 theta grows without bound, "
            "so 2 theta approaches 90 degrees and theta approaches 45, never more."
        )
        self.play(g.animate.set_value(story.PERTURBATION_END_GAP), run_time=6.0, rate_func=rate_functions.ease_in_out_sine)
        self.play(FadeIn(col[3]))

        self.say(
            "Theorem 8.1 makes that general: when F0 is the matching spectral subspace of A + H, every angle is at "
            "most 45 degrees, however large H is. That is the ceiling we saw at the start."
        )
        self.play(FadeIn(col[4]))


# ----------------------------------------------------------------------------
# F1b. Directed and ambient angles
# ----------------------------------------------------------------------------


class F01bAngles(DeckSlide):
    depth = "*"
    title = "Directed and ambient angles"
    kicker = r"$\Theta_0$ looks from the trial subspace; $\Theta$ looks at the whole rotation"

    def body(self) -> None:
        th = np.radians(28.0)
        plane = Plane([-4.4, -0.35, 0], 2.0)
        reach = 1.15
        e1, e2 = np.array([1.0, 0.0]), np.array([0.0, 1.0])
        v, v_perp = story.unit(th), story.unit(th + np.pi / 2)

        V = through_origin(plane, e1, reach, concept_color("V"), width=4)
        U = through_origin(plane, v, reach, concept_color("U"), width=4)
        V_lbl = tex(r"$V=\operatorname{ran}E_0$", size=22, color=concept_color("V")).next_to(plane(reach * e1), DOWN, buff=0.1)
        U_lbl = tex(r"$U=\operatorname{ran}F_0$", size=22, color=concept_color("U")).next_to(plane(reach * v), RIGHT, buff=0.1)
        arc = angle_arc(plane, e1, v, 1.15, SINE, width=4)
        th_lbl = math(r"\sym{theta}", size=28).move_to(plane(0.72 * story.unit(th / 2)))

        V_perp = DashedVMobject(through_origin(plane, e2, reach, concept_color("Vperp"), width=3), num_dashes=24)
        U_perp = DashedVMobject(through_origin(plane, v_perp, reach, concept_color("Uperp"), width=3), num_dashes=24)
        Vp_lbl = math(r"\sym{Vperp}", size=24).next_to(plane(reach * e2), UP, buff=0.08)
        Up_lbl = math(r"\sym{Uperp}", size=24).next_to(plane(reach * v_perp), LEFT, buff=0.08)
        arc2 = angle_arc(plane, e2, v_perp, 0.8, SINE, width=4)
        th2_lbl = math(r"\sym{theta}", size=28).move_to(plane(0.52 * story.unit(np.pi / 2 + th / 2)))
        caption = para(
            r"The rotation that takes $V$ to $U$ also takes $V^\perp$ to $U^\perp$, by the same angle.",
            width=5.0, size=19, color=MUTED, align="centering",
        ).move_to([-4.4, -3.2, 0])

        size, w = 21, TEXT_W
        p_dir = para(
            r"\textbf{Directed} $\sym{Theta0}$: the angles from the trial subspace $\sym{V}$ to "
            r"the target $\sym{U}$, one per direction of $V$. With $Q$ the projector onto $U$: "
            r"$\norm{\sin\Theta_0}=\norm{(I-Q)E_0}$.",
            width=w, size=size,
        )
        p_amb = para(
            r"\textbf{Ambient} $\sym{Theta}$: the angles of the whole rotation, so each nonzero angle appears "
            r"twice. With $P$ the projector onto $V$, every unitarily invariant norm has "
            r"$\norm{\sin\Theta}=\norm{P-Q}$.",
            width=w, size=size,
        )
        p_norms = para(
            r"They agree in the operator norm; in the Frobenius norm $\norm{\sin\Theta}_F=\sqrt2\,\norm{\sin\Theta_0}_F$ "
            r"(here $\sqrt2\sin\theta$ against $\sin\theta$).",
            width=w, size=size,
        )
        p_rh = para(
            r"Directed bounds compare with the residual $\sym{R}=HE_0$, the part of $H$ acting on $V$; ambient "
            r"bounds compare with all of $H$. Always $\norm{R}\le\norm{H}$.",
            width=w, size=size,
        )
        p_sin = para(
            r"With one gap, $\sin\Theta$ has no ambient form in every norm: Davis and Kahan's $2\times2$ example has "
            r"$\delta\norm{\sin\Theta}_F=2>\sqrt3=\norm{H}_F$. Proposition~6.1 recovers $\delta\norm{\sin\Theta}\le\norm{H}$ "
            r"with a second gap, between $A_1$ and $\sym{Lambda0}$.",
            width=w, size=size - 1, color=MUTED,
        )
        col = text_column(p_dir, p_amb, p_norms, p_rh, p_sin, top=self.content_top - 0.1)

        self.say(
            "Two ways to measure how far a subspace moved. Directed: stand in the trial subspace V and measure the "
            "angle of each of its directions to the target U. That is Theta0, and its sine measures the amount of the "
            "trial subspace V lying outside the target U: the part of E0 outside U."
        )
        self.play(Create(U), Create(V), FadeIn(U_lbl, V_lbl), Create(arc), FadeIn(th_lbl), FadeIn(col[0]))

        self.say(
            "Ambient: look at the whole rotation. Turning V onto U also turns the complement V perp onto U perp, by "
            "the same angle, so every angle shows up twice. Its sine has the same norms as the difference of the two projectors. In the "
            "operator norm the two agree; in the Frobenius norm the ambient one is root 2 larger."
        )
        self.play(Create(U_perp), Create(V_perp), FadeIn(Up_lbl, Vp_lbl), Create(arc2), FadeIn(th2_lbl, caption), FadeIn(col[1]), FadeIn(col[2]))

        self.say(
            "Directed bounds pay with the residual, the part of H that acts on the trial subspace; ambient bounds pay "
            "with all of H. The sin Theta theorem only has the directed form: with one gap, the ambient form fails in "
            "some norms, and Proposition 6.1 needs a second gap to get it back."
        )
        self.play(FadeIn(col[3]), FadeIn(col[4]))


# ----------------------------------------------------------------------------
# F1c. One rotation, four trigonometric functions
# ----------------------------------------------------------------------------


class F01cTwoByTwo(DeckSlide):
    depth = "*"
    title = r"One rotation, four trigonometric functions"
    kicker = r"For a $2\times2$ matrix all four are exact identities, each with its own gap"

    def body(self) -> None:
        eps = story.PERTURBATION_EPS
        pair = story.PerturbedPair(gap=story.FAMILY_EXAMPLE_GAP, eps=eps)
        pair.verify()
        fam = pair.family()
        a0, a1 = pair.A.diagonal()
        l0, l1 = pair.perturbed_eigenvalues
        th = pair.line_angle
        lo, hi, x_lo, x_hi = 1.3, 1.7, -5.55, -0.95
        line_old, X_old = axis(lo, hi, x_lo, x_hi, 1.75)
        line_new, X_new = axis(lo, hi, x_lo, x_hi, 0.75)

        def X(t: float, y: float) -> np.ndarray:
            return np.array([X_old(t)[0], y, 0.0])

        old = VGroup(
            line_old,
            Dot(X_old(a0), radius=0.08, color=concept_color("a0")),
            Circle(radius=0.075, color=concept_color("a1"), stroke_width=3).move_to(X_old(a1)),
            math(rf"\sym{{a0}}={a0:.2f}", size=20).next_to(X_old(a0), UP, buff=0.1),
            math(rf"\sym{{a1}}={a1:.2f}", size=20).next_to(X_old(a1), UP, buff=0.1),
            tex(r"old $A$", size=22, color=FG).next_to(X_old(lo), LEFT, buff=0.15),
        )
        new = VGroup(
            line_new,
            Dot(X_new(l0), radius=0.08, color=concept_color("lambda0")),
            Circle(radius=0.075, color=concept_color("lambda1"), stroke_width=3).move_to(X_new(l1)),
            math(rf"\sym{{lambda0}}={l0:.2f}", size=20).next_to(X_new(l0), UP, buff=0.1),
            math(rf"\sym{{lambda1}}={l1:.2f}", size=20).next_to(X_new(l1), UP, buff=0.1),
            tex(r"new $A+H$", size=22, color=FG).next_to(X_new(lo), LEFT, buff=0.15),
        )

        def span_row(t_from: float, y_from: float, t_to: float, y_to: float, y: float, label: str) -> VGroup:
            """A violet interval at height ``y`` between two eigenvalues, with dashed guides up to them."""
            a, b = X(t_from, y), X(t_to, y)
            bar = VGroup(
                Line(a, b, color=GAP, stroke_width=4),
                Line(a + UP * 0.1, a + DOWN * 0.1, color=GAP, stroke_width=3),
                Line(b + UP * 0.1, b + DOWN * 0.1, color=GAP, stroke_width=3),
            )
            guides = VGroup(dashed(X(t_from, y_from), a, FAINT, 1.2), dashed(X(t_to, y_to), b, FAINT, 1.2))
            text = tex(label, size=21, color=GAP).next_to(bar, UP, buff=0.1)
            return VGroup(guides, bar, text)

        y_old, y_new = 1.75, 0.75
        row_tan2 = span_row(a1, y_old, a0, y_old, -0.45, rf"old gap $a_0-a_1={fam['tan2'][0]:.2f}$")
        row_sin2 = span_row(l1, y_new, l0, y_new, -1.45, rf"new gap $\lambda_0-\lambda_1={fam['sin2'][0]:.2f}$")
        row_tan = span_row(l1, y_new, a0, y_old, -2.45, rf"trial value to new unwanted $a_0-\lambda_1={fam['tan'][0]:.2f}$")

        size = 20
        mat = VGroup(
            math(r"A+H=\begin{pmatrix}a_0&b\\ b&a_1\end{pmatrix}", size=30),
            para(
                rf"in $A$'s eigenbasis: $A=\operatorname{{diag}}(a_0,a_1)$, $H$ off-diagonal with $b={eps:g}$. "
                rf"The top eigenvector of $A+H$ is turned by $\theta={pymath.degrees(th):.1f}^\circ$; its "
                r"eigenvalues are $\lambda_0>\lambda_1$.",
                width=3.9, size=size - 1,
            ),
        ).arrange(RIGHT, buff=0.25)

        def ident(name: str, lhs: str, rhs: str, value: str, rel: str = "=") -> VGroup:
            return VGroup(
                math(name, size=24, color=SINE),
                math(rf"{lhs}{rel}{rhs}", size=28),
                math(value, size=22, color=MUTED),
            )

        b = eps
        rows = VGroup(
            ident(r"\tan2\Theta", r"\tan2\theta", r"\frac{2b}{\like{delta}{a_0-a_1}}", rf"={2 * b / fam['tan2'][0]:.3f}"),
            ident(r"\sin2\Theta", r"\sin2\theta", r"\frac{2b}{\like{delta}{\lambda_0-\lambda_1}}", rf"={2 * b / fam['sin2'][0]:.3f}"),
            ident(r"\tan\Theta", r"\tan\theta", r"\frac{b}{\like{delta}{a_0-\lambda_1}}", rf"={b / fam['tan'][0]:.3f}"),
            ident(r"\sin\Theta", r"\sin\theta", r"\frac{b}{\like{delta}{a_0-\lambda_1}}", rf"\sin\theta={pymath.sin(th):.3f}", rel="<"),
        )
        for r in rows:
            r[1].move_to([2.05, 0, 0], aligned_edge=LEFT)
            r[0].move_to([0.6, 0, 0], aligned_edge=LEFT)
            r[2].move_to([4.95, 0, 0], aligned_edge=LEFT)
        rows.arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        for r in rows:  # re-align columns after arranging rows
            y = r.get_center()[1]
            r[0].move_to([0.6, y, 0], aligned_edge=LEFT)
            r[1].move_to([2.05, y, 0], aligned_edge=LEFT)
            r[2].move_to([4.95, y, 0], aligned_edge=LEFT)
        derive = para(
            r"From the eigenvector equation's second row, $b\cos\theta+a_1\sin\theta=\lambda_0\sin\theta$, so "
            r"$\tan\theta=b/(\lambda_0-a_1)$, and $\lambda_0-a_1=a_0-\lambda_1$. The double-angle lines are the "
            r"Jacobi rotation formula and its companion.",
            width=TEXT_W, size=size - 2, color=MUTED,
        )
        close = para(
            r"With $\norm{H}=\norm{R}=|b|$, multiplying out gives the four theorems' conclusions, three of them with "
            r"equality. The theorems make these $2\times2$ identities into inequalities for subspaces of any dimension, "
            r"in every unitarily invariant norm.",
            width=TEXT_W, size=size,
        )
        col = text_column(mat, rows, derive, close, top=self.content_top - 0.1, buff=0.28)

        self.say(
            "Why these four functions, and why four different gaps? Take the 2 by 2 matrix A plus H written in A's "
            "eigenbasis: A on the diagonal, H off the diagonal. Diagonalizing it turns the eigenvector by theta. "
            "The old eigenvalues on top, the trial value a0 in amber; the new ones below, lambda0 blue and lambda1 "
            "cyan: the new ones are pushed apart."
        )
        self.play(FadeIn(old), FadeIn(new), FadeIn(col[0]))

        self.say(
            "The Jacobi rotation formula: tan 2 theta is 2b over the old gap. Exactly the tan 2 Theta theorem, with "
            "equality."
        )
        self.play(FadeIn(row_tan2), FadeIn(rows[0]))

        self.say("sin 2 theta is 2b over the new gap, the gap of A plus H: the sin 2 Theta theorem, with equality.")
        self.play(FadeIn(row_sin2), FadeIn(rows[1]))

        self.say(
            "tan theta is b over the distance from the trial value a0 to the new unwanted eigenvalue: the tan Theta "
            "theorem, with equality. And sin theta is smaller than tan theta, which is the sin Theta theorem."
        )
        self.play(FadeIn(row_tan), FadeIn(rows[2]), FadeIn(rows[3]))

        self.say(
            "So in two dimensions the four theorems are four exact facts about one rotation, each needing a different "
            "gap. The general theorems turn them into inequalities for subspaces of any dimension, in every unitarily "
            "invariant norm. The paper states all four constants are best possible."
        )
        self.play(FadeIn(col[2]), FadeIn(col[3]))
