"""Slides: an intuition-first introduction to the Davis--Kahan ``sin Theta`` theorem.

Each class is one manim-slides scene; within a scene every ``self.say(...)``
starts a new build (one click) and carries its presenter notes.  ``SCENES``
lists the deck in presentation order.  Build and present from
``visualizations/`` with::

    uv run --extra slides python -m dkvis.build_slides sine-theta          # render + html
    uv run --extra slides manim-slides present $(python -m dkvis.build_slides sine-theta --list)

The story:

1. a symmetric matrix is an ellipse, and its axes are the eigenvectors;
2. perturbing it barely moves the eigenvalues but can turn the axes, and
   without an eigenvalue gap the turn can be 45 degrees however small the
   perturbation;
3. the three ingredients: the angle ``sin Theta0``, the residual ``R``, the gap
   ``delta``;
4. the theorem ``delta ||sin Theta0|| <= ||R||``;
5. why it holds (one vector, then the Sylvester equation), why the constant is
   sharp, what it says about perturbations, and what the Lean theorem states.

All numbers shown come from :mod:`dkvis.sine_theta_story` and
:mod:`dkvis.sine_theta`, whose models are checked by the test suite.
"""

from __future__ import annotations

import math as pymath

import numpy as np
from manim import (
    LaggedStart,
    RoundedRectangle,
    Text,
    DOWN,
    LEFT,
    ORIGIN,
    RIGHT,
    TAU,
    UL,
    UP,
    UR,
    Arc,
    Arrow,
    Axes,
    BraceBetweenPoints,
    Create,
    DashedVMobject,
    DecimalNumber,
    Dot,
    FadeIn,
    FadeOut,
    GrowFromEdge,
    Line,
    ParametricFunction,
    Rectangle,
    ReplacementTransform,
    Transform,
    Triangle,
    ValueTracker,
    VGroup,
    VMobject,
    always_redraw,
    rate_functions,
)

from dkvis import sine_theta_story as story
from dkvis.sine_theta import SineThetaModel
from dkvis.slide_style import (
    EXACT,
    FAINT,
    FG,
    GAP,
    MUTED,
    PANEL,
    RESID,
    SINE,
    TRIAL,
    DeckSlide,
    MONO_FONT,
    boxed,
    math,
    mono,
    para,
    tex,
)

# ----------------------------------------------------------------------------
# Drawing helpers
# ----------------------------------------------------------------------------

RIGHT_COL_X = 0.75
RIGHT_COL_W = 6.0


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


def ellipse(plane: Plane, M: np.ndarray, color: str = FG, width: float = 3.0) -> ParametricFunction:
    return ParametricFunction(
        lambda t: plane(M @ np.array([np.cos(t), np.sin(t)])),
        t_range=[0, TAU],
        color=color,
        stroke_width=width,
    )


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


def live(getter, decimals: int = 3, size: float = 30, color: str = FG, unit: str | None = None) -> DecimalNumber:
    num = DecimalNumber(
        getter(), num_decimal_places=decimals, font_size=size, color=color, unit=unit
    )
    num.add_updater(lambda m: m.set_value(getter()))
    return num


def readout_rows(rows, size: float = 30, buff: float = 0.22) -> VGroup:
    """Rows of ``(label_tex, getter, color, decimals, unit)``; values align in a column."""
    labels = VGroup(*[math(lbl, size=size, color=color) for lbl, _, color, _, _ in rows])
    labels.arrange(DOWN, aligned_edge=RIGHT, buff=buff)
    values = VGroup()
    for label, (_, getter, color, decimals, unit) in zip(labels, rows):
        value = live(getter, decimals=decimals, size=size, color=color, unit=unit)
        value.next_to(label, RIGHT, buff=0.2)
        value.add_updater(lambda m, label=label: m.next_to(label, RIGHT, buff=0.2))
        values.add(value)
    return VGroup(labels, values)


RIGHT_LIMIT = 6.85


def fit_right(mob, right: float = RIGHT_LIMIT):
    """Shrink ``mob`` about its left edge if it would cross ``right``."""
    overflow = mob.get_right()[0] - right
    if overflow > 0:
        mob.scale((mob.width - overflow) / mob.width, about_edge=LEFT)
    return mob


def column(*mobs, top: float, x: float = RIGHT_COL_X, buff: float = 0.35) -> VGroup:
    group = VGroup(*mobs).arrange(DOWN, aligned_edge=LEFT, buff=buff)
    group.move_to([x, top, 0], aligned_edge=UP + LEFT)
    for mob in mobs:
        fit_right(mob)
    return group


def text_col(body: str, size: float = 28, width: float = RIGHT_COL_W, color: str = FG) -> VMobject:
    return para(body, width=width, size=size, color=color)


# ----------------------------------------------------------------------------
# 0. Title
# ----------------------------------------------------------------------------


class S00Title(DeckSlide):
    section = ""
    show_depth_legend = True

    def body(self) -> None:
        self.say(
            "Title. The question for the whole talk: when a symmetric matrix is "
            "perturbed, how far can its eigenvectors turn? Davis and Kahan (1970) "
            "answer it with four theorems; this deck is about the first, the sin Theta theorem."
        )
        title = tex(r"How far can an eigenvector turn?", size=64).move_to(UP * 1.9)
        sub = tex(r"The Davis--Kahan $\sin\Theta$ theorem, in pictures", size=38, color=MUTED)
        sub.next_to(title, DOWN, buff=0.35)
        ref = tex(
            r"C.~Davis and W.~M.~Kahan, \emph{The rotation of eigenvectors by a perturbation.~III},"
            r" SIAM J.~Numer.~Anal.~7 (1970)",
            size=22,
            color=MUTED,
        ).to_edge(DOWN, buff=0.55)

        plane = Plane(ORIGIN + DOWN * 1.35, 0.62, rotate=np.radians(18))
        pair = story.PerturbedPair(gap=0.5, eps=0.3)
        old = ellipse(plane, pair.A, color=MUTED, width=2)
        new = ellipse(plane, pair.perturbed, color=FG, width=3)
        axis_old = through_origin(plane, [1, 0], 2.6, MUTED, width=2)
        axis_new = through_origin(plane, pair.perturbed_top_eigenvector, 2.6, EXACT, width=4)
        arc = angle_arc(plane, [1, 0], pair.perturbed_top_eigenvector, 1.6, SINE, width=4)
        theta = math(r"\theta", size=32, color=SINE).move_to(
            plane(2.05 * story.unit(pair.theta / 2 - 0.08))
        )
        self.play(FadeIn(title, shift=DOWN * 0.2), FadeIn(sub))
        self.play(Create(old), Create(axis_old), run_time=1.0)
        self.play(
            ReplacementTransform(old.copy(), new),
            ReplacementTransform(axis_old.copy(), axis_new),
            run_time=1.4,
        )
        self.play(Create(arc), FadeIn(theta), FadeIn(ref))
        if self.show_depth_legend:
            legend = tex(
                r"Unmarked slides form the core talk; $\ast$ marks optional technical depth, $\ast\ast$ backup.",
                size=20,
                color=MUTED,
            ).next_to(ref, UP, buff=0.18)
            self.play(FadeIn(legend), run_time=0.5)


class S00TitleShort(S00Title):
    """The title slide of the short deck, which has no optional slides."""

    show_depth_legend = False


# ----------------------------------------------------------------------------
# 0b. The setting
# ----------------------------------------------------------------------------


class S00bSetting(DeckSlide):
    title = "The setting: self-adjoint operators"
    kicker = r"A real symmetric matrix is the simplest instance, but not the only one"

    def body(self) -> None:
        levels = [
            (r"unbounded self-adjoint operators, e.g.\ $-\tfrac{d^2}{dx^2}$, quantum Hamiltonians", MUTED),
            (r"bounded self-adjoint operators on a Hilbert space, any dimension", MUTED),
            (r"complex Hermitian matrices, $\ A=A^{*}$", FG),
            (r"real symmetric matrices, $\ A=A^{\mathsf T}$", EXACT),
        ]
        # Explicit nesting: (left, right, top, bottom) of each box.
        x_l, x_r = -6.8, 0.25
        tops = [self.content_top - 0.15, self.content_top - 1.05, self.content_top - 1.55, self.content_top - 2.05]
        bottoms = [-3.35, -3.15, -2.95, -2.75]
        boxes, labels = VGroup(), VGroup()
        for i, (label, color) in enumerate(levels):
            left, right = x_l + 0.25 * i, x_r - 0.25 * i
            box = RoundedRectangle(
                corner_radius=0.18,
                width=right - left,
                height=tops[i] - bottoms[i],
                stroke_color=color,
                stroke_width=2.6 if i == 3 else 1.8,
                fill_color=EXACT,
                fill_opacity=0.12 if i == 3 else 0.0,
            ).move_to([(left + right) / 2, (tops[i] + bottoms[i]) / 2, 0])
            lab = tex(label, size=22, color=color)
            lab.move_to([left + 0.2, tops[i] - 0.25, 0], aligned_edge=LEFT)
            if lab.width > right - left - 0.35:
                lab.scale((right - left - 0.35) / lab.width, about_edge=LEFT)
            boxes.add(box)
            labels.add(lab)
        outer_note = tex(r"$\uparrow$ the scope of Davis--Kahan (1970) and of our Lean theorem", size=22, color=FG)
        outer_note.move_to([x_l + 0.2, tops[0] - 0.6, 0], aligned_edge=LEFT)
        inner = boxes[3]
        mini = math(r"A=\begin{pmatrix}2&0.3\\0.3&1\end{pmatrix}", size=30, color=EXACT).move_to(
            inner.get_center() + np.array([0, 0.1, 0])
        )
        pictures = tex(r"every picture in this talk: $2\times2$ and $3\times3$", size=22, color=EXACT).move_to(
            [inner.get_center()[0], bottoms[3] + 0.35, 0]
        )

        x0, w = 0.75, 6.1
        t1 = para(
            r"Throughout, $A$ is \textbf{self-adjoint}: $\langle Ax,y\rangle=\langle x,Ay\rangle$ for all $x,y$. "
            r"For a real matrix that just means \emph{symmetric}, $A=A^{\mathsf T}$.",
            width=w,
            size=27,
        )
        t2 = para(
            r"Such an $A$ has real eigenvalues and, in finite dimensions, \emph{perpendicular} eigenvectors "
            r"(the spectral theorem): it is a pure stretch along perpendicular axes. In infinite dimensions "
            r"the same role is played by \emph{spectral subspaces}.",
            width=w,
            size=27,
        )
        t3 = para(
            r"Where it shows up: covariance matrices (PCA), graph Laplacians (spectral clustering), "
            r"Hamiltonians in quantum mechanics, vibration modes. The eigenspaces carry the meaning, "
            r"and the operator is only ever known approximately.",
            width=w,
            size=25,
            color=MUTED,
        )
        col = VGroup(t1, t2, t3).arrange(DOWN, aligned_edge=LEFT, buff=0.4)
        col.move_to([x0, self.content_top - 0.25, 0], aligned_edge=UP + LEFT)

        self.say(
            "First, the setting. Everything today is about self-adjoint operators: <Ax, y> = <x, Ay>. "
            "For a real matrix that is just a symmetric matrix. That is the innermost box here."
        )
        self.play(FadeIn(boxes[3]), FadeIn(labels[3]), FadeIn(mini), FadeIn(t1))

        self.say(
            "Self-adjoint operators are pure stretches along perpendicular axes: real eigenvalues, "
            "orthogonal eigenvectors. The class grows: complex Hermitian matrices, bounded operators "
            "on a Hilbert space of any dimension, and unbounded ones like differential operators."
        )
        self.play(
            LaggedStart(*[FadeIn(VGroup(boxes[i], labels[i])) for i in (2, 1, 0)], lag_ratio=0.4),
            FadeIn(t2),
            run_time=2.0,
        )

        self.say(
            "All the pictures in this talk live in the innermost box, 2 by 2 and 3 by 3 real symmetric "
            "matrices. Davis and Kahan, and our Lean theorem, cover the outermost box. And these objects "
            "are everywhere: covariance matrices, graph Laplacians, quantum Hamiltonians."
        )
        self.play(FadeIn(pictures), FadeIn(outer_note), FadeIn(t3))


# ----------------------------------------------------------------------------
# 1. A symmetric matrix is an ellipse
# ----------------------------------------------------------------------------

ELLIPSE_BASE = np.radians(20.0)


class S01Ellipse(DeckSlide):
    title = "Picturing a symmetric matrix"
    kicker = "For a positive-definite matrix, the unit circle maps to an ellipse"

    def body(self) -> None:
        lam1, lam2 = story.ELLIPSE_EIGENVALUES
        plane = Plane([-3.3, -0.75, 0], 1.25, rotate=ELLIPSE_BASE)
        A = np.diag([lam1, lam2])

        self.say(
            "Picture a symmetric matrix by what it does to the unit circle. This example is "
            "positive definite, with eigenvalues 2 and 1. Grey arrows are arbitrary unit "
            "vectors, blue arrows the two eigenvectors."
        )
        circle = ellipse(plane, np.eye(2), color=MUTED, width=2)
        sample_dirs = [story.unit(np.radians(22.5 + 45 * k)) for k in range(8)]
        samples = VGroup(*[vec(plane.origin, plane(d), FG, width=3).set_opacity(0.55) for d in sample_dirs])
        f1, f2 = np.array([1.0, 0.0]), np.array([0.0, 1.0])
        eig_lines = VGroup(
            through_origin(plane, f1, 2.6, EXACT, width=2, opacity=0.35),
            through_origin(plane, f2, 2.3, EXACT, width=2, opacity=0.35),
        )
        e1 = vec(plane.origin, plane(f1), EXACT, width=7)
        e2 = vec(plane.origin, plane(f2), EXACT, width=7)
        intro = text_col(
            r"Take this positive-definite example, $A$ with eigenvalues $2$ and $1$, "
            r"and watch where it sends the unit circle."
        )
        turned = text_col(
            r"Most vectors are stretched \emph{and turned}.\\[0.5em]"
            r"Eigenvectors are only stretched: "
            r"$A\cx{exact}{f_i}=\lambda_i\cx{exact}{f_i}$."
        )
        axes_text = text_col(
            r"The ellipse's axes point along the \cx{exact}{eigenvectors}; in this example "
            r"the semi-axis lengths are the eigenvalues $2$ and $1$.\\[0.5em]"
            r"\cx{muted}{(For a general symmetric matrix the semi-axes are $|\lambda_i|$. "
            r"In $n$ dimensions the picture is an ellipsoid, and an \emph{eigenspace} "
            r"is spanned by some of its principal axes.)}"
        )
        column(intro, turned, axes_text, top=self.content_top - 0.2, buff=0.5)
        self.play(Create(circle), FadeIn(eig_lines), run_time=1.0)
        self.play(FadeIn(samples), FadeIn(e1), FadeIn(e2), FadeIn(intro))

        self.say(
            "Apply A. Generic vectors are stretched and turned. The eigenvectors are "
            "only stretched: A f = lambda f."
        )
        image = ellipse(plane, A, color=FG, width=3)
        new_samples = VGroup(*[vec(plane.origin, plane(A @ d), FG, width=3).set_opacity(0.55) for d in sample_dirs])
        new_e1 = vec(plane.origin, plane(lam1 * f1), EXACT, width=7)
        new_e2 = vec(plane.origin, plane(lam2 * f2), EXACT, width=7)
        self.play(
            ReplacementTransform(circle, image),
            ReplacementTransform(samples, new_samples),
            ReplacementTransform(e1, new_e1),
            ReplacementTransform(e2, new_e2),
            FadeIn(turned),
            run_time=2.0,
        )

        self.say(
            "So the ellipse's axes point along the eigenvectors, and here the semi-axis lengths "
            "are the eigenvalues. For a general symmetric matrix they are the absolute values. "
            "In n dimensions it is an ellipsoid, and an eigenspace is spanned by principal axes."
        )
        l1 = math(r"\lambda_1 = 2", size=32, color=EXACT).next_to(plane(lam1 * f1), RIGHT, buff=0.12)
        l2 = math(r"\lambda_2 = 1", size=32, color=EXACT).next_to(plane(lam2 * f2), UP, buff=0.12)
        self.play(FadeOut(new_samples), FadeIn(l1), FadeIn(l2), FadeIn(axes_text))


# ----------------------------------------------------------------------------
# 2. Perturb it
# ----------------------------------------------------------------------------


class S02Perturb(DeckSlide):
    title = "Perturb the matrix"
    kicker = r"$A \to A+H$ with $H$ small and symmetric"

    def body(self) -> None:
        eps = story.PERTURBATION_EPS
        gap = story.PERTURBATION_START_GAP
        pair = story.PerturbedPair(gap=gap, eps=eps)
        pair.verify()
        plane = Plane([-3.3, -0.75, 0], 1.25, rotate=ELLIPSE_BASE)

        self.say(
            "Start from the same ellipse, drawn with its axes. Now add a small symmetric H."
        )
        old = ellipse(plane, pair.A, color=MUTED, width=2)
        old_axis = through_origin(plane, [1, 0], 3.0, EXACT, width=3)
        old_axis2 = through_origin(plane, [0, 1], 2.0, EXACT, width=3)
        eq = math(
            r"A=\begin{pmatrix}2&0\\0&1\end{pmatrix},\qquad "
            r"H=\varepsilon\begin{pmatrix}0&1\\1&0\end{pmatrix},\ \ \varepsilon=0.12",
            size=30,
        )
        basis_note = tex(r"(written in the eigenbasis of $A$)", size=22, color=MUTED)
        l_old = pair.A.diagonal()
        l_new = pair.perturbed_eigenvalues
        table = math(
            r"\begin{array}{lcc}"
            r" & \lambda_1 & \lambda_2\\ \hline "
            rf"A & {l_old[0]:.3f} & {l_old[1]:.3f}\\"
            rf"A+H & {l_new[0]:.3f} & {l_new[1]:.3f}"
            r"\end{array}",
            size=30,
        )
        weyl = tex(
            rf"Eigenvalues moved by ${pair.eigenvalue_shift:.3f} \le \norm{{H}}_2 = {eps}$ (Weyl).",
            size=26,
        )
        turn = tex(
            rf"Eigenvectors turned by \cx{{sine}}{{$\theta = {pymath.degrees(pair.theta):.1f}^\circ$}}.",
            size=26,
        )
        question = boxed(tex(r"How far can an eigenvector turn?", size=32), color=SINE)
        column(eq, basis_note, table, weyl, turn, question, top=self.content_top - 0.2, buff=0.32)
        basis_note.next_to(eq, DOWN, aligned_edge=LEFT, buff=0.12)
        self.play(Create(old), Create(old_axis), Create(old_axis2), FadeIn(eq), FadeIn(basis_note))

        self.say(
            "The ellipse of A + H is almost the same ellipse: the eigenvalues barely "
            "move. Weyl's inequality says they move by at most the norm of H. "
            "But the axes turn, by an angle theta."
        )
        new = ellipse(plane, pair.perturbed, color=FG, width=3)
        v_new = pair.perturbed_top_eigenvector
        w_new = np.array([-v_new[1], v_new[0]])
        new_axis = through_origin(plane, v_new, 3.0, EXACT, width=4)
        new_axis2 = through_origin(plane, w_new, 2.0, EXACT, width=4)
        dashed_old = VGroup(
            DashedVMobject(through_origin(plane, [1, 0], 3.0, MUTED, width=2), num_dashes=30),
            DashedVMobject(through_origin(plane, [0, 1], 2.0, MUTED, width=2), num_dashes=20),
        )
        arc = angle_arc(plane, [1, 0], v_new, 2.9, SINE, width=4)
        theta = math(r"\theta", size=34, color=SINE).move_to(plane(3.25 * story.unit(pair.theta / 2)))
        self.play(
            ReplacementTransform(old_axis, dashed_old[0]),
            ReplacementTransform(old_axis2, dashed_old[1]),
            TransformFromCopySafe(old, new),
            Create(new_axis),
            Create(new_axis2),
            run_time=1.6,
        )
        self.play(Create(arc), FadeIn(theta), FadeIn(table), FadeIn(weyl), FadeIn(turn))

        self.say(
            "That is the question of the talk. Eigenvalue perturbation is easy "
            "(Weyl). How far can the eigenvectors, or more generally an invariant "
            "subspace, turn?"
        )
        self.play(FadeIn(question, shift=UP * 0.15))


def TransformFromCopySafe(source, target, **kwargs):
    """Grow ``target`` out of a copy of ``source`` (``source`` stays on screen)."""
    return ReplacementTransform(source.copy(), target, **kwargs)


# ----------------------------------------------------------------------------
# 3. No gap, no stability
# ----------------------------------------------------------------------------


class S03NoGap(DeckSlide):
    title = "How far can an eigenvector turn? It depends on whether there is a gap"
    kicker = r"Without a gap, eigenvectors are unstable"

    def body(self) -> None:
        eps = story.PERTURBATION_EPS
        g_start, g_end = story.PERTURBATION_START_GAP, story.PERTURBATION_END_GAP
        g = ValueTracker(g_start)
        plane = Plane([-3.75, -0.25, 0], 1.1, rotate=ELLIPSE_BASE)

        def pair() -> story.PerturbedPair:
            return story.PerturbedPair(gap=g.get_value(), eps=eps)

        def lam() -> tuple[float, float]:
            l1, l2 = pair().A.diagonal()
            return float(l1), float(l2)

        # A: dashed blue ellipse and its eigenvectors, arrows as long as the eigenvalues.
        old = always_redraw(
            lambda: DashedVMobject(ellipse(plane, pair().A, color=EXACT, width=2), num_dashes=60).set_opacity(0.8)
        )
        f1 = always_redraw(lambda: vec(plane.origin, plane([lam()[0], 0.0]), EXACT, width=6))
        f2 = always_redraw(lambda: vec(plane.origin, plane([0.0, lam()[1]]), EXACT, width=6))
        f1_lbl = always_redraw(lambda: math(r"\lambda_1", size=28, color=EXACT).next_to(plane([lam()[0], 0.0]), DOWN, buff=0.08))
        f2_lbl = always_redraw(lambda: math(r"\lambda_2", size=28, color=EXACT).next_to(plane([0.0, lam()[1]]), LEFT, buff=0.08))
        # A + H: solid white ellipse and its top eigenvector, which turns by theta.
        new = always_redraw(lambda: ellipse(plane, pair().perturbed, color=FG, width=3))
        new_axis = always_redraw(lambda: through_origin(plane, pair().perturbed_top_eigenvector, 2.3, FG, width=3))
        new_lbl = always_redraw(
            lambda: tex(r"$A+H$", size=22, color=FG).next_to(plane(2.3 * pair().perturbed_top_eigenvector), UR, buff=0.05)
        )
        arc = always_redraw(lambda: angle_arc(plane, [1, 0], pair().perturbed_top_eigenvector, 0.95, SINE, width=4))
        theta_lbl = always_redraw(
            lambda: math(r"\theta", size=30, color=SINE).move_to(plane(1.2 * story.unit(max(pair().theta, 0.14) / 2)))
        )

        # The eigenvalues of A on a number line, with the gap between them.
        lo, hi, x_lo, x_hi, y_nl = 0.75, 2.25, -6.4, -1.1, -3.0

        def X(v: float) -> np.ndarray:
            return np.array([x_lo + (v - lo) / (hi - lo) * (x_hi - x_lo), y_nl, 0.0])

        nl = Line(X(lo), X(hi), color=MUTED, stroke_width=2)
        nl_lbl = VGroup(
            tex(r"eigenvalues", size=20, color=MUTED),
            tex(r"\cx{exact}{dots: $A$} \ \cx{fg}{ticks: $A+H$}", size=18, color=MUTED),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.04).next_to(X(hi), RIGHT, buff=0.1)
        lam_dots = always_redraw(lambda: VGroup(*[Dot(X(v), radius=0.09, color=EXACT) for v in lam()]))
        lam_lbls = always_redraw(
            lambda: VGroup(
                math(r"\lambda_2", size=24, color=EXACT).next_to(X(lam()[1]), DOWN, buff=0.12).shift(LEFT * 0.12),
                math(r"\lambda_1", size=24, color=EXACT).next_to(X(lam()[0]), DOWN, buff=0.12).shift(RIGHT * 0.12),
            )
        )
        new_ticks = always_redraw(
            lambda: VGroup(
                *[Line(X(v) + UP * 0.16, X(v) + DOWN * 0.16, color=FG, stroke_width=3) for v in pair().perturbed_eigenvalues]
            )
        )

        def gap_marker():
            l1, l2 = lam()
            a, b = X(l2) + UP * 0.2, X(l1) + UP * 0.2
            if b[0] - a[0] > 0.3:
                mark = BraceBetweenPoints(a, b, direction=UP, color=GAP)
            else:
                mark = Line(a + UP * 0.1, b + UP * 0.1, color=GAP, stroke_width=4)
            label = tex(r"gap $g$", size=24, color=GAP).next_to(mark, UP, buff=0.06)
            return VGroup(mark, label)

        gap = always_redraw(gap_marker)

        axes = Axes(
            x_range=[0, 1.0, 0.25],
            y_range=[0, 45, 15],
            x_length=4.6,
            y_length=2.6,
            tips=False,
            axis_config={"color": MUTED, "stroke_width": 2, "include_ticks": True},
        ).move_to([4.0, 0.55, 0])
        x_lbl = math(r"g", size=28, color=MUTED).next_to(axes.x_axis, RIGHT, buff=0.15)
        y_lbl = math(r"\theta\ (\text{deg})", size=26, color=MUTED).next_to(axes.y_axis, UP, buff=0.3)
        y_ticks = VGroup(*[math(str(v), size=22, color=MUTED).next_to(axes.c2p(0, v), LEFT, buff=0.1) for v in (15, 30, 45)])
        x_ticks = VGroup(*[math(f"{v:g}", size=22, color=MUTED).next_to(axes.c2p(v, 0), DOWN, buff=0.1) for v in (0.5, 1.0)])
        curve = axes.plot(
            lambda x: pymath.degrees(story.PerturbedPair(gap=x, eps=eps).theta),
            x_range=[0.005, 1.0],
            color=SINE,
            stroke_width=3,
        )
        dot = always_redraw(lambda: Dot(axes.c2p(g.get_value(), pymath.degrees(pair().theta)), color=SINE, radius=0.07))
        rows = readout_rows(
            [
                (r"g =", lambda: g.get_value(), FG, 2, None),
                (r"\norm{H}_2 =", lambda: eps, FG, 2, None),
                (r"\max|\Delta\lambda| =", lambda: pair().eigenvalue_shift, FG, 3, None),
                (r"\theta =", lambda: pymath.degrees(pair().theta), SINE, 1, r"^\circ"),
            ],
            size=28,
        )
        rows.move_to([3.6, -2.35, 0])

        self.say(
            "Blue: A, drawn as its ellipse with its two eigenvectors, each arrow as long as its eigenvalue. "
            "Below, the same two eigenvalues on a number line; the violet bracket is the gap g between them. "
            "White: A + H for a fixed small H, with its top eigenvector, turned by theta. "
            "Right: theta as a function of the gap."
        )
        left = VGroup(old, f1, f2, f1_lbl, f2_lbl, new, new_axis, new_lbl, arc, theta_lbl, nl, nl_lbl, lam_dots, lam_lbls, new_ticks, gap)
        self.add(left)
        self.play(
            FadeIn(left),
            Create(axes),
            FadeIn(x_lbl, y_lbl, y_ticks, x_ticks),
            Create(curve),
            FadeIn(rows),
        )
        self.add(dot)

        self.say(
            "Now make A more and more round: its two eigenvalues slide together and the gap closes. "
            "The white ticks, the eigenvalues of A + H, never move more than 0.12 from the blue dots. "
            "But the eigenvector of A + H swings toward 45 degrees, however small H is."
        )
        self.play(g.animate.set_value(g_end), run_time=6.0, rate_func=rate_functions.ease_in_out_sine)

        self.say(
            "The classic example: diag(1+eps, 1-eps) versus [[1, eps],[eps, 1]]. Every "
            "eps > 0 gives a 45-degree turn. So a gap is necessary; the sin Theta theorem "
            "says it is also sufficient, quantitatively."
        )
        msg = para(
            r"Eigenvalues are stable.\\ Eigenvectors are stable only \emph{with a gap}.",
            width=RIGHT_COL_W,
            size=32,
        )
        classic_note = tex(r"the classic example: for every $\varepsilon>0$", size=24, color=MUTED)
        classic = math(
            r"\begin{pmatrix}1+\varepsilon&0\\0&1-\varepsilon\end{pmatrix}"
            r"\ \longrightarrow\ "
            r"\begin{pmatrix}1&\varepsilon\\ \varepsilon&1\end{pmatrix}"
            r"\qquad \cx{sine}{\theta = 45^\circ}",
            size=30,
        )
        takeaway = column(msg, classic_note, classic, top=self.content_top - 0.4, x=RIGHT_COL_X + 0.2, buff=0.3)
        plot = VGroup(axes, x_lbl, y_lbl, y_ticks, x_ticks, curve, dot)
        self.play(FadeOut(plot))
        self.play(FadeIn(takeaway, shift=UP * 0.1))


# ----------------------------------------------------------------------------
# 4. Measuring the angle
# ----------------------------------------------------------------------------


class S04Angle(DeckSlide):
    title = "Measuring how far a subspace moved"
    kicker = r"Angles between subspaces, and the operator $\sin\Theta_0$"

    def body(self) -> None:
        th = ValueTracker(np.radians(35.0))
        plane = Plane([-4.6, -2.2, 0], 3.3)

        def model() -> SineThetaModel:
            return SineThetaModel(th.get_value())

        U = through_origin(plane, [1, 0], 1.25, EXACT, width=4)
        U.put_start_and_end_on(plane([-0.35, 0]), plane([1.25, 0]))
        U_lbl = math(r"U", size=36, color=EXACT).next_to(plane([1.25, 0]), DOWN, buff=0.15)
        V = always_redraw(
            lambda: Line(plane(-0.3 * model().trial_vector), plane(1.25 * model().trial_vector), color=TRIAL, stroke_width=3).set_opacity(0.6)
        )
        V_lbl = always_redraw(lambda: math(r"V", size=36, color=TRIAL).next_to(plane(1.25 * model().trial_vector), UP, buff=0.1))
        v = always_redraw(lambda: vec(plane.origin, plane(model().trial_vector), TRIAL, width=7))
        v_lbl = always_redraw(
            lambda: math(r"v", size=34, color=TRIAL).next_to(plane(model().trial_vector), UL, buff=0.05)
        )
        arc = always_redraw(lambda: angle_arc(plane, [1, 0], model().trial_vector, 0.9, FG, width=3))
        th_lbl = always_redraw(
            lambda: math(r"\theta", size=32).move_to(plane(0.36 * story.unit(model().theta / 2)))
        )

        self.say(
            "Blue: the true subspace U (here a line). Amber: a trial subspace V, "
            "spanned by the unit vector v. theta is the angle between them."
        )
        self.play(Create(U), FadeIn(U_lbl))
        self.add(V, V_lbl, v, v_lbl, arc, th_lbl)
        self.play(FadeIn(VGroup(V, V_lbl, v, v_lbl, arc, th_lbl)))

        self.say(
            "Split v into its part in U and its part orthogonal to U. The orthogonal part "
            "has length sin theta: it is the distance from v to U."
        )
        proj = always_redraw(lambda: segment(plane.origin, plane(model().desired_projection), MUTED, width=5))
        perp = always_redraw(lambda: segment(plane(model().desired_projection), plane(model().trial_vector), SINE, width=8))
        corner = always_redraw(
            lambda: right_angle(plane(model().desired_projection), [-1, 0], [0, 1], size=0.16)
        )
        perp_lbl = always_redraw(
            lambda: math(r"\sin\theta", size=32, color=SINE).next_to(
                plane((model().desired_projection + model().trial_vector) / 2), RIGHT, buff=0.12
            )
        )
        proj_lbl = always_redraw(
            lambda: math(r"P_U v", size=28, color=MUTED).next_to(plane(model().desired_projection / 2), DOWN, buff=0.12)
        )
        f1 = math(r"\cx{sine}{\sin\theta} = \norm{(I-P_U)\,\cx{trial}{v}} = \operatorname{dist}(\cx{trial}{v},\cx{exact}{U})", size=32)
        column(f1, top=self.content_top - 0.25)
        self.add(proj, perp, corner, perp_lbl, proj_lbl)
        self.play(FadeIn(VGroup(proj, perp, corner, perp_lbl, proj_lbl)), FadeIn(f1))

        self.say(
            "Move V around: the pink leg is the size of the error. It vanishes exactly "
            "when V = U and is 1 when V is orthogonal to U. (This build loops.)",
            loop=True,
        )
        self.play(th.animate.set_value(np.radians(70)), run_time=2.2, rate_func=rate_functions.ease_in_out_sine)
        self.play(th.animate.set_value(np.radians(8)), run_time=3.0, rate_func=rate_functions.ease_in_out_sine)
        self.play(th.animate.set_value(np.radians(35)), run_time=1.8, rate_func=rate_functions.ease_in_out_sine)

        self.say(
            "Same idea for k-dimensional subspaces: there are k principal angles, and "
            "sin Theta0 is the operator whose eigenvalues are their sines. The rectangular "
            "blocks (I - F0 F0*) E0 and F1* E0 have exactly the same singular values, so they "
            "have the same size in every unitarily invariant norm; proofs compute with them."
        )
        general = text_col(
            r"For $k$-dimensional subspaces there are $k$ \emph{principal angles} "
            r"$\theta_1\ge\dots\ge\theta_k$, and"
        )
        definition = boxed(
            para(
                r"$\cx{sine}{\sin\Theta_0}$ is the operator whose eigenvalues are "
                r"$\sin\theta_1,\dots,\sin\theta_k$.",
                width=RIGHT_COL_W - 0.5,
                size=28,
            ),
            color=SINE,
            pad=0.18,
        )
        g_eq = math(
            r"\norm{\cx{sine}{\sin\Theta_0}} = \norm{(I-\cx{exact}{F_0F_0^{*}})\,\cx{trial}{E_0}}"
            r"= \norm{\cx{exact}{F_1}^{*}\cx{trial}{E_0}}",
            size=32,
        )
        g_note = para(
            r"The rectangular blocks have the same singular values as $\sin\Theta_0$, hence the same "
            r"size in every unitarily invariant norm, e.g.\ "
            r"$\norm{\sin\Theta_0}_{2}=\sin\theta_1$, $\ \norm{\sin\Theta_0}_{F}=(\sum_i\sin^2\theta_i)^{1/2}$.",
            width=RIGHT_COL_W,
            size=24,
            color=MUTED,
        )
        legend = tex(
            r"\cx{trial}{$E_0$}: trial basis, \ \cx{exact}{$F_0$}: basis of $U$,"
            r" \ \cx{exact}{$F_1$}: basis of $U^\perp$",
            size=24,
            color=MUTED,
        )
        column(f1, general, definition, g_eq, g_note, legend, top=self.content_top - 0.25, buff=0.28)
        self.play(FadeIn(VGroup(general, definition, g_eq, g_note, legend), shift=UP * 0.1))


class S04bSinThetaOperator(DeckSlide):
    title = r"What $\sin\Theta_0$ is, exactly"
    kicker = "The operator in the theorem, and the block the proof computes with"
    depth = "*"

    def body(self) -> None:
        x0, w = -6.5, 13.0
        top = self.content_top - 0.3

        notes1 = (
            "The paper defines the angle operator from the cosines. On the trial coordinates, "
            "E0* F0 F0* E0 has eigenvalues cos^2 theta_i; Theta0 is its arccos square root, and "
            "sin Theta0 is sine applied to that operator: eigenvalues sin theta_i."
        )
        cos_line = math(
            r"\cos^2\Theta_0=\cx{trial}{E_0}^{*}\cx{exact}{F_0F_0^{*}}\cx{trial}{E_0},\qquad"
            r"\Theta_0=\arccos\sqrt{\cx{trial}{E_0}^{*}\cx{exact}{F_0F_0^{*}}\cx{trial}{E_0}},\qquad"
            r"\cx{sine}{\sin\Theta_0}=\sin(\Theta_0)",
            size=34,
        )
        cos_note = tex(
            r"operators on the trial coordinates (Davis--Kahan (1.16)); eigenvalues "
            r"$\cos^2\theta_i$, $\theta_i$, $\sin\theta_i$",
            size=24,
            color=MUTED,
        )

        notes2 = (
            "The rectangular block S = (I - F0 F0*) E0 satisfies S* S = I - E0* F0 F0* E0 = sin^2 Theta0, "
            "so its modulus |S| is exactly sin Theta0. Same singular values, so the same value in "
            "every unitarily invariant norm. The same holds for F1* E0, because F1 F1* = I - F0 F0*."
        )
        s_line = math(
            r"S=(I-\cx{exact}{F_0F_0^{*}})\cx{trial}{E_0}:\qquad "
            r"S^{*}S=I-\cx{trial}{E_0}^{*}\cx{exact}{F_0F_0^{*}}\cx{trial}{E_0}=\cx{sine}{\sin^2\Theta_0}"
            r"\quad\Longrightarrow\quad |S|=\cx{sine}{\sin\Theta_0}",
            size=34,
        )
        s_note = para(
            r"So $S$ (and $\cx{exact}{F_1}^{*}\cx{trial}{E_0}$, since $F_1F_1^{*}=I-F_0F_0^{*}$) has the "
            r"singular values $\sin\theta_i$ and the same value as $\sin\Theta_0$ in every unitarily "
            r"invariant norm. The operator is the \emph{statement}; the block is what a proof can compute with.",
            width=w,
            size=26,
        )

        notes3 = (
            "In Lean the theorem is stated on the literal sin Theta0: sourceDirectedSinThetaOperator, "
            "defined as cfc sin of an angle operator reconstructed from |S|. The bridge theorem "
            "sourceDirectedSinThetaOperator_eq_modulus proves it equals |S|, and the analysis runs on S."
        )
        lean = VGroup(
            tex(r"In Lean:", size=26, color=MUTED),
            mono("sourceDirectedSinThetaOperator E₀ F₀  :=  cfc sin Θ₀,     Θ₀ := cfc arcsin |S|", size=19),
            mono("sourceDirectedSinThetaOperator_eq_modulus :  sin Θ₀ = |S|", size=19),
            para(
                r"The theorem's conclusion is stated on $\sin\Theta_0$ itself; this bridge moves it to $S$ "
                r"for the analysis. (Reconstructing $\Theta_0$ as $\arcsin|S|$ agrees with the paper's "
                r"$\arccos$ form because $S^{*}S=I-E_0^{*}F_0F_0^{*}E_0$.)",
                width=w,
                size=24,
                color=MUTED,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.16)

        blocks = VGroup(VGroup(cos_line, cos_note).arrange(DOWN, aligned_edge=LEFT, buff=0.15),
                        VGroup(s_line, s_note).arrange(DOWN, aligned_edge=LEFT, buff=0.18),
                        lean).arrange(DOWN, aligned_edge=LEFT, buff=0.5)
        blocks.move_to([x0, top, 0], aligned_edge=UP + LEFT)
        for b in blocks:
            fit_right(b)
        for notes, block in zip((notes1, notes2, notes3), blocks):
            self.say(notes)
            self.play(FadeIn(block))


# ----------------------------------------------------------------------------
# 5. The residual
# ----------------------------------------------------------------------------


class S05Residual(DeckSlide):
    """The residual, and why it is computable when the angle is not.

    The right column keeps a small "recall" panel (what A, U and v are) and swaps
    one explanation per build, so the audience never has to remember the cast.
    """

    title = "The residual: checking a guess without knowing the answer"
    kicker = r"Test the guess: does $A$ only stretch it, as it would an eigenvector?"

    def body(self) -> None:
        lam1, lam2 = story.RESIDUAL_EIGENVALUES
        phi = ValueTracker(np.radians(40.0))
        plane = Plane([-5.8, -2.6, 0], 2.55)

        def model() -> story.RayleighResidual:
            return story.RayleighResidual(lam1, lam2, phi.get_value())

        # The answer we do not have: drawn faint and dashed.
        e_lines = VGroup(
            DashedVMobject(Line(plane([-0.2, 0]), plane([2.1, 0]), color=EXACT, stroke_width=2), num_dashes=24),
            DashedVMobject(Line(plane([0, -0.1]), plane([0, 1.85]), color=EXACT, stroke_width=2), num_dashes=20),
        ).set_opacity(0.7)
        u_lbl = tex(r"$U$: true eigenvector (unknown)", size=22, color=EXACT).next_to(plane([1.2, 0]), DOWN, buff=0.15)
        v = always_redraw(lambda: vec(plane.origin, plane(model().v), TRIAL, width=7))
        v_lbl = always_redraw(lambda: math(r"v", size=32, color=TRIAL).next_to(plane(model().v), UL, buff=0.05))
        Av = always_redraw(lambda: vec(plane.origin, plane(model().Av), FG, width=5))
        Av_lbl = always_redraw(lambda: math(r"Av", size=30).next_to(plane(model().Av), RIGHT, buff=0.1))
        rho_v = always_redraw(lambda: segment(plane.origin, plane(model().rho_v), TRIAL, width=12).set_opacity(0.35))
        rho_lbl = always_redraw(lambda: math(r"\rho v", size=28, color=TRIAL).next_to(plane(model().rho_v), LEFT, buff=0.12))
        r = always_redraw(lambda: vec(plane(model().rho_v), plane(model().Av), RESID, width=7))
        r_lbl = always_redraw(
            lambda: math(r"r", size=32, color=RESID).next_to(plane((model().rho_v + model().Av) / 2), UR, buff=0.06)
        )
        arc = always_redraw(lambda: angle_arc(plane, [1, 0], model().v, 0.55, SINE, width=4))
        th_lbl = always_redraw(
            lambda: math(r"\theta", size=30, color=SINE).move_to(plane(0.72 * story.unit(max(phi.get_value(), 0.12) / 2)))
        )

        # Right column: a persistent recap, then one explanation per build.
        x0, w = RIGHT_COL_X - 0.15, RIGHT_COL_W + 0.2
        rows = [
            (
                r"$A$",
                r"the matrix whose eigenvectors we want; we can multiply any vector by it. "
                r"(In a perturbation problem: the perturbed $A+H$.)",
                FG,
            ),
            (r"$\cx{exact}{U}$", r"its true eigenvector. Any computation only ever gives an approximation of it.", EXACT),
            (r"$\cx{trial}{v}$", r"our approximation, e.g.\ from an iterative eigensolver.", TRIAL),
        ]
        recap = VGroup()
        for sym, text, color in rows:
            key = tex(sym, size=30, color=color)
            body = para(text, width=w - 1.0, size=23)
            row = VGroup(key, body).arrange(RIGHT, aligned_edge=UP, buff=0.25)
            key.align_to(body, UP).shift(DOWN * 0.02)
            recap.add(row)
        recap.arrange(DOWN, aligned_edge=LEFT, buff=0.14)
        recap_title = tex(r"Recall", size=22, color=MUTED)
        recap_box = VGroup(recap_title, recap).arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        recap_box.move_to([x0 + 0.15, self.content_top - 0.2, 0], aligned_edge=UP + LEFT)
        recap_bg = Rectangle(
            width=recap_box.width + 0.35, height=recap_box.height + 0.3, fill_color=PANEL, fill_opacity=1, stroke_width=0
        ).move_to(recap_box)
        area_top = recap_bg.get_bottom()[1] - 0.3

        def place(*mobs, buff=0.28):
            g = VGroup(*mobs).arrange(DOWN, aligned_edge=LEFT, buff=buff)
            g.move_to([x0, area_top, 0], aligned_edge=UP + LEFT)
            for m in g:
                fit_right(m)
            return g

        self.say(
            "A reminder of the cast. A is the matrix whose eigenvectors we want, and we can multiply vectors "
            "by it; in a perturbation problem it is the perturbed matrix A + H. U is its true eigenvector. "
            "We can never compute U exactly: no formula exists beyond 4 by 4, solvers iterate, matrices can be "
            "huge or infinite-dimensional. v is the approximation we have."
        )
        e1 = place(
            para(
                r"We cannot measure the error $\cx{sine}{\theta}$ of the guess directly: that needs $\cx{exact}{U}$.",
                width=w,
                size=26,
            )
        )
        self.play(FadeIn(recap_bg), FadeIn(recap_box), FadeIn(e_lines), FadeIn(u_lbl))
        self.add(v, v_lbl, arc, th_lbl)
        self.play(FadeIn(VGroup(v, v_lbl, arc, th_lbl)), FadeIn(e1))

        self.say(
            "But we can test the guess. From the ellipse slide: an eigenvector is a direction A only "
            "stretches. So multiply: if v were an eigenvector, Av would point exactly along v. Here it does not."
        )
        e2 = place(
            para(
                r"But we can \emph{test} it. An eigenvector is a direction $A$ only stretches, so apply $A$: "
                r"if $v$ were an eigenvector, $Av$ would point exactly along $v$.",
                width=w,
                size=26,
            )
        )
        self.add(Av, Av_lbl)
        self.play(FadeOut(e1), FadeIn(e2), FadeIn(VGroup(Av, Av_lbl)))

        self.say(
            "Split Av into the part along v, rho v, and the leftover r. The recipe needs one "
            "multiplication by A and one dot product. U never appears: that is why r is computable. "
            "It is exactly how iterative eigensolvers decide to stop: iterate until the residual is small."
        )
        recipe = math(
            r"\begin{aligned}&1.\ \ w=Av\\ &2.\ \ \rho=v^{*}w\\ &3.\ \ \cx{resid}{r}=w-\rho\,v\end{aligned}",
            size=32,
        )
        recipe_note = para(
            r"$\rho v$ is the part of $Av$ along $v$; the \cx{resid}{residual} $r$ is what is left over. "
            r"One multiplication and one dot product: $\cx{exact}{U}$ never appears. "
            r"This is the stopping test iterative eigensolvers use.",
            width=w - 2.0,
            size=24,
        )
        e3 = place(VGroup(recipe, recipe_note).arrange(RIGHT, aligned_edge=UP, buff=0.4))
        self.add(rho_v, rho_lbl, r, r_lbl)
        self.play(FadeOut(e2), FadeIn(e3), FadeIn(VGroup(rho_v, rho_lbl, r, r_lbl)))

        self.say(
            "Improve the guess: the angle theta and the residual shrink together, and r is zero exactly "
            "when v is an eigenvector. We can watch r; we cannot watch theta. The theorem will say how "
            "much a small r guarantees about theta."
        )
        readouts = readout_rows(
            [
                (r"\cx{sine}{\theta}\ \text{(needs } U) =", lambda: np.degrees(phi.get_value()), SINE, 1, r"^\circ"),
                (r"\norm{\cx{resid}{r}}\ \text{(needs } A, v) =", lambda: model().residual_norm, RESID, 3, None),
            ],
            size=28,
        )
        zero = tex(r"$\cx{resid}{r}=0$ exactly when $v$ is an eigenvector.", size=26)
        e4 = place(readouts, zero, buff=0.3)
        self.play(FadeOut(e3), FadeIn(e4))
        self.play(phi.animate.set_value(np.radians(6.0)), run_time=3.5, rate_func=rate_functions.ease_in_out_sine)

        self.say(
            "The same works for several trial vectors at once: E0 holds them as orthonormal columns and "
            "A0 is a small trial matrix, for instance E0* A E0. The residual is R = A E0 - E0 A0, still "
            "computable from A and the guess. The question for the theorem: does a small R force a small angle?"
        )
        block = math(r"\cx{resid}{R} = A\,\cx{trial}{E_0} - \cx{trial}{E_0}\,\cx{trial}{A_0}", size=34)
        block_note = para(
            r"several guesses at once: $\cx{trial}{E_0}$ holds them as orthonormal columns, $\cx{trial}{A_0}$ is a "
            r"small trial matrix (e.g.\ $E_0^{*}AE_0$; for one vector it is just $\rho$)",
            width=w,
            size=22,
            color=MUTED,
        )
        q = boxed(tex(r"Does a small $\cx{resid}{R}$ force a small $\cx{sine}{\sin\Theta_0}$?", size=28), color=FG)
        e5 = place(block, block_note, q, buff=0.25)
        # Freeze the live readouts first: their digit count would change mid-fade.
        e4.clear_updaters()
        self.play(FadeOut(e4), FadeIn(e5), phi.animate.set_value(np.radians(40.0)), run_time=1.5)


# ----------------------------------------------------------------------------
# 6. The gap
# ----------------------------------------------------------------------------


class S06Gap(DeckSlide):
    title = r"The gap $\delta$"
    kicker = "Where the trial spectrum sits relative to the unwanted part of the true spectrum"

    def body(self) -> None:
        g = story.gap_picture_example()
        beta, alpha, delta = g["beta"], g["alpha"], g["delta"]
        y0 = 0.9
        scale = 1.95

        def X(t: float) -> np.ndarray:
            return np.array([scale * t, y0, 0.0])

        line = Line(X(-3.2), X(3.2), color=MUTED, stroke_width=2)
        window = Rectangle(
            width=scale * (alpha - beta + 2 * delta), height=0.9, fill_color=GAP, fill_opacity=0.14, stroke_width=0
        ).move_to(X((alpha + beta) / 2))
        window_edges = VGroup(
            DashedVMobject(Line(X(beta - delta) + DOWN * 0.45, X(beta - delta) + UP * 0.45, color=GAP, stroke_width=2), num_dashes=6),
            DashedVMobject(Line(X(alpha + delta) + DOWN * 0.45, X(alpha + delta) + UP * 0.45, color=GAP, stroke_width=2), num_dashes=6),
        )
        interval = Line(X(beta), X(alpha), color=TRIAL, stroke_width=8).set_opacity(0.45)
        ritz = VGroup(*[Dot(X(a), color=TRIAL, radius=0.1) for a in g["ritz"]])
        ritz_lbl = VGroup(
            tex(r"our estimates", size=22, color=TRIAL),
            math(r"\operatorname{spec}(A_0)\subset[\beta,\alpha]", size=30, color=TRIAL),
        ).arrange(DOWN, buff=0.06).next_to(interval, UP, buff=0.4)
        ab = VGroup(
            math(r"\beta", size=28, color=TRIAL).next_to(X(beta), DOWN, buff=0.2),
            math(r"\alpha", size=28, color=TRIAL).next_to(X(alpha), DOWN, buff=0.2),
        )
        br_l = BraceBetweenPoints(X(beta - delta), X(beta), direction=DOWN, color=GAP).shift(DOWN * 0.45)
        br_r = BraceBetweenPoints(X(alpha), X(alpha + delta), direction=DOWN, color=GAP).shift(DOWN * 0.45)
        d_l = math(r"\delta", size=30, color=GAP).next_to(br_l, DOWN, buff=0.08)
        d_r = math(r"\delta", size=30, color=GAP).next_to(br_r, DOWN, buff=0.08)
        unwanted = VGroup(*[Dot(X(lam), color=EXACT, radius=0.1) for lam in g["unwanted"]])
        un_lbl_l = VGroup(
            tex(r"unwanted eigenvalues of $A$", size=22, color=EXACT),
            math(r"\operatorname{spec}(\Lambda_1)", size=30, color=EXACT),
        ).arrange(DOWN, buff=0.06).next_to(VGroup(*unwanted[:3]), UP, buff=0.4)
        un_lbl_r = VGroup(
            tex(r"unwanted eigenvalues of $A$", size=22, color=EXACT),
            math(r"\operatorname{spec}(\Lambda_1)", size=30, color=EXACT),
        ).arrange(DOWN, buff=0.06).next_to(VGroup(*unwanted[3:]), UP, buff=0.4)

        self.say(
            "The number line is the real axis of eigenvalues. Amber: the eigenvalues "
            "of the trial matrix A0, inside an interval [beta, alpha]."
        )
        self.play(Create(line), FadeIn(interval), FadeIn(ritz), FadeIn(ritz_lbl), FadeIn(ab))

        self.say(
            "Widen the interval by delta on each side: the violet window. "
            "Lambda1 is A restricted to the unwanted part U-perp. The hypothesis: no "
            "eigenvalue of Lambda1 enters the window. Everything of A inside the window "
            "belongs to U."
        )
        hyp = math(
            r"\cx{trial}{\operatorname{spec}(A_0)}\subset[\beta,\alpha],\qquad"
            r"\cx{exact}{\operatorname{spec}(\Lambda_1)}\cap(\beta-\cx{gap}{\delta},\,\alpha+\cx{gap}{\delta})=\varnothing",
            size=32,
        ).move_to([0, -1.25, 0])
        lam_note = tex(
            r"$\cx{exact}{\Lambda_1}$: $A$ restricted to $U^{\perp}$, i.e.\ $A\cx{exact}{F_1}=\cx{exact}{F_1}\cx{exact}{\Lambda_1}$."
            r"\quad Or the same with the roles of $A_0$ and $\Lambda_1$ exchanged.",
            size=24,
            color=MUTED,
        ).next_to(hyp, DOWN, buff=0.25)
        self.play(FadeIn(window), FadeIn(window_edges), FadeIn(br_l, br_r, d_l, d_r))
        self.play(FadeIn(unwanted, lag_ratio=0.15), FadeIn(un_lbl_l), FadeIn(un_lbl_r), FadeIn(hyp), FadeIn(lam_note))

        self.say(
            "Why an interval and not just 'every pair of eigenvalues is delta apart'? "
            "If the two spectra interleave, constant 1 survives only in the Frobenius "
            "norm (Davis-Kahan Theorem 6.2); in the operator norm it fails, and "
            "Section 5 of the paper gives an explicit 2x2 example."
        )
        warn = para(
            r"\cx{muted}{Why an interval?} If the spectra are merely $\delta$ apart pairwise but "
            r"\emph{interleaved}, the bound with constant $1$ holds only in the Frobenius norm "
            r"(Davis--Kahan Thm~6.2); in the operator norm it can fail (\S5).",
            width=12.2,
            size=24,
        ).move_to([0, -3.05, 0])
        self.play(FadeIn(warn))


# ----------------------------------------------------------------------------
# 7. The theorem
# ----------------------------------------------------------------------------


class S07Theorem(DeckSlide):
    title = r"The $\sin\Theta$ theorem"
    kicker = r"Davis \& Kahan (1970). $A$ is the matrix we have, e.g.\ the perturbed $A+H$"

    def body(self) -> None:
        self.say(
            "Put the three pieces together. Under the gap hypothesis, for every "
            "unitarily invariant norm: delta times the norm of sin Theta0 is at most the norm of R."
        )
        stmt = math(
            r"\cx{gap}{\delta}\,\norm{\cx{sine}{\sin\Theta_0}}\ \le\ \norm{\cx{resid}{R}}",
            size=64,
        )
        box = boxed(stmt, color=FG, pad=0.3).move_to([0, 1.7, 0])
        hyp = tex(
            r"whenever $\cx{trial}{\operatorname{spec}(A_0)}\subset[\beta,\alpha]$ and "
            r"$\cx{exact}{\operatorname{spec}(\Lambda_1)}$ avoids $(\beta-\cx{gap}{\delta},\alpha+\cx{gap}{\delta})$, "
            r"for \emph{every} unitarily invariant norm",
            size=26,
            color=MUTED,
        ).next_to(box, DOWN, buff=0.3)
        self.play(FadeIn(box, scale=0.95), FadeIn(hyp))

        self.say(
            "Read each factor. sin Theta0: how far the trial subspace is from the true one "
            "(not computable). R: how far the trial is from being invariant (computable). "
            "delta: how isolated the wanted part of the spectrum is."
        )
        rows = VGroup(
            tex(r"\cx{sine}{$\norm{\sin\Theta_0}$}\quad how far the trial subspace is from the true one", size=30),
            tex(r"\cx{resid}{$\norm{R}$}\quad how far the trial is from invariant \cx{muted}{(computable)}", size=30),
            tex(r"\cx{gap}{$\delta$}\quad how isolated the wanted eigenvalues are", size=30),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.25)
        rows.next_to(hyp, DOWN, buff=0.4)
        self.play(FadeIn(rows, lag_ratio=0.3))

        self.say(
            "Rearranged: the subspace error is at most residual over gap. Any dimension, "
            "including infinite, and any unitarily invariant norm."
        )
        slogan = boxed(
            math(
                r"\norm{\cx{sine}{\sin\Theta_0}}\ \le\ \frac{\norm{\cx{resid}{R}}}{\cx{gap}{\delta}}"
                r"\qquad\text{subspace error}\ \le\ \frac{\text{residual}}{\text{gap}}",
                size=36,
            ),
            color=SINE,
        ).next_to(rows, DOWN, buff=0.35)
        self.play(FadeIn(slogan, shift=UP * 0.1))


# ----------------------------------------------------------------------------
# 8. Why: one trial vector
# ----------------------------------------------------------------------------


class S08Components(DeckSlide):
    """The one-vector proof as a bar chart.

    ``short = True`` gives the condensed version for the short deck: the same
    picture, plain-language captions instead of the equations, three builds.
    """

    title = "Why it is true: one trial vector"
    kicker = r"Write $v$ in the eigenbasis of $A$ (the proof uses it; the bound does not need it)"
    depth = "*"
    short = False

    def body(self) -> None:
        ex = story.COMPONENT_EXAMPLE
        ex.verify()
        lam, c, rho, delta = ex.lam, ex.c, ex.rho, ex.delta
        base_y = -2.65
        sx, sy = 0.98, 2.6
        x0 = -3.95

        def X(t: float, h: float = 0.0) -> np.ndarray:
            return np.array([x0 + sx * t, base_y + sy * h, 0.0])

        axis = Line(X(-3.0), X(3.0), color=MUTED, stroke_width=2)
        lam_lbl = math(r"\lambda", size=28, color=MUTED).next_to(X(3.0), RIGHT, buff=0.1)
        window = Rectangle(
            width=sx * 2 * delta, height=sy * 1.0, fill_color=GAP, fill_opacity=0.13, stroke_width=0
        ).move_to(X(rho, 0.5))
        win_lbl = math(r"(\rho-\delta,\rho+\delta)", size=24, color=GAP).next_to(window, UP, buff=0.08)
        rho_mark = Triangle(color=TRIAL, fill_color=TRIAL, fill_opacity=1).scale(0.09).rotate(np.pi).next_to(X(rho), DOWN, buff=0.04)
        rho_lbl = math(r"\rho", size=28, color=TRIAL).next_to(rho_mark, DOWN, buff=0.06)
        ticks = VGroup(*[Dot(X(t), radius=0.05, color=MUTED) for t in lam])
        bar_w = 0.34

        def bars(heights, colors) -> VGroup:
            return VGroup(
                *[
                    Rectangle(width=bar_w, height=max(sy * h, 1e-3), stroke_width=0, fill_color=col, fill_opacity=0.9).move_to(
                        X(t, 0), aligned_edge=DOWN
                    )
                    for t, h, col in zip(lam, heights, colors)
                ]
            )

        coef_colors = [EXACT if w else SINE for w in ex.wanted]
        coef_bars = bars(np.abs(c), coef_colors)
        bar_lbl = tex(r"bars: $|c_j|$", size=26).move_to([X(-3.0)[0], 1.1, 0], aligned_edge=LEFT)

        # The stretch factor |lambda - rho| is drawn on its own vertical scale:
        # screen height = wscale * |lambda - rho|.
        wscale = 0.55

        def W(t: float, value: float) -> np.ndarray:
            return X(t, wscale * value / sy)

        weight = VMobject()
        weight.set_points_as_corners([W(-3.0, abs(-3.0 - rho)), W(rho, 0.0), W(3.0, abs(3.0 - rho))])
        weight.set_stroke(GAP, width=3)
        delta_line = DashedVMobject(Line(W(-3.0, delta), W(3.0, delta), color=GAP, stroke_width=2), num_dashes=50)
        w_lbl = math(r"|\lambda-\rho|", size=26, color=GAP).next_to(W(3.0, abs(3.0 - rho)), UP, buff=0.08)
        d_lbl = math(r"\delta", size=26, color=GAP).next_to(W(3.0, delta), RIGHT, buff=0.08)
        res_bars = bars(np.abs(ex.residual_coefficients), [RESID] * len(lam))
        res_lbl = tex(r"bars: \cx{resid}{$|\lambda_j-\rho|\,|c_j|$}", size=26).move_to(bar_lbl, aligned_edge=LEFT)
        rx = -0.45

        if self.short:
            self._short_body(ex, rx, axis, lam_lbl, ticks, window, win_lbl, rho_mark, rho_lbl, coef_bars, bar_lbl,
                             weight, delta_line, w_lbl, d_lbl, res_bars, res_lbl)
            return

        v_eq = math(r"v=\sum_j c_j f_j,\qquad A f_j=\lambda_j f_j", size=30)
        sin_eq = math(r"\cx{sine}{\sin^2\theta}=\sum_{\lambda_j\notin\text{window}}\cx{sine}{c_j^2}", size=30)
        u_note = tex(r"$\cx{exact}{U}$ = span of the $f_j$ with $\lambda_j$ in the window", size=24, color=MUTED)
        r_eq = math(r"\cx{resid}{r}=Av-\rho v=\sum_j(\lambda_j-\rho)\,c_j f_j", size=30)
        outside = tex(r"outside the window: $|\lambda_j-\rho|\ge\cx{gap}{\delta}$", size=26)
        chain = math(
            r"\begin{aligned}\norm{\cx{resid}{r}}^2&\ge\sum_{\lambda_j\notin\text{window}}(\lambda_j-\rho)^2c_j^2\\"
            r"&\ge\cx{gap}{\delta}^2\sum_{\lambda_j\notin\text{window}}c_j^2=\cx{gap}{\delta}^2\cx{sine}{\sin^2\theta}\end{aligned}",
            size=30,
        )
        nums = math(
            rf"\cx{{gap}}{{\delta}}\cx{{sine}}{{\sin\theta}}={ex.theorem_lhs:.3f}\ \le\ {ex.unwanted_residual_norm:.3f}"
            rf"\ \le\ \norm{{\cx{{resid}}{{r}}}}={ex.residual_norm:.3f}",
            size=28,
        )
        column(v_eq, sin_eq, u_note, r_eq, outside, chain, nums, top=self.content_top - 0.2, x=rx, buff=0.22)
        tail = VGroup(chain, nums)
        tail_bg = Rectangle(
            width=tail.width + 0.3, height=tail.height + 0.3, fill_color=PANEL, fill_opacity=0.95, stroke_width=0
        ).move_to(tail)

        self.say(
            "Expand v in eigenvectors f_j of A; the bars are |c_j|, placed at their "
            "eigenvalues. The window around rho contains the wanted eigenvalues, blue; "
            "the rest, pink, is Lambda1. The pink mass is exactly sin^2 theta."
        )
        self.play(Create(axis), FadeIn(lam_lbl, ticks, window, win_lbl, rho_mark, rho_lbl))
        self.play(LaggedStartMapGrow(coef_bars), FadeIn(bar_lbl))
        self.play(FadeIn(v_eq, sin_eq, u_note))

        self.say(
            "Now apply A - rho. Each component is multiplied by lambda_j - rho: the V-shaped "
            "curve. Outside the window it is at least delta."
        )
        self.play(Create(weight), Create(delta_line), FadeIn(w_lbl, d_lbl), FadeIn(r_eq), FadeIn(outside))

        self.say(
            "Multiply. Components near rho are crushed; every pink component is "
            "multiplied by at least delta. Green bars are the residual's components."
        )
        self.play(Transform(coef_bars, res_bars), Transform(bar_lbl, res_lbl), run_time=2.0)

        self.say(
            "Keep only the pink directions and use the weight bound: the norm of r is at "
            "least delta sin theta. That is the theorem for one vector. Numbers for this "
            "picture on the right."
        )
        self.play(FadeIn(tail_bg), FadeIn(tail))

    def _short_body(self, ex, rx, axis, lam_lbl, ticks, window, win_lbl, rho_mark, rho_lbl, coef_bars, bar_lbl,
                    weight, delta_line, w_lbl, d_lbl, res_bars, res_lbl) -> None:
        w = 7.2
        t1 = para(
            r"The bars are the trial vector's components along the eigenvectors of $A$, placed at "
            r"their eigenvalues. \cx{exact}{Blue}: inside the window around $\rho$; they span $U$. "
            r"\cx{sine}{Pink}: outside; together they measure $\sin\theta$.",
            width=w,
            size=27,
        )
        t2 = para(
            r"The residual multiplies each component by its eigenvalue's distance from $\rho$ "
            r"(\cx{gap}{violet}). Outside the window that factor is at least $\cx{gap}{\delta}$.",
            width=w,
            size=27,
        )
        verdict = boxed(math(r"\cx{gap}{\delta}\,\cx{sine}{\sin\theta}\ \le\ \norm{\cx{resid}{r}}", size=40), color=FG)
        t3 = para(
            rf"So the pink part of the residual alone is at least $\delta\sin\theta$ "
            rf"(here ${ex.theorem_lhs:.3f}\le{ex.residual_norm:.3f}$). With many trial vectors the same "
            r"argument runs block by block, through a Sylvester equation.",
            width=w,
            size=25,
            color=MUTED,
        )
        col = VGroup(t1, t2, verdict, t3).arrange(DOWN, aligned_edge=LEFT, buff=0.35)
        col.move_to([rx, self.content_top - 0.2, 0], aligned_edge=UP + LEFT)
        for m in col:
            fit_right(m)

        self.say(
            "Why should it be true? Write the trial vector in the eigenvectors of A. Blue bars are "
            "the components we want; pink bars are the components outside U, and their total size is sin theta."
        )
        self.play(Create(axis), FadeIn(lam_lbl, ticks, window, win_lbl, rho_mark, rho_lbl))
        self.play(LaggedStartMapGrow(coef_bars), FadeIn(bar_lbl), FadeIn(t1))

        self.say(
            "The residual multiplies every component by how far its eigenvalue is from rho. Near rho "
            "that is small, so the wanted components nearly vanish. Outside the window it is at least delta."
        )
        self.play(Create(weight), Create(delta_line), FadeIn(w_lbl, d_lbl), FadeIn(t2))
        self.play(Transform(coef_bars, res_bars), Transform(bar_lbl, res_lbl), run_time=2.0)

        self.say(
            "So the residual is at least delta times sin theta. That is the whole idea; the "
            "general case runs the same argument on blocks."
        )
        self.play(FadeIn(verdict), FadeIn(t3))


class S08WhyShort(S08Components):
    title = "Why it is true, in one picture"
    kicker = r"Write the trial vector $v$ in the eigenvectors of $A$"
    depth = ""
    short = True


def LaggedStartMapGrow(bars: VGroup):
    from manim import LaggedStart

    return LaggedStart(*[GrowFromEdge(b, DOWN) for b in bars], lag_ratio=0.12, run_time=1.4)


# ----------------------------------------------------------------------------
# 9. Many vectors: a Sylvester equation
# ----------------------------------------------------------------------------


class S09Sylvester(DeckSlide):
    title = "Many trial vectors: a Sylvester equation"
    kicker = "The same argument, one block at a time"
    depth = "*"

    def body(self) -> None:
        ex = story.SYLVESTER_EXAMPLE
        ex.verify()

        self.say(
            "Project the residual onto the unwanted eigenvectors F1. Because A F1 = F1 Lambda1, "
            "F1* R is a Sylvester expression in X = F1* E0, and the singular values of X are the sines."
        )
        lines = VGroup(
            math(r"A\cx{exact}{F_1}=\cx{exact}{F_1\Lambda_1}\ \Longrightarrow\ \cx{exact}{F_1^{*}}A=\cx{exact}{\Lambda_1F_1^{*}}", size=32),
            math(
                r"\cx{exact}{F_1^{*}}\cx{resid}{R}=\cx{exact}{F_1^{*}}A\cx{trial}{E_0}-\cx{exact}{F_1^{*}}\cx{trial}{E_0A_0}"
                r"=\cx{exact}{\Lambda_1}\cx{sine}{X}-\cx{sine}{X}\cx{trial}{A_0},"
                r"\qquad \cx{sine}{X}=\cx{exact}{F_1^{*}}\cx{trial}{E_0}",
                size=32,
            ),
            math(r"\norm{\cx{sine}{X}}=\norm{\cx{sine}{\sin\Theta_0}},\qquad \norm{\cx{exact}{F_1^{*}}\cx{resid}{R}}\le\norm{\cx{resid}{R}}", size=32),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.3)
        lines.move_to([LEFT_X(), self.content_top - 0.25, 0], aligned_edge=UP + LEFT)
        self.play(FadeIn(lines[0]))
        self.play(FadeIn(lines[1]))
        self.play(FadeIn(lines[2]))

        self.say(
            "In eigenbases of Lambda1 and A0 the Sylvester map acts entrywise: "
            "entry x_ij is multiplied by lambda_i - a_j, and the gap makes every such factor at "
            "least delta. That already proves the Frobenius-norm case."
        )
        grid_left = self._grid(ex.X, ex, label=r"\cx{sine}{X}", color=SINE).move_to([-5.35, -1.8, 0])
        grid_right = self._grid(
            ex.C, ex, label=r"\cx{exact}{\Lambda_1}X-X\cx{trial}{A_0}", color=RESID, rows_right=True
        ).move_to([-0.45, -1.8, 0])
        arrow = Arrow(grid_left[0].get_right(), grid_right[0].get_left(), buff=0.2, color=MUTED, stroke_width=4)
        arrow_lbl = math(r"x_{ij}\mapsto(\lambda_i-a_j)\,x_{ij}", size=22, color=MUTED).next_to(arrow, UP, buff=0.12)
        self.play(FadeIn(grid_left))
        self.play(Create(arrow), FadeIn(arrow_lbl), ReplacementTransformFromCopy(grid_left, grid_right))

        self.say(
            "For every unitarily invariant norm, entrywise is not enough; that is exactly "
            "where the interval shape of the gap is used, through Davis and Kahan's "
            "Sylvester-equation theorems in Section 5. Conclusion: delta ||sin Theta0|| <= ||R||."
        )
        sep = math(
            r"\text{gap}\ \Longrightarrow\ \norm{\cx{exact}{\Lambda_1}X-X\cx{trial}{A_0}}\ \ge\ \cx{gap}{\delta}\,\norm{X}",
            size=30,
        )
        sep_note = para(
            r"entrywise $\Rightarrow$ Frobenius norm at once;\\ \emph{every} unitarily invariant norm needs the "
            r"separating interval (Davis--Kahan \S5, Thms~5.1--5.2)",
            width=4.4,
            size=22,
            color=MUTED,
        )
        qed = boxed(math(r"\cx{gap}{\delta}\,\norm{\cx{sine}{\sin\Theta_0}}\le\norm{\cx{resid}{R}}", size=36), color=FG)
        right = VGroup(sep, sep_note, qed).arrange(DOWN, aligned_edge=LEFT, buff=0.3)
        right.move_to([2.45, -1.75, 0], aligned_edge=LEFT)
        for mob in right:
            fit_right(mob)
        self.play(FadeIn(right, shift=UP * 0.1))

    def _grid(self, M: np.ndarray, ex, label: str, color: str, rows_right: bool = False) -> VGroup:
        rows, cols = M.shape
        cell = 0.62
        vmax = float(np.max(np.abs(np.concatenate([ex.X.ravel(), ex.C.ravel()]))))
        cells = VGroup()
        for i in range(rows):
            for j in range(cols):
                a = abs(M[i, j]) / vmax
                sq = Rectangle(width=cell, height=cell, stroke_color=FAINT, stroke_width=1.5, fill_color=color, fill_opacity=0.12 + 0.85 * a)
                sq.move_to([j * cell, -i * cell, 0])
                cells.add(sq)
        row_lbls = VGroup(
            *[
                math(rf"{l:+.1f}", size=20, color=EXACT).next_to(
                    cells[i * cols + (cols - 1 if rows_right else 0)], RIGHT if rows_right else LEFT, buff=0.1
                )
                for i, l in enumerate(ex.lam)
            ]
        )
        col_lbls = VGroup(*[math(rf"{a:+.1f}", size=20, color=TRIAL).next_to(cells[j], UP, buff=0.08) for j, a in enumerate(ex.a)])
        name = math(label, size=26).next_to(VGroup(cells, col_lbls), UP, buff=0.12)
        return VGroup(cells, row_lbls, col_lbls, name)


def LEFT_X() -> float:
    return -6.55


def ReplacementTransformFromCopy(a, b):
    return ReplacementTransform(a.copy(), b)


# ----------------------------------------------------------------------------
# 10. Sharpness
# ----------------------------------------------------------------------------


class S10Sharp(DeckSlide):
    title = "The constant 1 cannot be improved"
    kicker = "A two-dimensional example with equality at every angle"
    depth = "*"

    def body(self) -> None:
        delta = story.SHARP_DELTA
        th = ValueTracker(np.radians(35.0))
        plane = Plane([-5.2, -2.45, 0], 2.9)

        def model() -> SineThetaModel:
            return SineThetaModel(th.get_value(), delta=delta)

        U = Line(plane([-0.15, 0]), plane([1.3, 0]), color=EXACT, stroke_width=4)
        U_lbl = math(r"U=\operatorname{span}(e_1)", size=28, color=EXACT).next_to(plane([1.3, 0]), DOWN, buff=0.15).shift(LEFT * 0.6)
        v = always_redraw(lambda: vec(plane.origin, plane(model().trial_vector), TRIAL, width=7))
        v_lbl = always_redraw(lambda: math(r"v_\theta", size=30, color=TRIAL).next_to(plane(model().trial_vector), UL, buff=0.08))
        leg = always_redraw(lambda: segment(plane(model().desired_projection), plane(model().trial_vector), SINE, width=8))
        leg_lbl = always_redraw(
            lambda: math(r"\sin\theta", size=28, color=SINE).next_to(plane(model().desired_projection + model().sine_block_vector / 2), LEFT, buff=0.1)
        )
        res_x = 1.45

        def res_start():
            return plane([res_x, 0])

        r_vec = always_redraw(lambda: vec(res_start(), res_start() + p3(plane.scale * model().residual), RESID, width=8))
        r_lbl = always_redraw(
            lambda: math(r"r", size=30, color=RESID).next_to(res_start() + p3(plane.scale * model().residual / 2), RIGHT, buff=0.1)
        )
        arc = always_redraw(lambda: angle_arc(plane, [1, 0], model().trial_vector, 0.6, FG, width=3))

        self.say(
            "Take A = diag(rho, rho + delta) and the trial vector v_theta at angle theta "
            "from the eigenvector e1, with A0 = rho. The gap is exactly delta."
        )
        eqs = VGroup(
            math(r"A=\begin{pmatrix}\rho&0\\0&\rho+\delta\end{pmatrix},\quad A_0=[\rho],\quad v_\theta=(\cos\theta,\sin\theta)", size=30),
            math(
                r"\cx{resid}{r}=Av_\theta-\rho v_\theta=(0,\ \cx{gap}{\delta}\cx{sine}{\sin\theta})"
                r"\ \Longrightarrow\ \norm{\cx{resid}{r}}=\cx{gap}{\delta}\,\cx{sine}{\sin\theta}",
                size=30,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.3)
        eqs.move_to([-0.6, self.content_top - 0.25, 0], aligned_edge=UP + LEFT)
        self.play(Create(U), FadeIn(U_lbl))
        self.add(v, v_lbl, arc, leg, leg_lbl)
        self.play(FadeIn(VGroup(v, v_lbl, arc, leg, leg_lbl)), FadeIn(eqs[0]))
        self.add(r_vec, r_lbl)
        self.play(FadeIn(VGroup(r_vec, r_lbl)), FadeIn(eqs[1]))

        meter_axes_x = 1.9
        meter_len = 3.4

        def meter(y, getter, color, label):
            track = Line([meter_axes_x, y, 0], [meter_axes_x + meter_len, y, 0], color=FAINT, stroke_width=14)
            fill = always_redraw(
                lambda: Line(
                    [meter_axes_x, y, 0],
                    [meter_axes_x + max(meter_len * getter() / delta, 1e-3), y, 0],
                    color=color,
                    stroke_width=14,
                )
            )
            lbl = math(label, size=28).next_to(track, LEFT, buff=0.2)
            val = live(getter, decimals=3, size=28, color=color).next_to(track, RIGHT, buff=0.2)
            val.add_updater(lambda m: m.next_to(track, RIGHT, buff=0.2))
            return VGroup(track, fill, lbl, val)

        m1 = meter(-1.0, lambda: model().theorem_lhs, SINE, r"\cx{gap}{\delta}\cx{sine}{\sin\theta}")
        m2 = meter(-1.7, lambda: model().residual_norm, RESID, r"\norm{\cx{resid}{r}}")
        meters = VGroup(m1, m2)

        self.play(FadeIn(meters))

        self.say(
            "Sweep the angle: the two bars stay exactly equal. So no constant smaller "
            "than 1 can replace the one in the theorem. (This build loops.)",
            loop=True,
        )
        self.play(th.animate.set_value(np.radians(75)), run_time=2.4, rate_func=rate_functions.ease_in_out_sine)
        self.play(th.animate.set_value(np.radians(10)), run_time=3.0, rate_func=rate_functions.ease_in_out_sine)
        self.play(th.animate.set_value(np.radians(35)), run_time=1.8, rate_func=rate_functions.ease_in_out_sine)

        self.say(
            "Davis and Kahan note that orthogonal sums of such planes give equality in all "
            "unitarily invariant norms at once. In Lean, sinTheta_constant_one_optimal proves "
            "that no c < 1 works, for every symmetric norming function."
        )
        lean = VGroup(
            tex(r"Lean:", size=24, color=MUTED),
            mono("TauCeti.DavisKahan.ExactSinTheta\n  .sinTheta_constant_one_optimal", size=17, color=FG),
            tex(r"no constant $c<1$ works, for any symmetric norm", size=24, color=MUTED),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        lean.move_to([0.7, -2.35, 0], aligned_edge=UP + LEFT)
        self.play(FadeIn(lean))


# ----------------------------------------------------------------------------
# 11. Payoff: perturbation bound
# ----------------------------------------------------------------------------


class S11Payoff(DeckSlide):
    title = "Payoff: how far can an eigenvector turn?"
    kicker = r"Use the \emph{old} eigenvectors as the trial subspace"

    def body(self) -> None:
        eps = story.PERTURBATION_EPS
        g = ValueTracker(story.PERTURBATION_START_GAP)

        def pair() -> story.PerturbedPair:
            return story.PerturbedPair(gap=g.get_value(), eps=eps)

        self.say(
            "Classic use: A is perturbed to A + H. Take E0 = eigenvectors of A and A0 = their "
            "eigenvalues. The residual for A + H is just H E0, so its norm is at most the "
            "norm of H. Here delta separates the old wanted eigenvalues from the new unwanted ones."
        )
        derivation = VGroup(
            math(
                r"\cx{resid}{R}=(A+H)\cx{trial}{E_0}-\cx{trial}{E_0A_0}=H\cx{trial}{E_0}"
                r"\ \Longrightarrow\ \norm{\cx{resid}{R}}\le\norm{H}",
                size=32,
            ),
            boxed(
                math(r"\norm{\cx{sine}{\sin\Theta_0}}\ \le\ \frac{\norm{H}}{\cx{gap}{\delta}}", size=40),
                color=SINE,
            ),
        ).arrange(RIGHT, buff=0.6)
        derivation.move_to([0, self.content_top - 0.2, 0], aligned_edge=UP)
        note = tex(
            r"$\cx{trial}{E_0}$: eigenvectors of $A$; $\cx{trial}{A_0}$: their eigenvalues;"
            r" $\cx{gap}{\delta}$: from them to the \emph{unwanted} eigenvalues of $A+H$",
            size=24,
            color=MUTED,
        ).next_to(derivation, DOWN, buff=0.2)
        self.play(FadeIn(derivation), FadeIn(note))

        plane = Plane([-4.3, -1.75, 0], 0.82, rotate=ELLIPSE_BASE)
        old = always_redraw(lambda: DashedVMobject(ellipse(plane, pair().A, color=MUTED, width=2), num_dashes=50))
        new = always_redraw(lambda: ellipse(plane, pair().perturbed, color=FG, width=3))
        old_axis = DashedVMobject(through_origin(plane, [1, 0], 2.3, MUTED, width=2), num_dashes=24)
        new_axis = always_redraw(lambda: through_origin(plane, pair().perturbed_top_eigenvector, 2.0, EXACT, width=4))
        arc = always_redraw(lambda: angle_arc(plane, [1, 0], pair().perturbed_top_eigenvector, 2.1, SINE, width=4))

        axes = Axes(
            x_range=[0, 1.0, 0.25],
            y_range=[0, 1.0, 0.25],
            x_length=5.2,
            y_length=2.9,
            tips=False,
            axis_config={"color": MUTED, "stroke_width": 2},
        ).move_to([3.3, -1.85, 0])
        x_lbl = math(r"\text{gap of }A:\ g", size=24, color=MUTED).next_to(axes.x_axis, DOWN, buff=0.12).shift(RIGHT * 1.6)
        y_ticks = VGroup(*[math(f"{v:g}", size=20, color=MUTED).next_to(axes.c2p(0, v), LEFT, buff=0.08) for v in (0.5, 1.0)])
        x_ticks = VGroup(*[math(f"{v:g}", size=20, color=MUTED).next_to(axes.c2p(v, 0), DOWN, buff=0.08) for v in (0.5, 1.0)])
        actual = axes.plot(lambda x: story.PerturbedPair(gap=x, eps=eps).sin_theta, x_range=[0.0, 1.0], color=SINE, stroke_width=4)
        bound = DashedVMobject(
            axes.plot(lambda x: story.PerturbedPair(gap=x, eps=eps).bound, x_range=[0.0, 1.0], color=RESID, stroke_width=3),
            num_dashes=45,
        )
        a_lbl = math(r"\sin\theta", size=26, color=SINE).next_to(axes.c2p(0.9, story.PerturbedPair(0.9, eps).sin_theta), DOWN, buff=0.12)
        b_lbl = math(r"\norm{R}/\delta", size=26, color=RESID).next_to(axes.c2p(0.25, story.PerturbedPair(0.25, eps).bound), UR, buff=0.08)
        d_actual = always_redraw(lambda: Dot(axes.c2p(g.get_value(), pair().sin_theta), color=SINE, radius=0.07))
        d_bound = always_redraw(lambda: Dot(axes.c2p(g.get_value(), pair().bound), color=RESID, radius=0.07))

        self.say(
            "Back to the 2x2 example with epsilon = 0.12. Pink: the true sin theta as the gap "
            "of A shrinks. Green dashed: the bound ||R|| / delta. The bound always holds, and "
            "for large gaps it is essentially exact."
        )
        self.add(old, new, old_axis, new_axis, arc)
        self.play(
            FadeIn(VGroup(old, new, old_axis, new_axis, arc)),
            Create(axes),
            FadeIn(x_lbl, y_ticks, x_ticks),
            Create(actual),
            Create(bound),
            FadeIn(a_lbl, b_lbl),
        )
        self.add(d_actual, d_bound)
        self.play(g.animate.set_value(story.PERTURBATION_END_GAP), run_time=5.0, rate_func=rate_functions.ease_in_out_sine)

        self.say(
            "Note where delta is measured in this example: from the old wanted eigenvalue to the new "
            "unwanted one. The perturbed eigenvalues split apart, so here the bound stays finite, "
            "tending to 1, even as the original gap collapses. That is a property of this example, "
            "not a general promise."
        )
        remark = para(
            r"In this example $\cx{gap}{\delta}$ is measured against the \emph{perturbed} unwanted "
            r"eigenvalue, which splits away from the old one, so the bound stays informative "
            r"(it tends to $1$) even as $A$'s own gap collapses.",
            width=11.5,
            size=24,
        ).move_to(note)
        self.play(FadeOut(note), FadeIn(remark))


# ----------------------------------------------------------------------------
# 12. What Lean proves
# ----------------------------------------------------------------------------

# The statement exactly as `#check @TauCeti.DavisKahan1970.SectionTwo.sinTheta` prints
# it, with only instance-binder names dropped and the lines re-broken.  Re-check
# after any change to the alias (see the README).
LEAN_SIGNATURE = [
    "theorem TauCeti.DavisKahan1970.SectionTwo.sinTheta",
    "    {𝕜 : Type u_1} [RCLike 𝕜] {E F G H : Type u_2}",
    "    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]",
    "    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]",
    "    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]",
    "    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]",
    "    [TopologicalSpace.SeparableSpace E]",
    "    (N : TauCeti.DavisKahan.ExactSinTheta.NormalizedSymmetricOperatorIdealFamily 𝕜)",
    "    (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)",
    "    (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E) :",
    "    IsSelfAdjoint A → IsSelfAdjoint A₀ → IsSelfAdjoint Λ₁ →",
    "    TauCeti.DavisKahan1970.IsTrialResidual A A₀ E₀ R →",
    "    TauCeti.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ →",
    "    ∀ {δ : ℝ}, 0 < δ →",
    "    TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ →",
    "    N.Mem (TauCeti.DavisKahan1970.sourceDirectedSinThetaOperator E₀ F₀) → N.Mem R →",
    "    δ * N.gaugeReal (TauCeti.DavisKahan1970.sourceDirectedSinThetaOperator E₀ F₀)",
    "      ≤ N.gaugeReal R",
]

# (first line, last line, label, colour) for the "reading it" build.
LEAN_READING = [
    (1, 1, r"scalars: $\mathbb{R}$ or $\mathbb{C}$", FG),
    (2, 6, r"separable Hilbert spaces, any dimension", FG),
    (7, 7, r"every unitarily invariant norm", FG),
    (8, 8, r"possibly unbounded operators", EXACT),
    (10, 10, r"all self-adjoint", EXACT),
    (11, 11, r"$\cx{resid}{R}=A\cx{trial}{E_0}-\cx{trial}{E_0}\cx{trial}{A_0}$", RESID),
    (12, 12, r"$A\cx{exact}{F_1}=\cx{exact}{F_1}\cx{exact}{\Lambda_1}$", EXACT),
    (14, 14, r"the gap $\cx{gap}{\delta}$", GAP),
    (15, 15, r"where the norms are defined", MUTED),
    (16, 17, r"$\cx{gap}{\delta}\norm{\cx{sine}{\sin\Theta_0}}\le\norm{\cx{resid}{R}}$, on $\sin\Theta_0$ itself", SINE),
]


class S12Lean(DeckSlide):
    title = "What we formalized: the full Lean theorem"
    kicker = "The complete statement, shown for its reach; not meant to be read token by token"
    section = ""

    def body(self) -> None:
        size = 14
        probe = Text("M" * 20, font=MONO_FONT, font_size=size)
        char_w = probe.width / 20
        line_h = 0.275
        x0, top = -6.75, self.content_top - 0.15
        lines = VGroup()
        for i, raw in enumerate(LEAN_SIGNATURE):
            indent = len(raw) - len(raw.lstrip(" "))
            t = Text(raw.strip(), font=MONO_FONT, font_size=size, color=FG)
            t.move_to([x0 + indent * char_w, top - i * line_h, 0], aligned_edge=LEFT)
            lines.add(t)
        right_edge = 2.95
        if lines.get_right()[0] > right_edge:
            lines.scale((right_edge - x0) / (lines.get_right()[0] - x0), about_point=[x0, top, 0])
        bg = Rectangle(
            width=lines.width + 0.4, height=lines.height + 0.35, fill_color=PANEL, fill_opacity=1, stroke_width=0
        ).move_to(lines)
        caption = para(
            r"As \texttt{\#check} prints it, with instance-binder names dropped and lines re-broken; "
            r"$\sin\Theta_0$ is \texttt{sourceDirectedSinThetaOperator E$_0$ F$_0$}.",
            width=13.3,
            size=19,
            color=MUTED,
        ).next_to(bg, DOWN, aligned_edge=LEFT, buff=0.1)

        self.say(
            "This is the actual Lean statement of the sin Theta theorem, complete. Nobody should read it "
            "token by token; the point is that this is the real object the proof checker accepted."
        )
        self.play(FadeIn(bg), FadeIn(lines, lag_ratio=0.03), FadeIn(caption))

        self.say(
            "Reading it: real or complex scalars; separable Hilbert spaces of any dimension; every "
            "unitarily invariant norm; possibly unbounded self-adjoint operators; the paper's residual, "
            "spectral decomposition and gap; and the conclusion delta times norm of sin Theta0 at most norm of R."
        )
        highlights, labels = VGroup(), VGroup()
        for first, last, label, color in LEAN_READING:
            block = VGroup(*lines[first : last + 1])
            box = Rectangle(
                width=block.width + 0.14, height=block.height + 0.1, stroke_color=color, stroke_width=1.6
            ).move_to(block)
            lab = tex(label, size=21, color=color)
            lab.move_to([right_edge + 0.35, block.get_center()[1], 0], aligned_edge=LEFT)
            fit_right(lab)
            highlights.add(box)
            labels.add(lab)
        highlighted = {i for first, last, _, _ in LEAN_READING for i in range(first, last + 1)}
        dim = [line.animate.set_opacity(0.4) for i, line in enumerate(lines) if i not in highlighted and i != 0]
        self.play(*dim, FadeIn(highlights, lag_ratio=0.1), FadeIn(labels, lag_ratio=0.1), run_time=1.6)

        self.say(
            "And it is trustworthy in the usual sense: print axioms shows only Lean's three standard "
            "axioms. The same holds for the Proposition 4.4 refutation later in the talk."
        )
        trust = para(
            r"\texttt{\#print axioms}: \texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound} "
            r"--- Lean's standard axioms, nothing assumed.",
            width=13.3,
            size=22,
            color=FG,
        ).next_to(caption, DOWN, aligned_edge=LEFT, buff=0.12)
        fit_right(trust)
        self.play(FadeIn(trust))


# ----------------------------------------------------------------------------
# 13. The family
# ----------------------------------------------------------------------------


class S13Family(DeckSlide):
    title = "The family: four theorems"
    kicker = r"Davis \& Kahan (1970), Section 2; this deck covered the first"
    depth = "*"

    def body(self) -> None:
        self.say(
            "The sin Theta theorem is the first of four. Each has a directed, residual "
            "form with sin Theta0 or tan Theta0; three also have an ambient form in H. "
            "The next decks cover tan Theta, sin 2 Theta and tan 2 Theta."
        )
        rows = [
            (r"\textbf{theorem}", r"\textbf{conclusions}", r"\textbf{hypotheses beyond self-adjointness}"),
            (r"$\sin\Theta$", r"$\delta\norm{\sin\Theta_0}\le\norm{R}$", r"interval/exterior gap, $A_0$ vs $\Lambda_1$"),
            (
                r"$\tan\Theta$",
                r"$\delta\norm{\tan\Theta_0}\le\norm{R}$, \ $\delta\norm{\tan\Theta}\le\norm{H}$",
                r"one-sided gap; $A_0=E_0^{*}(A+H)E_0$",
            ),
            (
                r"$\sin2\Theta$",
                r"$\delta\norm{\sin2\Theta_0}\le2\norm{R}$, \ $\delta\norm{\sin2\Theta}\le2\norm{H}$",
                r"interval/exterior gap, $\Lambda_0$ vs $\Lambda_1$",
            ),
            (
                r"$\tan2\Theta$",
                r"$\delta\norm{\tan2\Theta_0}\le2\norm{R}$, \ $\delta\norm{\tan2\Theta}\le2\norm{H}$",
                r"one-sided gap, $A_0$ vs $A_1$; $H_0=H_1=0$",
            ),
        ]
        cells = [[tex(c, size=26, color=FG if i else MUTED) for c in row] for i, row in enumerate(rows)]
        col_w = [max(r[j].width for r in cells) for j in range(3)]
        gutter, row_h = 0.55, 0.78
        total_w = sum(col_w) + 2 * gutter
        x_left = -total_w / 2
        y_top = 2.1
        for i, row in enumerate(cells):
            x = x_left
            for j, cell in enumerate(row):
                cell.move_to([x, y_top - i * row_h, 0], aligned_edge=LEFT)
                x += col_w[j] + gutter
        table = VGroup(*[c for row in cells for c in row])
        rule = Line([x_left, y_top - row_h / 2, 0], [x_left + total_w, y_top - row_h / 2, 0], color=FAINT, stroke_width=2)
        highlight = Rectangle(
            width=total_w + 0.4, height=row_h * 0.9, stroke_color=SINE, stroke_width=2.5, fill_opacity=0
        ).move_to([0, y_top - row_h, 0])
        self.play(FadeIn(table), Create(rule))
        self.play(Create(highlight))
        foot = tex(
            r"All constants are best possible. All hold for every unitarily invariant norm, in infinite "
            r"dimensions, and for unbounded self-adjoint operators under the paper's domain conditions.",
            size=24,
            color=MUTED,
        ).to_edge(DOWN, buff=0.75)
        self.play(FadeIn(foot))


# ----------------------------------------------------------------------------
# 14. Summary
# ----------------------------------------------------------------------------


class S14Summary(DeckSlide):
    title = "What to take away"
    kicker = ""

    def body(self) -> None:
        items = [
            (
                r"\cx{sine}{1}",
                r"\textbf{The $\sin\Theta$ theorem.} How far a subspace is from the true eigenspace is bounded "
                r"by something you can compute: $\ \norm{\cx{sine}{\sin\Theta_0}}\le\norm{\cx{resid}{R}}/\cx{gap}{\delta}$, "
                r"residual over gap.",
            ),
            (
                r"\cx{exact}{2}",
                r"\textbf{Formalized at the paper's full scope.} Real or complex Hilbert spaces of any dimension, "
                r"possibly unbounded operators, every unitarily invariant norm, checked by Lean with only its "
                r"standard axioms.",
            ),
            (
                r"\cx{gap}{3}",
                r"\textbf{Proposition 4.4 is false as printed.} An explicit counterexample in $\mathbb{R}^4$, "
                r"refuted in Lean, together with a proved repair: the claim holds for the $Q$-norms "
                r"(e.g.\ operator and Frobenius).",
            ),
        ]
        rows = VGroup()
        for num, text in items:
            n = tex(num, size=60)
            body = para(text, width=11.4, size=30)
            rows.add(VGroup(n, body).arrange(RIGHT, aligned_edge=UP, buff=0.45))
        rows.arrange(DOWN, aligned_edge=LEFT, buff=0.55)
        rows.move_to([-6.3, self.content_top - 0.35, 0], aligned_edge=UP + LEFT)
        self.say("Three things to remember.")
        for row in rows:
            self.play(FadeIn(row, shift=UP * 0.1), run_time=0.7)


SCENES = [
    S00Title,
    S00bSetting,
    S01Ellipse,
    S02Perturb,
    S03NoGap,
    S04Angle,
    S04bSinThetaOperator,
    S05Residual,
    S06Gap,
    S07Theorem,
    S11Payoff,
    S08Components,
    S09Sylvester,
    S10Sharp,
    S12Lean,
    S13Family,
    S14Summary,
]
