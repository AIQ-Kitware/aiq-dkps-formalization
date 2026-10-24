"""Standalone teaching deck for the post-Davis--Kahan optimization program.

The existing slide families explain the classical sin-Theta theorem, its
formalization, and the Proposition 4.4 refutation.  This module instead teaches
what the newer mathematics is trying to do: optimize *ambient* transport
penalties between subspaces, distinguish what is already formalized from what is
still only drafted, and keep the color roles consistent with the rest of the
visual system.
"""

from __future__ import annotations

import numpy as np
from manim import (
    Arc,
    Axes,
    Create,
    DashedLine,
    Dot,
    FadeIn,
    LEFT,
    Line,
    RIGHT,
    UP,
    DOWN,
    VGroup,
)

from dkvis.novelty_math import optimal_phase_three_halves
from dkvis.slide_style import (
    CURRENT,
    FAINT,
    FG,
    GAP,
    MUTED,
    SINE,
    TRIAL,
    WANTED,
    DeckSlide,
    axis_line,
    boxed,
    math,
    para,
    tex,
)

SECTION = r"New mathematics: spectral-penalty transport between subspaces"


def principal_plane(theta: float = 0.9, *, show_caption: bool = True) -> VGroup:
    """A simple 2D principal-plane picture with the same role colors as the
    main decks: source subspace blue, target subspace amber, turning angle pink.
    """

    origin = np.array([0.0, 0.0, 0.0])
    radius = 2.15
    x_axis = axis_line(origin + LEFT * 2.5, origin + RIGHT * 2.6)
    y_axis = axis_line(origin + DOWN * 2.0, origin + UP * 2.15)
    u = Line(origin, origin + np.array([radius, 0.0, 0.0]), color=WANTED, stroke_width=5)
    v = Line(
        origin,
        origin + np.array([radius * np.cos(theta), radius * np.sin(theta), 0.0]),
        color=TRIAL,
        stroke_width=5,
    )
    u_back = Line(origin, origin + np.array([-0.55 * radius, 0.0, 0.0]), color=WANTED, stroke_width=3, stroke_opacity=0.45)
    v_back = Line(
        origin,
        origin + np.array([-0.55 * radius * np.cos(theta), -0.55 * radius * np.sin(theta), 0.0]),
        color=TRIAL,
        stroke_width=3,
        stroke_opacity=0.45,
    )
    dot = Dot(origin, radius=0.04, color=FG)
    ang = Arc(radius=0.72, start_angle=0.0, angle=theta, color=SINE, stroke_width=4)
    u_lab = math(r"\sym{U}", size=30, color=WANTED).move_to(origin + np.array([2.45, -0.25, 0.0]))
    v_lab = math(r"\sym{V}", size=30, color=TRIAL).move_to(origin + np.array([2.05 * np.cos(theta) + 0.42, 2.05 * np.sin(theta) + 0.15, 0.0]))
    t_lab = math(r"\sym{theta}", size=28, color=SINE).move_to(
        np.array([0.94 * np.cos(theta / 2), 0.94 * np.sin(theta / 2) + 0.12, 0.0])
    )
    items = VGroup(x_axis, y_axis, u_back, v_back, u, v, ang, dot, u_lab, v_lab, t_lab)
    if show_caption:
        cap = tex(r"one principal plane", size=20, color=MUTED).next_to(items, DOWN, buff=0.2)
        items.add(cap)
    return items


def threshold_strip(left: str, right: str, *, tag: str) -> VGroup:
    axis = Line(LEFT * 2.6, RIGHT * 2.6, color=FAINT, stroke_width=2)
    tick = Line(UP * 0.18, DOWN * 0.18, color=GAP, stroke_width=3).move_to([0.0, 0.0, 0.0])
    left_lab = tex(left, size=21, color=MUTED).next_to(axis, DOWN, aligned_edge=LEFT, buff=0.12)
    right_lab = tex(right, size=21, color=MUTED).next_to(axis, DOWN, aligned_edge=RIGHT, buff=0.12)
    top = math(tag, size=28, color=GAP).next_to(tick, UP, buff=0.12)
    return VGroup(axis, tick, left_lab, right_lab, top)


def piece_box(*lines: str, size: float = 28, role: str = FG) -> VGroup:
    body = VGroup(*[math(line, size=size, color=role) for line in lines]).arrange(DOWN, aligned_edge=LEFT, buff=0.14)
    return boxed(body, color=role, pad=0.22)


def wrapped_bullets(*lines: str, width: float, size: float = 22, buff: float = 0.12) -> VGroup:
    """Readable, width-limited bullets (unlike unwrapped one-line ``bullets``).

    This is deliberately built out of the existing ``para`` utility so the
    glyphs, theme, mathematics, and source color conventions remain shared.
    """
    return VGroup(*[
        para(r"\textbullet\quad " + line, width=width, size=size)
        for line in lines
    ]).arrange(DOWN, aligned_edge=LEFT, buff=buff)


def fit_width(mobject: VGroup, width: float) -> VGroup:
    """Shrink a formula/card only when it exceeds its assigned column."""
    if mobject.width > width:
        mobject.scale_to_fit_width(width)
    return mobject


class N00Title(DeckSlide):
    section = ""

    def body(self) -> None:
        self.say(
            "Title. This deck is a standalone tour of the mathematical program that"
            " grows beyond the classical Davis-Kahan story: optimizing ambient"
            " transport penalties between subspaces, separating what is already"
            " formalized from what is still conjectural or only drafted."
        )
        title = tex(r"What is the new math we are building?", size=58).move_to(UP * 2.05)
        sub = tex(r"A standalone tour of spectral-penalty transport between subspaces", size=32, color=MUTED)
        sub.next_to(title, DOWN, buff=0.28)
        link = tex(r"Repository: AIQ-Kitware/aiq-dkps-formalization", size=18, color=MUTED).next_to(sub, DOWN, buff=0.18)

        pic = principal_plane(theta=0.94, show_caption=False).scale(1.08)
        pic.move_to(LEFT * 3.2 + DOWN * 0.25)
        thesis = VGroup(
            para(
                r"We already know the classical $\,\sin\Theta\,$ bounds and the"
                r" Proposition 4.4 refutation. The newer program asks a different"
                r" question: among all feasible ambient transports taking $\sym{U}$ to"
                r" $\sym{V}$, which one minimizes a chosen spectral penalty of"
                r" $I-W$?",
                width=6.2,
                size=27,
            ),
            para(
                r"Three threads matter: exact complex trace transport, exact smoothed"
                r" transport with a phase transition, and the Schatten/real-field"
                r" extensions. This deck shows what each thread says and what status it"
                r" has right now.",
                width=6.2,
                size=27,
                color=MUTED,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.32)
        thesis.move_to(RIGHT * 2.8 + DOWN * 0.05)

        self.play(FadeIn(title), FadeIn(sub), FadeIn(link))
        self.play(Create(pic), FadeIn(thesis), run_time=1.2)


class N01ThreeStories(DeckSlide):
    title = "Three different stories"
    kicker = r"Formalization, completed new optimization theorems, and drafted extensions"
    section = SECTION

    def body(self) -> None:
        cols = []
        specs = [
            (
                r"1. Formalized Davis--Kahan",
                WANTED,
                [
                    r"28 reviewed source targets formalized",
                    r"printed Proposition 4.4 refuted",
                    r"small-angle counterexamples verified",
                    r"best viewed as \textbf{formalized mathematics}, not a claim to invent classical $\sin\Theta$ theory",
                ],
            ),
            (
                r"2. Completed exact smoothed transport",
                CURRENT,
                [
                    r"complex equal-rank Charbonnier minimum formalized",
                    r"explicit optimizer via a spectral phase correction",
                    r"quantitative stability below a phase-transition angle",
                    r"currently the strongest completed candidate for genuinely new mathematics",
                ],
            ),
            (
                r"3. Schatten and real-field program",
                TRIAL,
                [
                    r"planar complex $1<p<2$ phase transition formalized",
                    r"higher-rank complex formula: drafted, not yet a compiled global theorem",
                    r"real matching and sharp field-gap theorems: drafted, with many verified ingredients",
                    r"these may become the next research paper, but not all are certified yet",
                ],
            ),
        ]
        for heading, color, items in specs:
            head = para(r"\textbf{" + heading + "}", width=3.75, size=24, color=color)
            body = wrapped_bullets(*items, width=3.65, size=20, buff=0.13)
            card = VGroup(head, body).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
            cols.append(boxed(card, color=color, pad=0.22))
        row = VGroup(*cols).arrange(RIGHT, buff=0.25, aligned_edge=UP)
        row.scale_to_fit_width(12.75)
        row.move_to([0.0, self.content_top - 1.9, 0.0])

        summary = para(
            r"The key novelty question is therefore not a yes/no label on the whole"
            r" repository. The right question is: \emph{which exact theorem, in which"
            r" field, for which cost, is completed and plausibly first-publication?}",
            width=12.3,
            size=25,
        ).move_to([0.0, -3.02, 0.0])

        self.say(
            "This novelty review separates three stories. First, the formalized"
            " Davis-Kahan paper. Second, the completed smoothed transport theorem," 
            " which is the strongest current new-math candidate. Third, the larger"
            " Schatten and real-field program, where some important results are still"
            " conventional drafts rather than Lean-certified global theorems."
        )
        self.play(FadeIn(row), FadeIn(summary), run_time=1.0)


class N02OptimizationProblem(DeckSlide):
    title = "The optimization problem"
    kicker = r"Feasible transporters are constrained by the subspaces, and the cost is a spectral penalty of $I-W$"
    section = SECTION

    def body(self) -> None:
        pic = principal_plane(theta=0.88).scale(1.05)
        pic.move_to(LEFT * 3.9 + DOWN * 0.25)

        defs = VGroup(
            math(r"W(\sym{U}) = \sym{V}", size=34),
            math(r"D_{\rho}(\sym{U},\sym{V}) = \min_{W:\,W\sym{U}=\sym{V}} \sum_j \rho\!\left(\sigma_j(I-W)\right)", size=29),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        fit_width(defs, 6.2)
        defs.move_to([0.12, self.content_top - 0.12, 0.0], aligned_edge=LEFT + UP)

        costs = VGroup(
            piece_box(r"\rho(s)=s", r"\text{trace / nuclear displacement}", size=25, role=WANTED),
            piece_box(r"\rho(s)=s^p", r"\text{Schatten-}p\text{ power}", size=25, role=TRIAL),
            piece_box(r"\rho_{\tau}(s)=\sqrt{\tau^2+s^2}-\tau", r"\text{smoothed / Charbonnier penalty}", size=25, role=CURRENT),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.22)
        fit_width(costs, 6.25)
        costs.move_to(RIGHT * 3.15 + DOWN * 1.02)

        note = para(
            r"This is an \emph{extrinsic} optimization problem in the ambient space."
            r" The cost sees the singular values of $I-W$, not just the geodesic"
            r" distance on the Grassmannian and not just the projection distance.",
            width=6.2,
            size=23,
            color=MUTED,
        ).next_to(costs, DOWN, aligned_edge=LEFT, buff=0.2)

        self.say(
            "Here is the common optimization template. We only consider transporters"
            " W that actually carry the source subspace U to the target subspace V."
            " Then we minimize a spectral penalty of the ambient displacement I minus"
            " W. The three main costs we study are the trace penalty, the Schatten-p"
            " power, and the smoothed Charbonnier penalty."
        )
        self.play(Create(pic), FadeIn(defs), FadeIn(costs), FadeIn(note), run_time=1.2)


class N03LowerBound(DeckSlide):
    title = "A universal lower bound"
    kicker = r"Before optimizing a cost, identify the part that no feasible transporter can beat"
    section = SECTION

    def body(self) -> None:
        left = principal_plane(theta=0.78).scale(0.92).move_to(LEFT * 4.15 + UP * 0.1)
        floor = VGroup(
            tex(r"For every unitarily invariant seminorm $N$ and every feasible $W$:", size=25, color=MUTED),
            math(r"N(P_{\sym{U}}-P_{\sym{V}}) \le N(I-W)", size=38),
            math(r"N\!\left(\left|P_{\sym{U}}-P_{\sym{V}}\right|\right) \le N(I-W)", size=34, color=SINE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        floor_box = fit_width(boxed(floor, color=SINE, pad=0.25), 7.0)
        floor_box.move_to(RIGHT * 2.55 + UP * 0.95)

        points = wrapped_bullets(
            r"No acute-angle assumption is needed",
            r"No singular-value enumeration is needed in the proof",
            r"The projection floor works for every unitarily invariant norm",
            r"Likely classical mathematics, but essential to our exact transport results",
            width=5.75,
            size=22,
        ).move_to(RIGHT * 2.55 + DOWN * 1.25)

        tag = para(
            r"Interpretation: the projections already tell you how much turning must"
            r" happen. Any feasible ambient unitary has to pay at least that much.",
            width=6.1,
            size=24,
            color=MUTED,
        ).next_to(points, DOWN, aligned_edge=LEFT, buff=0.2)

        self.say(
            "This lower bound is the workhorse. Whatever unitary transporter you"
            " choose, the displacement cannot beat the difference between the two"
            " projections. Mathematically it is probably not the deepest new result,"
            " but it is the hinge that turns exact optimization statements into sharp"
            " formulas."
        )
        self.play(Create(left), FadeIn(floor_box), FadeIn(points), FadeIn(tag), run_time=1.0)


class N04ComplexTrace(DeckSlide):
    title = "Exact complex trace transport"
    kicker = r"The full trace-displacement optimum is the projection floor itself"
    section = SECTION

    def body(self) -> None:
        theorem = VGroup(
            tex(r"Finite-dimensional complex equal-rank theorem:", size=26, color=MUTED),
            math(r"\min_{W:\,W\sym{U}=\sym{V}} \norm{I-W}_{1} = \operatorname{tr}\left|P_{\sym{U}}-P_{\sym{V}}\right| = 2\sum_{i=1}^{k} \sin\theta_i", size=33),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        theorem_box = fit_width(boxed(theorem, color=WANTED, pad=0.24), 12.5)
        theorem_box.move_to([0.0, self.content_top - 1.0, 0.0])

        phase = VGroup(
            tex(r"Optimal transporter (one explicit form):", size=25, color=MUTED),
            math(r"T_{\star}=R(C-iS)\quad\text{or}\quad R(C+iS)", size=34, color=CURRENT),
            math(r"C=\cos\Theta,\qquad S=\left|P_{\sym{U}}-P_{\sym{V}}\right|", size=31, color=SINE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.16)
        fit_width(phase, 5.95)
        phase.move_to(LEFT * 3.25 + DOWN * 1.25)

        explain = wrapped_bullets(
            r"The direct rotation $R$ is \textbf{not} always trace-optimal",
            r"Opposite complex phases split displacement into positive and negative parts",
            r"Each principal plane contributes exactly $2\sin\theta_i$",
            r"Exact global formula formalized; mathematical priority still under review",
            width=5.6,
            size=21,
        ).move_to(RIGHT * 3.35 + DOWN * 1.25)

        strip = threshold_strip(r"projection floor", r"trace-optimal complex transporter", tag=r"\text{exact equality}")
        strip.move_to([0.0, -3.0, 0.0])

        self.say(
            "For the complex trace problem the lower bound becomes the exact answer."
            " The minimum trace displacement equals the trace of the positive sine"
            " operator, or equivalently twice the sum of the principal sines. The"
            " direct rotation itself may fail to minimize trace cost, but a phase-"
            " corrected version does."
        )
        self.play(FadeIn(theorem_box), FadeIn(phase), FadeIn(explain), FadeIn(strip), run_time=1.1)


class N05SmoothedTransport(DeckSlide):
    title = "The completed exact smoothed theorem"
    kicker = r"Charbonnier transport becomes a weighted nuclear problem with a phase transition"
    section = SECTION

    def body(self) -> None:
        top = VGroup(
            math(r"\Psi_{\tau}(W)=\sum_j \left(\sqrt{\tau^2+\sigma_j(I-W)^2}-\tau\right)", size=31),
            math(r"\eta=\frac{\tau+\sqrt{\tau^2+4}}{2},\qquad \theta_c(\tau)=\arccos(\eta^{-2})", size=31, color=GAP),
            math(r"\Psi_{\tau}(W)=\norm{\eta W-\eta^{-1}I}_{1}-n\tau", size=33, color=CURRENT),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.14)
        top_box = fit_width(boxed(top, color=CURRENT, pad=0.22), 12.5)
        top_box.move_to([0.0, self.content_top - 0.10, 0.0], aligned_edge=UP)

        left = piece_box(
            r"\mu_{\tau}(\theta)=2\left(\sqrt{\tau^2+2-2\cos\theta}-\tau\right),\quad \theta\le \theta_c(\tau)",
            r"\mu_{\tau}(\theta)=2\eta\sin\theta-2\tau,\quad \theta\ge \theta_c(\tau)",
            size=23,
            role=WANTED,
        )
        fit_width(left, 6.05)
        left.move_to(LEFT * 3.25 + DOWN * 1.1)

        right = VGroup(
            tex(r"Global complex equal-rank minimum:", size=24, color=MUTED),
            math(r"\min_{W:\,W\sym{U}=\sym{V}} \Psi_{\tau}(W)=\sum_{i=1}^{k} \mu_{\tau}(\theta_i)", size=30),
            tex(r"Above the threshold, a nonzero phase correction appears:", size=24, color=MUTED),
            math(r"\delta_{\star}(\theta)=\arccos\!\left(\eta^{2}\cos\theta\right)\qquad (\theta\ge \theta_c(\tau))", size=29, color=TRIAL),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.15)
        fit_width(right, 6.0)
        right.move_to(RIGHT * 3.2 + DOWN * 1.0)

        strip = threshold_strip(r"canonical phase correction $=0$", r"nonzero optimal phase correction", tag=r"\theta_c(\tau)")
        strip.move_to([0.0, -3.0, 0.0])

        self.say(
            "This is the strongest completed new-math story in the repository. The"
            " literal smoothed singular-value objective turns into a weighted nuclear"
            " norm. That reveals an exact principal-angle formula, an explicit cutoff"
            " angle, and an explicit optimal phase correction above the cutoff."
        )
        self.play(FadeIn(top_box), FadeIn(left), FadeIn(right), FadeIn(strip), run_time=1.1)


class N06SmoothedStability(DeckSlide):
    title = "Smoothed transport is quantitatively stable below the cutoff"
    kicker = r"A near-minimizer must lie near the canonical rotation in Frobenius distance"
    section = SECTION

    def body(self) -> None:
        statement = VGroup(
            tex(r"If every principal angle satisfies $\theta_i\le \beta < \theta_c(\tau)$, then for every feasible $T$:", size=24, color=MUTED),
            math(
                r"c_{\tau,\beta}\,\norm{T-R}_{F}^{2} \le \Psi_{\tau}(T)-\Psi_{\tau}(R)",
                size=38,
                color=CURRENT,
            ),
            math(
                r"c_{\tau,\beta}=\frac{\cos\beta-\eta^{-2}}{2\sqrt{\tau^2+2-2\cos\beta}} > 0",
                size=30,
                color=GAP,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.14)
        statement_box = fit_width(boxed(statement, color=CURRENT, pad=0.24), 12.5)
        statement_box.move_to([0.0, self.content_top - 0.10, 0.0], aligned_edge=UP)

        left = wrapped_bullets(
            r"This is an \emph{error bound}, not only existence of a minimizer",
            r"It applies to every admissible unitary, including mixed principal planes",
            r"The growth coefficient is explicit and positive in the strict subcritical regime",
            r"This quantifies \emph{robustness}: small cost error forces small rotation error",
            width=5.7,
            size=21,
        ).move_to(LEFT * 3.25 + DOWN * 1.3)

        right = VGroup(
            threshold_strip(r"stability regime", r"phase-transition regime", tag=r"\beta < \theta_c(\tau)"),
            para(
                r"Interpretation: if a feasible transporter nearly minimizes the smoothed"
                r" cost, then it must be quadratically close to the canonical nonacute"
                r" direct rotation $R$. This is one of the strongest ``usable'' outputs of"
                r" the whole program.",
                width=5.55,
                size=23,
                color=MUTED,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.4)
        right.move_to(RIGHT * 3.2 + DOWN * 1.3)

        self.say(
            "The stability theorem says that below the cutoff angle, the objective has"
            " real quadratic growth around the canonical rotation. So near-minimizers"
            " cannot wander arbitrarily: the objective gap controls Frobenius distance."
            " This is mathematically distinct from merely writing down the exact"
            " minimum."
        )
        self.play(FadeIn(statement_box), FadeIn(left), FadeIn(right), run_time=1.0)


class N07SchattenTransition(DeckSlide):
    title = "Schatten $1<p<2$: a genuine phase transition"
    kicker = r"The canonical transport ceases to minimize once the principal angle crosses a sharp threshold"
    section = SECTION

    def _phase_curve(self, theta: float, p: float, *, width: float = 4.5, height: float = 2.65) -> tuple[VGroup, float]:
        yfun = lambda delta: (2 * np.sin((theta + delta) / 2)) ** p + (2 * np.sin((theta - delta) / 2)) ** p
        xs = np.linspace(0.0, theta, 250)
        ys = yfun(xs)
        ymax = float(np.max(ys))
        ymin = float(np.min(ys))
        pad = 0.1 * (ymax - ymin + 0.2)
        axes = Axes(
            x_range=[0.0, theta, theta / 4],
            y_range=[max(0.0, ymin - pad), ymax + pad, max((ymax - ymin) / 3, 0.2)],
            x_length=width,
            y_length=height,
            axis_config={"color": FAINT, "stroke_width": 2},
            tips=False,
        )
        curve = axes.plot(lambda x: float(yfun(x)), x_range=[0.0, theta], color=TRIAL, stroke_width=4)
        if p != 1.5:
            raise ValueError("the plotted explicit phase formula is for p = 3/2")
        delta_star = optimal_phase_three_halves(theta)
        dot = Dot(axes.c2p(delta_star, float(yfun(delta_star))), radius=0.05, color=CURRENT)
        if delta_star > 1e-8:
            vline = DashedLine(
                axes.c2p(delta_star, max(0.0, ymin - pad)),
                axes.c2p(delta_star, float(yfun(delta_star))),
                color=CURRENT,
                stroke_width=2,
                dash_length=0.08,
            )
            marker = VGroup(vline, dot)
        else:
            marker = VGroup(dot)
        zero_lab = math(r"0", size=20).next_to(axes.c2p(0.0, max(0.0, ymin - pad)), DOWN, buff=0.08)
        theta_lab = math(r"\sym{theta}", size=23, color=SINE).next_to(axes.c2p(theta, max(0.0, ymin - pad)), DOWN, buff=0.08)
        delta_lab = math(r"\delta", size=25, color=FG).next_to(axes.get_x_axis(), DOWN, buff=0.26)
        title = tex(
            rf"$\theta={theta * 180 / np.pi:.0f}^\circ$",
            size=23,
            color=MUTED,
        ).next_to(axes, UP, buff=0.14)
        return VGroup(axes, curve, marker, zero_lab, theta_lab, delta_lab, title), delta_star

    def body(self) -> None:
        theorem = VGroup(
            tex(r"Planar complex theorem, formalized for every $1<p<2$:", size=24, color=MUTED),
            math(r"m_p(\theta)=\min_{0\le \delta\le \theta} \bigl[2\sin\tfrac{\theta+\delta}{2}\bigr]^p + \bigl[2\sin\tfrac{\theta-\delta}{2}\bigr]^p", size=27),
            math(r"\delta=0\text{ is optimal} \iff \theta\le \theta_c(p):=\arccos\!\left(\frac{2-p}{p}\right)", size=31, color=GAP),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.14)
        theorem_box = fit_width(boxed(theorem, color=TRIAL, pad=0.22), 12.5)
        theorem_box.move_to([0.0, self.content_top - 0.10, 0.0], aligned_edge=UP)

        left_plot, _ = self._phase_curve(theta=np.deg2rad(45), p=1.5, height=2.0, width=4.2)
        right_plot, delta_star = self._phase_curve(theta=np.deg2rad(80), p=1.5, height=2.0, width=4.2)
        left_plot.move_to(LEFT * 3.3 + DOWN * 1.48)
        right_plot.move_to(RIGHT * 3.3 + DOWN * 1.48)
        left_caption = para(
            r"Below the cutoff: the minimum stays at $\delta=0$.",
            width=5.2, size=21, color=MUTED,
        ).next_to(left_plot, DOWN, buff=0.14)
        right_caption = para(
            rf"Above the cutoff: the optimal phase is $\delta_\star\approx {delta_star * 180 / np.pi:.1f}^\circ$.",
            width=5.2, size=21, color=MUTED,
        ).next_to(right_plot, DOWN, buff=0.14)

        self.say(
            "For Schatten powers between one and two, there is a real symmetry-"
            " breaking phase transition. In a principal plane the optimization reduces"
            " to a one-variable problem in the phase delta, and the direct rotation is"
            " optimal exactly up to a sharp threshold angle."
        )
        self.play(FadeIn(theorem_box), FadeIn(left_plot), FadeIn(right_plot), FadeIn(left_caption), FadeIn(right_caption), run_time=1.2)


class N08ComplexVsReal(DeckSlide):
    title = "Why complex and real transport diverge"
    kicker = r"Complex phases decouple plane-by-plane; real transport introduces matching constraints"
    section = SECTION

    def body(self) -> None:
        complex_box = boxed(
            VGroup(
                tex(r"Complex field", size=28, color=WANTED),
                wrapped_bullets(
                    r"A continuous phase correction is available on each principal plane",
                    r"Exact complex trace and smoothed formulas have been formalized",
                    r"The planar Schatten $1<p<2$ threshold is also formalized",
                    width=5.7,
                    size=21,
                ),
            ).arrange(DOWN, aligned_edge=LEFT, buff=0.2),
            color=WANTED,
            pad=0.24,
        )
        real_box = boxed(
            VGroup(
                tex(r"Real field", size=28, color=TRIAL),
                wrapped_bullets(
                    r"No arbitrary complex phases: real $2\times2$ and $4\times4$ blocks interact",
                    r"A repeated-angle real rank-two trace optimum is formalized",
                    r"Global matching and sharp real-complex field gaps remain drafted",
                    width=5.7,
                    size=21,
                ),
            ).arrange(DOWN, aligned_edge=LEFT, buff=0.2),
            color=TRIAL,
            pad=0.24,
        )
        pair = VGroup(complex_box, real_box).arrange(RIGHT, buff=0.38, aligned_edge=UP)
        pair.scale_to_fit_width(12.5)
        pair.move_to([0.0, self.content_top - 1.6, 0.0])

        bottom = VGroup(
            tex(r"Takeaway", size=26, color=MUTED),
            para(
                r"Many of the cleanest formulas come from the extra phase freedom of"
                r" the complex field. The real problem is not a cosmetic variant; it is a"
                r" different optimization geometry, which is why the real matching program"
                r" may itself become a substantial theorem if the current drafts close.",
                width=12.0,
                size=24,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18).move_to([0.0, -2.75, 0.0])

        self.say(
            "This is the conceptual split to keep in mind. Over the complex field, the"
            " optimizer can adjust a phase continuously on each principal plane. Over"
            " the real field, that freedom disappears and the problem turns into block"
            " matching. So the real problem is structurally different, not just a"
            " weaker copy of the complex one."
        )
        self.play(FadeIn(pair), FadeIn(bottom), run_time=1.0)


class N09StatusBoard(DeckSlide):
    title = "What you can say today"
    kicker = r"Use the strongest completed theorem aggressively; separate it from drafted extensions"
    section = SECTION

    def body(self) -> None:
        left = boxed(
            VGroup(
                para(r"\textbf{Safe strong claims}", width=3.78, size=23, color=CURRENT),
                wrapped_bullets(
                    r"Exact smoothed complex equal-rank minimum",
                    r"Explicit smoothed optimizer",
                    r"Subcritical quadratic growth inequality",
                    r"Planar complex Schatten $1<p<2$ transition",
                    width=3.78,
                    size=21,
                ),
            ).arrange(DOWN, aligned_edge=LEFT, buff=0.2),
            color=CURRENT,
            pad=0.22,
        )
        mid = boxed(
            VGroup(
                para(r"\textbf{Formalized, but probably classical}", width=3.78, size=23, color=SINE),
                wrapped_bullets(
                    r"Universal projection-displacement lower bound",
                    r"Sharp class-uniform secant bound",
                    r"Projector trace identities and simple exact optima",
                    width=3.78,
                    size=21,
                ),
            ).arrange(DOWN, aligned_edge=LEFT, buff=0.2),
            color=SINE,
            pad=0.22,
        )
        right = boxed(
            VGroup(
                para(r"\textbf{Do not oversell yet}", width=3.78, size=23, color=TRIAL),
                wrapped_bullets(
                    r"Higher-rank complex Schatten formula",
                    r"Global real matching and sorted-pair reductions",
                    r"Sharp trace and smoothed real-complex gaps",
                    width=3.78,
                    size=21,
                ),
            ).arrange(DOWN, aligned_edge=LEFT, buff=0.2),
            color=TRIAL,
            pad=0.22,
        )
        row = VGroup(left, mid, right).arrange(RIGHT, buff=0.26, aligned_edge=UP)
        row.scale_to_fit_width(12.7)
        row.move_to([0.0, self.content_top - 1.85, 0.0])

        finish = para(
            r"If you want one headline: \emph{the repository already contains a"
            r" formalized exact theory of complex smoothed spectral transport, including"
            r" an explicit optimizer and a quantitative stability inequality.} That is"
            r" the anchor. The broader Schatten and real-field theories are the next"
            r" frontier.",
            width=12.15,
            size=24,
            color=MUTED,
        ).move_to([0.0, -3.0, 0.0])

        self.say(
            "This final slide is the practical summary. It tells you what to claim as"
            " completed mathematics, what to present as useful but probably classical," 
            " and what to keep clearly marked as active research rather than a finished"
            " theorem."
        )
        self.play(FadeIn(row), FadeIn(finish), run_time=1.0)
