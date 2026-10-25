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
    Circle,
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

from dkvis.novelty_layout import resolved_region
from dkvis.novelty_math import (
    optimal_phase_three_halves,
    schatten_signed_phase_power_three_halves,
    schatten_simple_active_signs_three_halves,
)
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


def place(slide: DeckSlide, slot: str, mob, *, align_top: bool = False):
    """Place a completely rendered Manim group inside a reserved region.

    This is important for dynamic LaTeX dimensions: an object is fit by both
    width *and* height, and never laid across another region or the footer.
    `align_top` keeps neighboring cards aligned when their heights differ.
    """
    header_bottom = None if isinstance(slide, N00Title) else slide.content_top
    rect = resolved_region(type(slide).__name__, slot, header_bottom)
    if rect.width <= 0 or rect.height <= 0:
        raise ValueError(f"invalid novelty layout cell: {type(slide).__name__}/{slot}: {rect}")
    inset = 0.045
    available_w = rect.width - 2 * inset
    available_h = rect.height - 2 * inset
    if mob.width <= 0 or mob.height <= 0:
        raise ValueError(f"empty Manim object: {type(slide).__name__}/{slot}")
    factor = min(1, available_w / mob.width, available_h / mob.height)
    if factor < 1:
        mob.scale(factor)
    x = (rect.left + rect.right) / 2
    y = (rect.top - inset - mob.height / 2 if align_top
         else (rect.bottom + rect.top) / 2)
    mob.move_to([x, y, 0])
    eps = 0.001
    if (mob.get_left()[0] < rect.left - eps or mob.get_right()[0] > rect.right + eps
            or mob.get_bottom()[1] < rect.bottom - eps or mob.get_top()[1] > rect.top + eps):
        raise RuntimeError(f"object exceeded novelty layout cell: {type(slide).__name__}/{slot}")
    return mob



def principal_plane(theta: float = 0.9, *, show_caption: bool = True) -> VGroup:
    """A simple 2D principal-plane picture with the same role colors as the
    Manim role palette: source subspace amber, target subspace blue,
    turning angle magenta.  This matches the paper's transport notation;
    older sine-theta slides retain their own exact-wanted/trial meanings.
    """

    origin = np.array([0.0, 0.0, 0.0])
    radius = 2.15
    x_axis = axis_line(origin + LEFT * 2.5, origin + RIGHT * 2.6)
    y_axis = axis_line(origin + DOWN * 2.0, origin + UP * 2.15)
    u = Line(origin, origin + np.array([radius, 0.0, 0.0]), color=TRIAL, stroke_width=5)
    v = Line(
        origin,
        origin + np.array([radius * np.cos(theta), radius * np.sin(theta), 0.0]),
        color=WANTED,
        stroke_width=5,
    )
    u_back = Line(origin, origin + np.array([-0.55 * radius, 0.0, 0.0]), color=TRIAL, stroke_width=3, stroke_opacity=0.45)
    v_back = Line(
        origin,
        origin + np.array([-0.55 * radius * np.cos(theta), -0.55 * radius * np.sin(theta), 0.0]),
        color=WANTED,
        stroke_width=3,
        stroke_opacity=0.45,
    )
    dot = Dot(origin, radius=0.04, color=FG)
    ang = Arc(radius=0.72, start_angle=0.0, angle=theta, color=SINE, stroke_width=4)
    u_lab = math(r"\sym{Usource}", size=30, color=TRIAL).move_to(origin + np.array([2.45, -0.25, 0.0]))
    v_lab = math(r"\sym{Vtarget}", size=30, color=WANTED).move_to(origin + np.array([2.05 * np.cos(theta) + 0.42, 2.05 * np.sin(theta) + 0.15, 0.0]))
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
    # Each label belongs to its own half of the axis.  In the first handout,
    # longer text overlapped across the midpoint even though the entire strip
    # fit inside the slide.  Internal geometry needs a bound too.
    left_lab = tex(left, size=21, color=MUTED)
    right_lab = tex(right, size=21, color=MUTED)
    for label in (left_lab, right_lab):
        if label.width > 2.42:
            label.scale_to_fit_width(2.42)
    left_lab.next_to(axis, DOWN, aligned_edge=LEFT, buff=0.16)
    right_lab.next_to(axis, DOWN, aligned_edge=RIGHT, buff=0.16)
    top = math(tag, size=28, color=GAP).next_to(tick, UP, buff=0.12)
    if left_lab.get_right()[0] + 0.2 > right_lab.get_left()[0]:
        raise RuntimeError("threshold-strip labels collide")
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


class N00Title(DeckSlide):
    section = ""

    def body(self) -> None:
        self.say(
            "Title. This deck is a standalone tour of the mathematical program that"
            " grows beyond the classical Davis-Kahan story: optimizing ambient"
            " transport penalties between subspaces, separating what is already"
            " formalized from what is still conjectural or only drafted."
        )
        title = place(self, "title", tex(r"What is the new math we are building?", size=56))
        sub = place(self, "subtitle", tex(
            r"A standalone tour of spectral-penalty transport between subspaces",
            size=30, color=MUTED))
        link = place(self, "link", tex(
            r"Repository: AIQ-Kitware/aiq-dkps-formalization", size=18, color=MUTED))

        pic = place(self, "diagram", principal_plane(theta=0.94, show_caption=False))
        thesis = VGroup(
            para(
                r"We already know the classical $\,\sin\Theta\,$ bounds and the"
                r" Proposition 4.4 refutation. The newer program asks a different"
                r" question: among all feasible ambient transports taking $\sym{Usource}$ to"
                r" $\sym{Vtarget}$, which one minimizes a chosen spectral penalty of"
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
        place(self, "prose", thesis)

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
                    r"an explicit optimizer and all global minimizers classified",
                    r"quadratic growth below and quartic growth through the cutoff",
                    r"exact uniqueness test and closest commuting-unitary correction",
                ],
            ),
            (
                r"3. Complete complex Schatten; open real theory",
                TRIAL,
                [
                    r"all-rank complex $1<p<2$ minimum and complete optimizer set proved",
                    r"every constrained local minimum is global",
                    r"multiplicity spaces determine discrete or continuous optimal families",
                    r"unrestricted real matching and sharp real-complex gaps remain research",
                ],
            ),
        ]
        for heading, color, items in specs:
            head = para(r"\textbf{" + heading + "}", width=3.75, size=24, color=color)
            body = wrapped_bullets(*items, width=3.65, size=20, buff=0.13)
            card = VGroup(head, body).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
            cols.append(boxed(card, color=color, pad=0.22))
        for slot, card in zip(("a", "b", "c"), cols):
            place(self, slot, card, align_top=True)

        summary = para(
            r"The key novelty question is therefore not a yes/no label on the whole"
            r" repository. The right question is: \emph{which exact theorem, in which"
            r" field, for which cost, is completed and plausibly first-publication?}",
            width=12.3,
            size=25,
        )
        place(self, "takeaway", summary)

        self.say(
            "This review separates source formalization, the completed complex"
            " smoothed theory, and the Schatten and real-field program. The new"
            " all-rank complex Schatten minimum and all optimizers are formalized."
            " Real matching and field-gap claims remain working mathematical drafts."
        )
        self.play(*[FadeIn(card) for card in cols], FadeIn(summary), run_time=1.0)


class N02OptimizationProblem(DeckSlide):
    title = "The optimization problem"
    kicker = r"Feasible transporters are constrained by the subspaces, and the cost is a spectral penalty of $I-W$"
    section = SECTION

    def body(self) -> None:
        pic = principal_plane(theta=0.88).scale(1.05)
        place(self, "diagram", pic)

        defs = VGroup(
            math(r"W(\sym{Usource}) = \sym{Vtarget}", size=34),
            math(r"D_{\rho}(\sym{Usource},\sym{Vtarget}) = \min_{W:\,W\sym{Usource}=\sym{Vtarget}} \sum_j \rho\!\left(\sigma_j(I-W)\right)", size=29),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        place(self, "definitions", defs)

        costs = VGroup(
            piece_box(r"\rho(s)=s", r"\text{trace / nuclear displacement}", size=25, role=WANTED),
            piece_box(r"\rho(s)=s^p", r"\text{Schatten-}p\text{ power}", size=25, role=TRIAL),
            piece_box(r"\rho_{\tau}(s)=\sqrt{\tau^2+s^2}-\tau", r"\text{smoothed / Charbonnier penalty}", size=25, role=CURRENT),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.22)
        place(self, "costs", costs)

        note = para(
            r"This is an \emph{extrinsic} optimization problem in the ambient space."
            r" The cost sees the singular values of $I-W$, not just the geodesic"
            r" distance on the Grassmannian and not just the projection distance.",
            width=6.2,
            size=23,
            color=MUTED,
        )
        place(self, "note", note)

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
        left = place(self, "diagram", principal_plane(theta=0.78))
        floor = VGroup(
            tex(r"For every unitarily invariant seminorm $N$ and every feasible $W$:", size=25, color=MUTED),
            math(r"N(\sym{ProjSource}-\sym{ProjTarget}) \le N(I-W)", size=38),
            math(r"N\!\left(\left|\sym{ProjSource}-\sym{ProjTarget}\right|\right) \le N(I-W)", size=34, color=SINE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        floor_box = place(self, "theorem", boxed(floor, color=SINE, pad=0.25))

        points = wrapped_bullets(
            r"No acute-angle assumption is needed",
            r"No singular-value enumeration is needed in the proof",
            r"The projection floor works for every unitarily invariant norm",
            r"Likely classical mathematics, but essential to our exact transport results",
            width=5.75,
            size=22,
        )
        place(self, "bullets", points)

        tag = para(
            r"Interpretation: the projections already tell you how much turning must"
            r" happen. Any feasible ambient unitary has to pay at least that much.",
            width=6.1,
            size=24,
            color=MUTED,
        )
        place(self, "note", tag)

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
            math(r"\min_{W:\,W\sym{Usource}=\sym{Vtarget}} \norm{I-W}_{1} = \operatorname{tr}\left|\sym{ProjSource}-\sym{ProjTarget}\right| = 2\sum_{i=1}^{k} \sin\theta_i", size=33),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        theorem_box = place(self, "theorem", boxed(theorem, color=WANTED, pad=0.24))

        phase = VGroup(
            tex(r"Optimal transporter (one explicit form):", size=25, color=MUTED),
            math(r"T_{\star}=R(C-iS)\quad\text{or}\quad R(C+iS)", size=34, color=CURRENT),
            math(r"C=\cos\Theta,\qquad S=\left|\sym{ProjSource}-\sym{ProjTarget}\right|", size=31, color=SINE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.16)
        place(self, "construction", phase)

        explain = wrapped_bullets(
            r"The direct rotation $R$ is \textbf{not} always trace-optimal",
            r"Opposite complex phases split displacement into positive and negative parts",
            r"Each principal plane contributes exactly $2\sin\theta_i$",
            r"Exact global formula formalized; mathematical priority still under review",
            width=5.6,
            size=21,
        )
        place(self, "bullets", explain)

        conclusion = place(self, "takeaway", tex(
            r"\textbf{The lower bound is attained exactly by a complex phase-corrected transporter.}",
            size=23, color=MUTED))

        self.say(
            "For the complex trace problem the lower bound becomes the exact answer."
            " The minimum trace displacement equals the trace of the positive sine"
            " operator, or equivalently twice the sum of the principal sines. The"
            " direct rotation itself may fail to minimize trace cost, but a phase-"
            " corrected version does."
        )
        self.play(FadeIn(theorem_box), FadeIn(phase), FadeIn(explain), FadeIn(conclusion), run_time=1.1)


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
        top_box = place(self, "identities", boxed(top, color=CURRENT, pad=0.22))

        left = piece_box(
            r"\mu_{\tau}(\theta)=2\left(\sqrt{\tau^2+2-2\cos\theta}-\tau\right),\quad \theta\le \theta_c(\tau)",
            r"\mu_{\tau}(\theta)=2\eta\sin\theta-2\tau,\quad \theta\ge \theta_c(\tau)",
            size=23,
            role=WANTED,
        )
        place(self, "cost", left)

        right = VGroup(
            tex(r"Global complex equal-rank minimum:", size=24, color=MUTED),
            math(r"\min_{W:\,W\sym{Usource}=\sym{Vtarget}} \Psi_{\tau}(W)=\sum_{i=1}^{k} \mu_{\tau}(\theta_i)", size=30),
            tex(r"Above the threshold, a nonzero phase correction appears:", size=24, color=MUTED),
            math(r"\delta_{\star}(\theta)=\arccos\!\left(\eta^{2}\cos\theta\right)\qquad (\theta\ge \theta_c(\tau))", size=29, color=SINE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.15)
        place(self, "minimum", right)

        strip = place(self, "threshold", threshold_strip(
            r"$\theta<\theta_c$: no phase correction",
            r"$\theta>\theta_c$: nonzero phase",
            tag=r"\theta_c(\tau)"))

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
        statement_box = place(self, "theorem", boxed(statement, color=CURRENT, pad=0.24))

        left = wrapped_bullets(
            r"This is an \emph{error bound}, not only existence of a minimizer",
            r"It applies to every admissible unitary, including mixed principal planes",
            r"The growth coefficient is explicit and positive in the strict subcritical regime",
            r"This quantifies \emph{robustness}: small cost error forces small rotation error",
            width=5.7,
            size=21,
        )
        place(self, "bullets", left)

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
        place(self, "interpretation", right)

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
        theorem_box = place(self, "theorem", boxed(theorem, color=TRIAL, pad=0.22))

        left_plot, _ = self._phase_curve(theta=np.deg2rad(45), p=1.5, height=2.0, width=4.2)
        right_plot, delta_star = self._phase_curve(theta=np.deg2rad(80), p=1.5, height=2.0, width=4.2)
        place(self, "left_plot", left_plot)
        place(self, "right_plot", right_plot)
        left_caption = para(
            r"Below the cutoff: the minimum stays at $\delta=0$.",
            width=5.2, size=21, color=MUTED,
        )
        place(self, "left_caption", left_caption)
        right_caption = para(
            rf"Above the cutoff: the optimal phase is $\delta_\star\approx {delta_star * 180 / np.pi:.1f}^\circ$.",
            width=5.2, size=21, color=MUTED,
        )
        place(self, "right_caption", right_caption)

        self.say(
            "For Schatten powers between one and two, there is a real symmetry-"
            " breaking phase transition. In a principal plane the optimization reduces"
            " to a one-variable problem in the phase delta, and the direct rotation is"
            " optimal exactly up to a sharp threshold angle."
        )
        self.play(FadeIn(theorem_box), FadeIn(left_plot), FadeIn(right_plot), FadeIn(left_caption), FadeIn(right_caption), run_time=1.2)


class N07GlobalSchatten(DeckSlide):
    """All-rank complex theorem: the genuinely new lower-bound statement."""

    title = "From one plane to every complex subspace"
    kicker = r"The missing step is now proved: mixing principal planes cannot reduce the Schatten minimum"
    section = SECTION

    def body(self) -> None:
        top = VGroup(
            tex(r"Formalized global result: equal-rank complex subspaces, $1<p<2$", size=23, color=MUTED),
            math(
                r"\min_{\sym{Wcompetitor}:\,\sym{Wcompetitor}(\sym{Usource})=\sym{Vtarget}}"
                r"\norm{I-\sym{Wcompetitor}}_p^p"
                r"=\sum_{j=1}^{k}m_p(\theta_j)", size=34,
            ),
            math(r"\sym{Rrotation}\text{ is optimal}\iff"
                 r"\max_j\theta_j\le\arccos\!\left(\frac{2-p}{p}\right)", size=29, color=GAP),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.15)
        theorem = place(self, "theorem", boxed(top, color=CURRENT, pad=0.20))

        model = VGroup(
            VGroup(
                principal_plane(theta=np.deg2rad(45), show_caption=False),
                tex(r"$\theta_1=45^\circ$", size=25, color=SINE),
            ).arrange(DOWN, buff=0.11),
            VGroup(
                principal_plane(theta=np.deg2rad(80), show_caption=False),
                tex(r"$\theta_2=80^\circ$", size=25, color=SINE),
            ).arrange(DOWN, buff=0.11),
        ).arrange(RIGHT, buff=0.27, aligned_edge=DOWN)
        diagram = place(self, "planes", model)

        from dkvis.novelty_math import schatten_two_angle_example_three_halves
        v = schatten_two_angle_example_three_halves()
        facts = VGroup(
            tex(r"Example: $p=3/2$ on two planes", size=25, color=MUTED),
            math(r"\theta_c=\arccos(1/3)\approx 70.53^\circ", size=26, color=GAP),
            math(r"m_{3/2}(45^\circ)\approx1.33917", size=27, color=WANTED),
            math(r"m_{3/2}(80^\circ)\approx2.75418", size=27, color=CURRENT),
            math(r"\min\norm{I-W}_{3/2}^{3/2}\approx4.09335", size=27, color=CURRENT),
            math(r"\norm{I-\mathcal R}_{3/2}^{3/2}\approx4.25442", size=25, color=TRIAL),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        assert np.isclose(v["global_sum"], 4.093350305605767, atol=2e-6)
        assert np.isclose(v["canonical_sum"], 4.254419090242005, atol=2e-6)
        numbers = place(self, "numbers", facts)

        conclusion = place(self, "takeaway", para(
            r"Optimizing each plane constructs an upper bound; the new Lean theorem"
            r" proves the matching lower bound against \emph{every} unitary transporter.",
            width=12.2, size=23, color=MUTED,
        ))
        self.say(
            "Previously we only had the solution in one principal plane."
            " We now have the exact minimum for any equal-rank complex subspaces,"
            " even if a candidate ambient unitary mixes planes. The right side is"
            " a sum of independently optimized scalar costs, and the theorem"
            " proves no other admissible unitary can beat it. In the two-angle"
            " example with p three halves, the canonical rotation is strictly"
            " more expensive than the global optimum."
        )
        self.play(FadeIn(theorem), FadeIn(diagram), FadeIn(numbers), FadeIn(conclusion), run_time=1.1)


class N07NoMixingProof(DeckSlide):
    """Proof intuition: stationarity, spectral blocks, negative curvature."""

    title = "Why arbitrary mixing cannot beat the sum"
    kicker = r"The global lower bound comes from a constrained-gradient and second-variation argument"
    section = SECTION

    def body(self) -> None:
        header = VGroup(
            tex(r"At a cost-minimizing feasible transporter:", size=25, color=MUTED),
            math(r"J G_p(W) J = - G_p(W),\qquad J=2P-I", size=34, color=GAP),
            math(r"\norm{I-W}_p^p\ \ge\ \sum_j m_p(\theta_j)", size=32, color=CURRENT),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.13)
        theorem = place(self, "theorem", boxed(header, color=CURRENT, pad=0.20))

        stages = VGroup(
            boxed(VGroup(
                math(r"G_p(W)", size=28, color=GAP),
                tex(r"spectral gradient", size=20, color=MUTED),
            ).arrange(DOWN, buff=0.10), color=GAP, pad=0.18),
            tex(r"$\Downarrow$", size=28, color=MUTED),
            boxed(VGroup(
                math(r"H_g\oplus H_{-g}", size=26, color=SINE),
                tex(r"paired phase blocks", size=20, color=MUTED),
            ).arrange(DOWN, buff=0.10), color=SINE, pad=0.18),
            tex(r"$\Downarrow$", size=28, color=MUTED),
            boxed(VGroup(
                math(r"AB=0", size=27, color=CURRENT),
                tex(r"no overlapping large-phase blocks", size=20, color=MUTED),
            ).arrange(DOWN, buff=0.10), color=CURRENT, pad=0.18),
        ).arrange(DOWN, buff=0.09)
        diagram = place(self, "flow", stages)

        reasoning = wrapped_bullets(
            r"First variation forces the gradient to exchange the source and complementary blocks.",
            r"At positive gradient levels, phases occur in paired small/large roots.",
            r"Overlapping large-phase projections give a feasible direction of \emph{negative second variation}; that contradicts minimality.",
            r"Zero-gradient blocks receive a separate projection-distance lower bound.",
            r"Each remaining invariant plane pays at least its own scalar minimum.",
            width=5.75, size=21, buff=0.13,
        )
        steps = place(self, "argument", reasoning)

        footer = place(self, "takeaway", para(
            r"This certifies a global result, not an assumption that the optimizer"
            r" happens to preserve chosen coordinates. The proof covers repeated,"
            r" zero and right principal angles.",
            width=12.1, size=23, color=MUTED,
        ))
        self.say(
            "The proof does not merely test the block diagonal candidates."
            " It starts with an arbitrary minimizer, uses first variation to"
            " expose paired gradient subspaces, and then negative second variation"
            " rules out overlapping large-phase blocks. The zero-gradient part"
            " has its own lower bound. That forces a sum of the scalar plane"
            " costs even if the original candidate could mix planes."
        )
        self.play(FadeIn(theorem), FadeIn(diagram), FadeIn(steps), FadeIn(footer), run_time=1.1)


class N07OptimizerChoices(DeckSlide):
    """Two distinct active simple angles produce exactly four optimizers."""

    title = "Two active angles: exactly four optimal transports"
    kicker = r"Each distinct simple supercritical angle makes an independent positive/negative phase choice"
    section = SECTION

    def body(self) -> None:
        example = schatten_simple_active_signs_three_halves()
        assert len(example["choices"]) == 4
        assert max(example["costs"]) - min(example["costs"]) < 1e-10
        header = VGroup(
            tex(r"Finite complex Schatten $p=3/2$: $75^\circ$ and $80^\circ$ are both above the cutoff", size=24, color=MUTED),
            math(r"\#\mathcal M_{3/2}=2^s=4\qquad(s=2,\ \text{no right-angle defect})", size=33, color=CURRENT),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.15)
        theorem = place(self, "theorem", boxed(header, color=CURRENT, pad=0.20))

        # A square is the product of two independent Boolean phase choices.
        coords = {(-1, 1): (-1.85, 0.83), (1, 1): (1.85, 0.83),
                  (-1, -1): (-1.85, -0.83), (1, -1): (1.85, -0.83)}
        edges = VGroup(
            Line([*coords[(-1, 1)], 0], [*coords[(1, 1)], 0], color=FAINT, stroke_width=3),
            Line([*coords[(-1, -1)], 0], [*coords[(1, -1)], 0], color=FAINT, stroke_width=3),
            Line([*coords[(-1, 1)], 0], [*coords[(-1, -1)], 0], color=FAINT, stroke_width=3),
            Line([*coords[(1, 1)], 0], [*coords[(1, -1)], 0], color=FAINT, stroke_width=3),
        )
        labels = VGroup()
        points = VGroup()
        for (sgn_a, sgn_b), (x, y) in coords.items():
            points.add(Dot([x, y, 0], radius=0.10, color=SINE))
            signs = ("+" if sgn_a > 0 else "-", "+" if sgn_b > 0 else "-")
            lab = math(rf"({signs[0]}\delta_1,{signs[1]}\delta_2)", size=31, color=SINE)
            lab.move_to([x + (0.65 if x > 0 else -0.65), y + (0.12 if y > 0 else -0.12), 0])
            labels.add(lab)
        square = place(self, "square", VGroup(edges, points, labels))

        right = VGroup(
            tex(r"Four distinct feasible transports:", size=26, color=MUTED),
            math(r"\delta_1\approx57.55^\circ,\qquad\delta_2\approx74.57^\circ", size=28, color=SINE),
            tex(r"Each of the four phase-sign combinations", size=23),
            tex(r"attains the same global displacement cost.", size=23),
            math(r"\min\norm{I-W}_{3/2}^{3/2}\approx5.39884", size=28, color=CURRENT),
            para(
                r"The formalized classification proves there are exactly four;"
                r" constructing four attaining candidates alone would not exclude others.",
                width=5.5, size=23, color=MUTED,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.15)
        explanation = place(self, "explain", right)
        takeaway = place(self, "takeaway", para(
            r"For $s$ distinct simple active angles and no right-angle defect,"
            r" all ambient global optimizers form a set of exactly $2^s$ elements.",
            width=12.1, size=24, color=MUTED,
        ))
        self.say(
            "Both principal angles exceed the exact critical angle. Each one permits"
            " an independent positive or negative optimal phase. In this example"
            " there are four choices, represented by the four corners of a square."
            " The Lean theorem proves that these are all the global optimizers,"
            " rather than just four examples we happened to construct."
        )
        self.play(FadeIn(theorem), FadeIn(square), FadeIn(explanation), FadeIn(takeaway), run_time=1.0)


class N07MultiplicityFamilies(DeckSlide):
    """Repeated active eigenangles replace Boolean signs by projection spaces."""

    title = "Repeated angles create continuous optimizer families"
    kicker = r"One angle with multiplicity two already has infinitely many globally minimizing phase choices"
    section = SECTION

    def body(self) -> None:
        header = VGroup(
            tex(r"For each distinct supercritical interior angle $\theta$ of multiplicity $m_\theta$:",
                size=24, color=MUTED),
            math(r"\text{phase choices}\ \simeq\ \coprod_{r=0}^{m_\theta}\operatorname{Gr}_{\mathbb C}(r,m_\theta)",
                 size=33, color=SINE),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.14)
        theorem = place(self, "theorem", boxed(header, color=SINE, pad=0.18))

        # Several rank-one projections are drawn as a *real slice* of all
        # complex lines in C^2; this is illustrative, not a topology proof.
        circle = Circle(radius=1.18, color=FAINT, stroke_width=2)
        lines = VGroup()
        for angle in (0.14, 0.57, 1.02, 1.43):
            direction = np.array([np.cos(angle), np.sin(angle), 0])
            lines.add(Line(-1.15 * direction, 1.15 * direction,
                           color=SINE, stroke_width=4, stroke_opacity=0.72))
        center = Dot(radius=0.055, color=FG)
        caption = tex(r"real slice of rank-one complex projections", size=22, color=MUTED)
        geometry = VGroup(circle, lines, center, caption)
        caption.next_to(circle, DOWN, buff=0.20)
        picture = place(self, "diagram", geometry)

        explanation = VGroup(
            tex(r"Example: one active angle with $m_\theta=2$", size=26, color=MUTED),
            math(r"\operatorname{Gr}_{\mathbb C}(0,2)\ \sqcup"
                 r"\ \operatorname{Gr}_{\mathbb C}(1,2)\ \sqcup"
                 r"\ \operatorname{Gr}_{\mathbb C}(2,2)", size=26, color=SINE),
            wrapped_bullets(
                r"Ranks zero and two each give one projection.",
                r"Rank one can select any complex line in $\mathbb C^2$.",
                r"A right-angle defect contributes an independent unitary factor.",
                width=5.0, size=22,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        explain = place(self, "explain", explanation)

        takeaway = place(self, "takeaway", para(
            r"The Lean result is an algebraic bijection of optimizer sets."
            r" No homeomorphism, connected-component, or manifold-dimension theorem is claimed.",
            width=12.0, size=23, color=MUTED,
        ))
        self.say(
            "With repeated supercritical angles, the optimal phase is no longer a"
            " separate binary choice for each coordinate. We instead choose an"
            " arbitrary projection on the whole multiplicity space. For multiplicity"
            " two, the rank-one choices already form a continuum of complex lines."
            " The drawing shows just a real slice. The formalization establishes the"
            " full algebraic parameterization, not yet its topology."
        )
        self.play(FadeIn(theorem), FadeIn(picture), FadeIn(explain), FadeIn(takeaway), run_time=1.0)


class N07LocalGlobal(DeckSlide):
    """Planar visual for the all-ambient no-nonglobal-local-minimum theorem."""

    title = "Every constrained Schatten local minimum is global"
    kicker = r"A planar double-well illustrates the theorem; the Lean result covers every feasible ambient unitary"
    section = SECTION

    def body(self) -> None:
        header = VGroup(
            tex(r"For finite-dimensional complex subspace transport, $1<p<2$:", size=25, color=MUTED),
            math(r"W\text{ locally minimizes }\norm{I-W}_p^p\ \Longrightarrow"
                 r"\ W\text{ globally minimizes }\norm{I-W}_p^p", size=31, color=CURRENT),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        theorem = place(self, "theorem", boxed(header, color=CURRENT, pad=0.19))

        theta = np.deg2rad(80.0)
        delta_star = optimal_phase_three_halves(theta)
        # Clip floating-point plot samples to the closed admissible phase interval.
        fun = lambda d: schatten_signed_phase_power_three_halves(
            theta, float(np.clip(d, -theta, theta)))
        ymin = fun(delta_star)
        ymax = fun(0.0)
        axes = Axes(
            x_range=[-theta, theta, theta / 2],
            y_range=[ymin - 0.04, ymax + 0.04, 0.08],
            x_length=5.25,
            y_length=2.05,
            axis_config={"color": FAINT, "stroke_width": 2}, tips=False,
        )
        curve = axes.plot(fun, x_range=[-theta, theta], color=SINE, stroke_width=4)
        left = Dot(axes.c2p(-delta_star, ymin), radius=0.075, color=CURRENT)
        right = Dot(axes.c2p(delta_star, ymin), radius=0.075, color=CURRENT)
        central = Dot(axes.c2p(0, ymax), radius=0.052, color=TRIAL)
        plot_label = tex(r"planar example: $p=3/2$, $\theta=80^\circ$", size=23, color=MUTED)
        bottom = tex(r"phase $\delta$  (two global minima $\pm\delta_\star$)", size=22, color=MUTED)
        chart = VGroup(axes, curve, left, right, central, plot_label, bottom)
        plot_label.next_to(axes, UP, buff=0.12)
        bottom.next_to(axes, DOWN, buff=0.13)
        plot = place(self, "plot", chart)

        explanation = VGroup(
            tex(r"Global theorem: no spurious constrained local minima", size=25, color=CURRENT),
            wrapped_bullets(
                r"All feasible ambient unitaries, including plane-mixing ones.",
                r"Repeated, zero, critical, and right principal angles included.",
                r"Nearest unitary commuting with a projection inherits the result.",
                r"The theorem does not assert convergence of a numerical solver.",
                width=5.0, size=22, buff=0.13,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.15)
        explain = place(self, "explain", explanation)

        takeaway = place(self, "takeaway", para(
            r"The planar plot is a scalar illustration. The formalized theorem rules"
            r" out nonglobal local minima in the complete constrained unitary space.",
            width=12.1, size=23, color=MUTED,
        ))
        self.say(
            "The curve shows the symmetry-breaking scalar phase for a single"
            " supercritical angle. It has two equally optimal phases. The actual"
            " theorem is more powerful: on the full constrained space of complex"
            " unitary transporters, every local minimum is global. The property"
            " also transfers to nearest unitary corrections that preserve a"
            " prescribed subspace."
        )
        self.play(FadeIn(theorem), FadeIn(plot), FadeIn(explain), FadeIn(takeaway), run_time=1.0)


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
                    r"The all-rank complex Schatten $1<p<2$ optimum and all minimizers are classified",
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
        place(self, "complex", complex_box, align_top=True)
        place(self, "real", real_box, align_top=True)

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
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        place(self, "takeaway", bottom)

        self.say(
            "This is the conceptual split to keep in mind. Over the complex field, the"
            " optimizer can adjust a phase continuously on each principal plane. Over"
            " the real field, that freedom disappears and the problem turns into block"
            " matching. So the real problem is structurally different, not just a"
            " weaker copy of the complex one."
        )
        self.play(FadeIn(complex_box), FadeIn(real_box), FadeIn(bottom), run_time=1.0)


class N09StatusBoard(DeckSlide):
    title = "What the current formalization proves"
    kicker = r"Exact optimization and critical stability are certified; global real matching remains research"
    section = SECTION

    def body(self) -> None:
        left = boxed(
            VGroup(
                para(r"\textbf{Safe strong claims}", width=3.78, size=23, color=CURRENT),
                wrapped_bullets(
                    r"Smoothed exact value and all optimizer families",
                    r"Uniqueness and quartic critical growth",
                    r"Exact commuting-unitary correction criterion",
                    r"All-rank complex Schatten minimum and exact cutoff",
                    r"Every minimizer classified; local minima global",
                    r"Exactly $2^s$ simple active-angle choices",
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
                    r"Topology of the complex optimizer families",
                    r"Global real matching and sorted-pair reductions",
                    r"Infinite-dimensional ideal optimization and sharp field gaps",
                    width=3.78,
                    size=21,
                ),
            ).arrange(DOWN, aligned_edge=LEFT, buff=0.2),
            color=TRIAL,
            pad=0.22,
        )
        place(self, "strong", left, align_top=True)
        place(self, "classical", mid, align_top=True)
        place(self, "working", right, align_top=True)

        finish = para(
            r"The complete finite-dimensional complex Schatten theory now gives the"
            r" exact value, every optimizer, and no nonglobal local minima."
            r" Smoothed transport has analogous global-optimizer geometry and"
            r" critical stability. Historical first-publication priority remains open.",
            width=12.15,
            size=24,
            color=MUTED,
        )
        place(self, "takeaway", finish)

        self.say(
            "This final slide is the practical summary. It tells you what to claim as"
            " completed mathematics, what to present as useful but probably classical," 
            " and what to keep clearly marked as active research rather than a finished"
            " theorem."
        )
        self.play(FadeIn(left), FadeIn(mid), FadeIn(right), FadeIn(finish), run_time=1.0)


class N06CriticalFlatness(DeckSlide):
    """The formalized order-four transition, distinguished from quadratic growth."""

    title = "At the cutoff, stability becomes quartic"
    kicker = r"The canonical rotation remains uniquely optimal at equality, but quadratic growth fails there"
    section = SECTION

    def body(self) -> None:
        formulas = VGroup(
            tex(r"For $n\ge1$ and all principal angles $\theta_j\le\theta_c(\tau)$:", size=25, color=MUTED),
            math(
                r"\Psi_{\tau}(W)-\Psi_{\tau}(R)"
                r"\ \ge\ \frac{3\tau}{32\eta^4n}\,\norm{W-R}_F^4",
                size=34, color=CURRENT,
            ),
            tex(r"At equality a critical principal plane has genuinely fourth-order cost growth.", size=23, color=MUTED),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.14)
        theorem = place(self, "theorem", boxed(formulas, color=CURRENT, pad=0.20))

        # Literal scalar-phase cost excess G(e^{it}), from SmoothedCriticalFlatness.
        # The quadratic guide agrees at t=0.8; it is not a lower bound.
        from dkvis.novelty_math import critical_phase_excess

        tau = 1.0
        stop = 0.8
        xmax = 0.9
        y_top = 0.035
        axes = Axes(
            x_range=[0, xmax, 0.2], y_range=[0, y_top, 0.01],
            x_length=5.0, y_length=2.5,
            axis_config={"color": FAINT, "stroke_width": 2}, tips=False,
        )
        actual = axes.plot(
            lambda t: critical_phase_excess(tau, t), x_range=[0, stop],
            color=CURRENT, stroke_width=4,
        )
        endpoint = critical_phase_excess(tau, stop)
        quadratic = axes.plot(
            lambda t: endpoint * (t / stop) ** 2, x_range=[0, stop],
            color=MUTED, stroke_width=2,
        )
        xlab = math(r"t", size=23).next_to(axes.get_x_axis(), DOWN, buff=0.12)
        axis_title = tex(r"critical phase path, $\tau=1$", size=23, color=MUTED).next_to(axes, UP, buff=0.12)
        leg = VGroup(
            tex(r"solid: actual objective gap", size=19, color=CURRENT),
            tex(r"gray: matched quadratic guide", size=19, color=MUTED),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08).next_to(xlab, DOWN, buff=0.10)
        chart = VGroup(axes, actual, quadratic, xlab, axis_title, leg)
        place(self, "plot", chart)

        lessons = wrapped_bullets(
            r"At $\theta_j<\theta_c$, every near-minimizer obeys a quadratic bound.",
            r"At $\theta_j=\theta_c$, uniqueness persists and a quartic bound holds globally.",
            r"The planar phase excess is asymptotic to a positive multiple of $|z-1|^4$.",
            r"No positive quadratic-growth coefficient works locally on the critical plane.",
            width=5.75, size=22, buff=0.17,
        )
        place(self, "explanation", lessons)

        takeaway = para(
            r"The fourth-order exponent is optimal at the transition."
            r" The displayed global constant is explicit, but no claim of its"
            r" sharpness is made.",
            width=12.2, size=24, color=GAP,
        )
        place(self, "takeaway", takeaway)
        self.say(
            "The new formalized result goes beyond subcritical quadratic stability."
            " At the exact phase cutoff, the canonical rotation remains unique,"
            " but the objective grows to fourth rather than second order along a"
            " real feasible phase path. The chart shows the literal critical cost"
            " compared with a quadratic guide chosen to agree at the right endpoint."
        )
        self.play(FadeIn(theorem), FadeIn(chart), FadeIn(lessons), FadeIn(takeaway), run_time=1.1)


class N08CommutingCorrection(DeckSlide):
    """An exact application: correcting a unitary to preserve one projection."""

    title = "An exact symmetry-preserving unitary correction"
    kicker = r"A commutator norm decides whether the canonical correction is uniquely optimal"
    section = SECTION

    def body(self) -> None:
        picture = VGroup(
            principal_plane(theta=0.90, show_caption=False),
            math(r"A(\sym{Usource})=\sym{Vtarget}", size=28),
        ).arrange(DOWN, buff=0.17)
        place(self, "diagram", picture)

        statement = VGroup(
            tex(r"Given a unitary $A$ and an orthogonal projection $P$:", size=24, color=MUTED),
            math(r"\mathcal E_\tau(A,C)=\sum_j\rho_\tau(\sigma_j(A-C))", size=28, color=CURRENT),
            math(
                r"\min_{\substack{C^*C=I\\CP=PC}}\ \mathcal E_\tau(A,C)"
                r"=\sum_j\mu_\tau(\theta_j)",
                size=29, color=CURRENT,
            ),
            math(r"C_{\mathrm{can}}=R^*A", size=29, color=WANTED),
            math(
                r"C_{\mathrm{can}}\text{ uniquely optimal}"
                r"\iff \norm{AP-PA}_{\mathrm{op}}\le\sqrt{1-\eta^{-4}}",
                size=30,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.16)
        theorem = place(self, "theorem", boxed(statement, color=CURRENT, pad=0.22))

        notes = wrapped_bullets(
            r"$C_*$ is an actual unitary preserving $\operatorname{ran}P$ and its complement.",
            r"$\norm{AP-PA}_{\mathrm{op}}$ can be computed without identifying every principal angle.",
            r"The inequality includes equality; above it, phase-adjusted minimizers are distinct.",
            r"The formal theorem covers arbitrary finite-dimensional complex unitary inputs.",
            width=6.20, size=21,
        )
        place(self, "bullets", notes)
        takeaway = para(
            r"The commuting condition is an exact mathematical constraint."
            r" Circuit locality, gate synthesis, and noise channels would impose"
            r" additional restrictions on the feasible correction.",
            width=12.1, size=23, color=MUTED,
        )
        place(self, "takeaway", takeaway)

        self.say(
            "Here is an application that follows exactly from the new theorem."
            " We start with a unitary A and an important subspace represented by"
            " projection P. We seek the closest unitary correction commuting with P."
            " The cutoff is a directly computable operator norm of the commutator."
            " Below and at the cutoff the canonical correction is uniquely optimal."
        )
        self.play(FadeIn(picture), FadeIn(theorem), FadeIn(notes), FadeIn(takeaway), run_time=1.1)


class N08NumericalCorrection(DeckSlide):
    """Two-angle computed example: spectral optimum versus canonical correction."""

    title = "A two-dimensional example"
    kicker = r"The same threshold separates a unique zero-phase correction from phase-adjusted optima"
    section = SECTION

    def body(self) -> None:
        from dkvis.novelty_math import (
            smoothing_radius, smoothed_cutoff, canonical_smoothed_cost,
            optimal_smoothed_cost, optimal_smoothed_phase,
        )

        tau = 1.0
        cutoff = np.rad2deg(smoothed_cutoff(tau))
        axes = Axes(
            x_range=[0, 90, 20], y_range=[0, 1.5, 0.5],
            x_length=6.0, y_length=3.5,
            axis_config={"color": FAINT, "stroke_width": 2}, tips=False,
        )
        canonical = axes.plot(
            lambda deg: canonical_smoothed_cost(tau, np.deg2rad(deg)),
            x_range=[0, 90], color=WANTED, stroke_width=3,
        )
        optimal = axes.plot(
            lambda deg: optimal_smoothed_cost(tau, np.deg2rad(deg)),
            x_range=[0, 90], color=CURRENT, stroke_width=4,
        )
        limit = DashedLine(
            axes.c2p(cutoff, 0), axes.c2p(cutoff, 1.40),
            color=GAP, stroke_width=2, dash_length=0.08,
        )
        marker = Dot(
            axes.c2p(cutoff, optimal_smoothed_cost(tau, np.deg2rad(cutoff))),
            radius=0.045, color=GAP,
        )
        xlabel = math(r"\sym{theta}\ (\text{degrees})", size=22).next_to(axes, DOWN, buff=0.12)
        legend = VGroup(
            tex(r"blue: canonical correction", size=20, color=WANTED),
            tex(r"steel: global minimum", size=20, color=CURRENT),
            math(r"\theta_c\approx 67.54^\circ", size=21, color=GAP),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08).next_to(axes, UP, buff=0.12)
        graph = VGroup(axes, canonical, optimal, limit, marker, xlabel, legend)
        place(self, "plot", graph)

        alpha = np.deg2rad(45)
        high = np.deg2rad(80)
        low_card = boxed(
            VGroup(
                math(r"\sym{theta}=45^\circ", size=30, color=SINE),
                tex(r"commutator norm $0.70711$", size=22, color=MUTED),
                math(r"C_*=I\quad\text{(unique)}", size=28),
                math(r"\mathcal E_{\min}=0.51856", size=26, color=CURRENT),
            ).arrange(DOWN, aligned_edge=LEFT, buff=0.13),
            color=WANTED, pad=0.23,
        )
        high_card = boxed(
            VGroup(
                math(r"\sym{theta}=80^\circ", size=30, color=SINE),
                tex(r"commutator norm $0.98481$", size=22, color=MUTED),
                math(r"C_\pm=e^{\pm i62.96^\circ}I", size=28, color=CURRENT),
                math(r"\mathcal E_{\min}=1.18690", size=26, color=CURRENT),
                math(r"\mathcal E(A,I)=1.25742", size=25, color=WANTED),
            ).arrange(DOWN, aligned_edge=LEFT, buff=0.13),
            color=TRIAL, pad=0.23,
        )
        # Non-renderer checks: the labels above must evaluate the exact model.
        assert np.isclose(optimal_smoothed_phase(tau, alpha), 0.0)
        assert np.isclose(np.rad2deg(optimal_smoothed_phase(tau, high)), 62.95971681332988, atol=1e-6)
        assert np.isclose(optimal_smoothed_cost(tau, high), 1.1869048335163286, atol=1e-6)
        assert np.isclose(smoothing_radius(tau), (1 + np.sqrt(5)) / 2)
        cards = VGroup(low_card, high_card).arrange(DOWN, aligned_edge=LEFT, buff=0.25)
        place(self, "examples", cards)

        final = para(
            r"For $P=\operatorname{diag}(1,0)$ and $A_\theta$ a real planar"
            r" rotation viewed as a complex unitary, both curves are exact."
            r" Above the cutoff the canonical correction $I$ costs more.",
            width=12.0, size=23, color=MUTED,
        )
        place(self, "takeaway", final)
        self.say(
            "For tau one, the critical angle is approximately 67.54 degrees."
            " At 45 degrees, the identity is the unique closest commuting correction."
            " At 80 degrees, a pair of nonzero scalar phases are globally optimal."
            " The gap between the blue canonical and steel optimal curves appears"
            " precisely above the violet cutoff."
        )
        self.play(FadeIn(graph), FadeIn(cards), FadeIn(final), run_time=1.1)
