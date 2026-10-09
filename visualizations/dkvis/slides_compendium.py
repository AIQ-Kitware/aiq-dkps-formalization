"""Chapter interludes for the long Davis--Kahan presentation.

These are navigation aids between substantial mathematical topics.  They use
only existing symbol colors and mathematical objects; the checked example
models and the scenes of the completed Kitware talk are left untouched.
"""

from __future__ import annotations

from pathlib import Path
from manim import (
    DOWN,
    LEFT,
    ORIGIN,
    RIGHT,
    UP,
    Create,
    FadeIn,
    Line,
    ReplacementTransform,
    SVGMobject,
    VGroup,
)
import numpy as np

from dkvis import sine_theta_story as story
from dkvis.components.common.geometry import Plane, angle_arc, ellipse, through_origin

from dkvis.slide_style import (
    CURRENT,
    FG,
    GAP,
    MUTED,
    OLD,
    PANEL,
    PERTURB,
    REFUTED,
    RESID,
    SINE,
    WANTED,
    DeckSlide,
    math,
    para,
    tex,
)


class C00LongTitle(DeckSlide):
    """A broader title for the four-theorem collection; the short talk is untouched."""

    section = ""

    def make_chrome(self):
        # This cover already contains its own paper citation at the bottom.
        # Avoid colliding with the long deck footer or a slide number.
        return None

    def body(self) -> None:
        title = tex("How far can an eigenspace turn?", size=61)
        title.move_to([0, 1.92, 0])
        subtitle = tex(
            r"Davis--Kahan: geometry, four theorems, and formal verification",
            size=33,
            color=MUTED,
        ).next_to(title, DOWN, buff=0.28)
        robot = SVGMobject(str(Path(__file__).resolve().parent / "assets" / "robot.svg"), height=0.33)
        credit = VGroup(
            tex("Presented by Jon Crall.", size=20, color=MUTED),
            robot,
            tex("Slides prepared with LLM assistance.", size=20, color=MUTED),
        ).arrange(RIGHT, buff=0.13).next_to(subtitle, DOWN, buff=0.23)
        link = tex("https://github.com/AIQ-Kitware/aiq-dkps-formalization", size=15, color=MUTED)
        link.next_to(credit, DOWN, buff=0.14)
        cite = tex(
            r"C.~Davis and W.~M.~Kahan, \emph{The rotation of eigenvectors by a perturbation.~III},"
            r" SIAM J.~Numer.~Anal.~7 (1970)",
            size=22,
            color=MUTED,
        ).to_edge(DOWN, buff=0.48)

        plane = Plane(ORIGIN + DOWN * 1.35, 0.62, rotate=np.radians(18))
        pair = story.PerturbedPair(gap=0.5, eps=0.3)
        old = ellipse(plane, pair.A, color=OLD, width=2)
        new = ellipse(plane, pair.perturbed, color=CURRENT, width=3)
        old_axis = through_origin(plane, [1, 0], 2.6, OLD, width=2)
        new_axis = through_origin(plane, pair.perturbed_top_eigenvector, 2.6, WANTED, width=4)
        arc = angle_arc(plane, [1, 0], pair.perturbed_top_eigenvector, 1.6, SINE, width=4)
        theta = math(r"\sym{theta}", size=32).move_to(
            plane(2.05 * story.unit(pair.theta / 2 - 0.08))
        )
        self.say(
            "Davis and Kahan's 1970 paper bounds the rotation of invariant subspaces under perturbation. "
            "We begin with the geometric sine-theta inequality, then examine the remaining angle theorems, "
            "a source counterexample, and what was verified by Lean."
        )
        self.play(FadeIn(title), FadeIn(subtitle), FadeIn(credit), FadeIn(link))
        self.play(Create(old), Create(old_axis), run_time=0.9)
        self.play(
            ReplacementTransform(old.copy(), new),
            ReplacementTransform(old_axis.copy(), new_axis),
            run_time=1.3,
        )
        self.play(Create(arc), FadeIn(theta), FadeIn(cite))


class CompendiumChapter(DeckSlide):
    """One consistent, quiet navigation frame for a long reference talk."""

    title = ""
    kicker = ""
    part: int = 0
    heading: str = ""
    description: str = ""
    formula: str = ""
    topics: tuple[str, str, str] = ("", "", "")
    accent: str = WANTED
    narration: str = ""

    def body(self) -> None:
        # Small, static chapter slides should read instantly in a browser.  No
        # build choreography is needed and no second frame is introduced.
        numeral = tex(rf"\textbf{{{self.part:02d}}}", size=100, color=self.accent)
        numeral.move_to([-6.45, 1.65, 0], aligned_edge=LEFT)
        label = tex(rf"PART {self.part} / 6", size=22, color=self.accent)
        label.move_to([-4.25, 2.65, 0], aligned_edge=LEFT)
        heading = tex(self.heading, size=49, color=FG)
        heading.move_to([-4.25, 1.65, 0], aligned_edge=LEFT)
        if heading.width > 10.5:
            heading.scale_to_fit_width(10.5)
        summary = para(self.description, width=10.45, size=27, color=MUTED)
        summary.next_to(heading, DOWN, aligned_edge=LEFT, buff=0.27)
        line = Line([-6.45, 0.20, 0], [6.3, 0.20, 0], color=self.accent, stroke_width=3)

        equation = math(self.formula, size=46)
        if equation.width > 11.8:
            equation.scale_to_fit_width(11.8)
        equation.move_to([0, -1.18, 0])
        # The broad strip supports the equation without giving the slide a
        # second title or any technical depth badges.
        background = VGroup(
            Line([-5.7, -2.14, 0], [5.7, -2.14, 0], color=PANEL, stroke_width=2),
            Line([-5.7, -0.36, 0], [5.7, -0.36, 0], color=PANEL, stroke_width=2),
        )
        topics = VGroup(*[tex(text, size=22, color=MUTED) for text in self.topics])
        topics.arrange(RIGHT, buff=0.55)
        if topics.width > 12:
            topics.scale_to_fit_width(12)
        topics.move_to([0, -2.75, 0])
        self.say(self.narration or self.description)
        self.add(numeral, label, heading, summary, line, background, equation, topics)


class C01Foundations(CompendiumChapter):
    part = 1
    heading = "The geometric problem"
    description = "From a perturbed self-adjoint operator to a measurable change in its eigenspaces."
    formula = r"\sym{Ahat}=\sym{A}+\sym{H}"
    topics = ("eigenvectors", "spectral gaps", "subspace angles")
    accent = PERTURB


class C02ThreeDimensions(CompendiumChapter):
    part = 2
    heading = "Subspaces in three dimensions"
    description = "Move from one-dimensional eigenvectors to two-dimensional planes, angles, and residuals."
    formula = r"\operatorname{range}(\sym{E0})\quad\leftrightarrow\quad\operatorname{range}(\sym{F0})"
    topics = ("principal angles", "a moving spectral gap", "VTK geometry")
    accent = WANTED


class C03TheoremFamily(CompendiumChapter):
    part = 3
    heading = "Four ways to bound a rotation"
    description = "The sine, tangent, double-sine, and double-tangent results use different spectral assumptions."
    formula = r"\sin\Theta\ ,\ \tan\Theta\ ,\ \sin 2\Theta\ ,\ \tan 2\Theta"
    topics = ("gap hypotheses", "sharp inequalities", "proof mechanisms")
    accent = SINE


class C04Proposition(CompendiumChapter):
    part = 4
    heading = "A counterexample in the source"
    description = "Proposition 4.4 leads to a four-dimensional counterexample and a norm-dependent repair."
    formula = r"\norm{I-W}\quad\text{versus}\quad\norm{I-\mathcal R}"
    topics = ("direct rotations", "unitarily invariant norms", "Q-norm repair")
    accent = REFUTED


class C05Evidence(CompendiumChapter):
    part = 5
    heading = "Proof checking and source fidelity"
    description = "A Lean theorem can compile while representing a statement different from the printed source."
    formula = r"\text{proof checked}\quad\not\Rightarrow\quad\text{source matched}"
    topics = ("agent workflow", "semantic alignment", "review evidence")
    accent = RESID


class C06Notation(CompendiumChapter):
    part = 6
    heading = "Notation reference"
    description = "The same symbols and mathematical roles remain consistent across the theorem family."
    formula = r"\sym{Ahat}\ ,\ \sym{E0}\ ,\ \sym{F0}\ ,\ \sym{R}\ ,\ \sym{delta}"
    topics = ("operators and frames", "angles and spectra", "norms and examples")
    accent = GAP
