"""Shared look for the manim-slides decks.

One color per mathematical role, used identically on every slide, so the
audience can read a picture by color before reading any label:

========  ==============================================  ==================
role      object                                          constant
========  ==============================================  ==================
exact     the true eigenspace ``U = ran F0``, eigenvectors ``EXACT``
trial     the trial subspace ``V = ran E0``, ``v``, ``A0``  ``TRIAL``
angle     ``sin Theta0``, the part of ``v`` outside ``U``    ``SINE``
residual  ``R = A E0 - E0 A0``                              ``RESID``
gap       ``delta`` and the separating window               ``GAP``
========  ==============================================  ==================

Set ``DKVIS_THEME=light`` before rendering for a light-background deck (useful
for bright rooms and for printing); the default is dark.

Text is typeset by LaTeX in Latin Modern Sans with Computer Modern math, the
familiar Beamer look, so prose and formulas share one engine.
"""

from __future__ import annotations

from manim import (
    RIGHT,
    UP,
    DOWN,
    LEFT,
    UL,
    DashedLine,
    FadeOut,
    Line,
    MathTex,
    Rectangle,
    Tex,
    TexTemplate,
    Text,
    VGroup,
    config,
)
from manim_slides import Slide

from dkvis.palette import PALETTE

BG = PALETTE["BG"]
FG = PALETTE["FG"]
MUTED = PALETTE["MUTED"]
FAINT = PALETTE["FAINT"]
PANEL = PALETTE["PANEL"]
EXACT = PALETTE["EXACT"]
TRIAL = PALETTE["TRIAL"]
SINE = PALETTE["SINE"]
RESID = PALETTE["RESID"]
GAP = PALETTE["GAP"]

config.background_color = BG

FRAME_W = config.frame_width
FRAME_H = config.frame_height
LEFT_EDGE = -FRAME_W / 2 + 0.55
TOP_EDGE = FRAME_H / 2 - 0.45


def _hex(color: str) -> str:
    return color.lstrip("#").upper()


TEMPLATE = TexTemplate()
TEMPLATE.add_to_preamble(
    rf"""
\usepackage{{lmodern}}
\renewcommand{{\familydefault}}{{\sfdefault}}
\usepackage{{amsmath,amssymb}}
\usepackage{{xcolor}}
\definecolor{{fg}}{{HTML}}{{{_hex(FG)}}}
\definecolor{{muted}}{{HTML}}{{{_hex(MUTED)}}}
\definecolor{{exact}}{{HTML}}{{{_hex(EXACT)}}}
\definecolor{{trial}}{{HTML}}{{{_hex(TRIAL)}}}
\definecolor{{sine}}{{HTML}}{{{_hex(SINE)}}}
\definecolor{{resid}}{{HTML}}{{{_hex(RESID)}}}
\definecolor{{gap}}{{HTML}}{{{_hex(GAP)}}}
\newcommand{{\norm}}[1]{{\lVert #1\rVert}}
\newcommand{{\cx}}[2]{{\textcolor{{#1}}{{#2}}}}
"""
)

# ``Tex(r"\rule{10cm}{1pt}", font_size=s).width == 0.2953 * s`` frame units.
_UNITS_PER_CM_PER_FONT_SIZE = 14.173228 / 10 / 48


MONO_FONT = "JetBrains Mono"


def tex(body: str, size: float = 30, color: str = FG, **kwargs) -> Tex:
    """Prose with inline ``$math$``."""
    return Tex(body, font_size=size, color=color, tex_template=TEMPLATE, **kwargs)


def math(*parts: str, size: float = 36, color: str = FG, **kwargs) -> MathTex:
    return MathTex(*parts, font_size=size, color=color, tex_template=TEMPLATE, **kwargs)


def colored_math(*parts: tuple[str, str | None], size: float = 36) -> MathTex:
    """Display math assembled from ``(tex, color)`` pieces.

    Coloring whole pieces avoids ``tex_to_color_map`` substring surgery, which
    breaks on braces.
    """
    mob = math(*[p for p, _ in parts], size=size)
    for sub, (_, color) in zip(mob, parts):
        if color is not None:
            sub.set_color(color)
    return mob


def para(body: str, width: float, size: float = 28, color: str = FG, align: str = "raggedright") -> Tex:
    """A paragraph wrapped by LaTeX to ``width`` frame units."""
    cm = width / (_UNITS_PER_CM_PER_FONT_SIZE * size)
    return tex(
        rf"\begin{{minipage}}{{{cm:.3f}cm}}\{align} {body}\end{{minipage}}",
        size=size,
        color=color,
    )


def mono(body: str, size: float = 20, color: str = FG) -> Text:
    return Text(body, font=MONO_FONT, font_size=size, color=color)


def bullets(*lines: str, size: float = 28, buff: float = 0.28, color: str = FG) -> VGroup:
    """Left-aligned column of ``tex`` lines (no bullet glyphs; spacing does the work)."""
    group = VGroup(*[tex(line, size=size, color=color) for line in lines])
    group.arrange(DOWN, aligned_edge=LEFT, buff=buff)
    return group


def panel(mob, pad: float = 0.3) -> Rectangle:
    """A subtle rounded-looking backing card for a formula block."""
    rect = Rectangle(
        width=mob.width + 2 * pad,
        height=mob.height + 2 * pad,
        stroke_width=0,
        fill_color=PANEL,
        fill_opacity=1.0,
    ).move_to(mob)
    return rect


def boxed(mob, color: str = FG, pad: float = 0.25) -> VGroup:
    rect = Rectangle(
        width=mob.width + 2 * pad,
        height=mob.height + 2 * pad,
        stroke_color=color,
        stroke_width=2,
        fill_color=PANEL,
        fill_opacity=1.0,
    ).move_to(mob)
    return VGroup(rect, mob)


def arrow_label(text: str, color: str, size: float = 30) -> MathTex:
    return math(text, size=size, color=color)


def dashed(start, end, color: str = MUTED, width: float = 2.0) -> DashedLine:
    return DashedLine(start, end, color=color, stroke_width=width, dash_length=0.08)


def axis_line(start, end, width: float = 1.5) -> Line:
    return Line(start, end, color=FAINT, stroke_width=width)


class DeckSlide(Slide):
    """Common chrome: a title, an optional kicker line and a footer tag.

    Subclasses set ``title``, ``kicker`` and ``section`` and implement
    ``body``.  Speaker notes for a build are given with ``self.say(...)``
    immediately before the animations of that build.
    """

    title: str = ""
    kicker: str = ""
    section: str = "The Davis--Kahan $\\sin\\Theta$ theorem"
    #: ``""`` core talk, ``"*"`` optional technical depth, ``"**"`` backup.
    depth: str = ""
    skip_reversing = True
    # manim writes the frame *before* an animation's final state, so a build
    # ending on a staggered FadeIn would otherwise freeze one frame short.
    wait_time_between_slides = 0.1

    def construct(self) -> None:
        self.chrome = self.make_chrome()
        if self.chrome is not None:
            self.add(self.chrome)
        self._ended_on_src = False
        self.body()
        # A scene that ends on an external-video slide must not get a trailing
        # wait, which would become an extra (static) slide after the video.
        if not self._ended_on_src:
            self.wait(self.wait_time_between_slides)

    # -- chrome ---------------------------------------------------------------
    def make_chrome(self) -> VGroup | None:
        items = VGroup()
        if self.title:
            title = tex(self.title, size=44).to_corner(UL, buff=0).move_to(
                [LEFT_EDGE, TOP_EDGE, 0], aligned_edge=UL
            )
            items.add(title)
            if self.kicker:
                kick = tex(self.kicker, size=26, color=MUTED).next_to(
                    title, DOWN, aligned_edge=LEFT, buff=0.18
                )
                items.add(kick)
        if self.depth:
            label = {"*": r"$\ast$\ optional depth", "**": r"$\ast\ast$\ backup"}[self.depth]
            badge = tex(label, size=20, color=MUTED).move_to(
                [FRAME_W / 2 - 0.45, TOP_EDGE - 0.05, 0], aligned_edge=UP + RIGHT
            )
            items.add(badge)
        if self.section:
            footer = tex(self.section, size=18, color=MUTED).move_to(
                [LEFT_EDGE, -FRAME_H / 2 + 0.3, 0], aligned_edge=LEFT
            )
            items.add(footer)
        self._has_footer = bool(self.section)
        return items

    @property
    def content_top(self) -> float:
        """y coordinate just below the title block."""
        if self.chrome is None or not self.title:
            return TOP_EDGE
        head = self.chrome[:-1] if self._has_footer else self.chrome
        return head.get_bottom()[1] - 0.25

    # -- builds ---------------------------------------------------------------
    def say(self, notes: str, **kwargs) -> None:
        """Start a new build whose presenter notes are ``notes``.

        Calling it before any animation attaches the notes to the scene's
        opening build.
        """
        self.next_slide(notes=notes, **kwargs)
        self._ended_on_src = kwargs.get("src") is not None

    def fade_all_but_chrome(self, run_time: float = 0.6) -> None:
        keep = {id(self.chrome)}
        mobs = [m for m in self.mobjects if id(m) not in keep]
        if mobs:
            self.play(*[FadeOut(m) for m in mobs], run_time=run_time)

    def body(self) -> None:  # pragma: no cover - implemented by subclasses
        raise NotImplementedError
