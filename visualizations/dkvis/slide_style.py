"""Shared look for the manim-slides decks.

One color per mathematical role, used identically on every slide, so the
audience can read a picture by color before reading any label.  The roles
follow the Davis--Kahan story: blue is what we want, amber is what we
computed, cyan is the exact part we do not want, pink is how much of our
computation points into it, green is the residual that exposes that error,
and violet is the separation that keeps it from hiding.

========  ==================================================  ============
role      objects                                             constant
========  ==================================================  ============
wanted    ``U``, ``F0``, ``Lambda0``, wanted eigenvectors       ``WANTED``
trial     ``V``, ``E0``, ``A0``, ``v``, Ritz values, ``rho``    ``TRIAL``
unwanted  ``U-perp``, ``F1``, ``Lambda1``, unwanted eigen-      ``UNWANTED``
          vectors and eigenvalues (exact, but not wanted)
angle     ``theta``, ``sin Theta0``, ``X``, the part of a trial   ``SINE``
          vector outside ``U``
residual  ``r``, ``R``, residual components                     ``RESID``
gap       ``delta`` and the separating window                   ``GAP``
neutral   projectors, axes, helper geometry, prose              ``FG``
========  ==================================================  ============

A quieter second tier says where an operator comes from, each a muted relative
of its eigenvectors' color:

========  ==================================================  ============
old       ``A`` (dashed when drawn), its block ``A1``           ``OLD``
current   ``A~`` (solid when drawn)                            ``CURRENT``
perturb   ``H``, its blocks and entries                         ``PERTURB``
refuted   a claim shown false, and nothing else                 ``REFUTED``
========  ==================================================  ============

``MUTED`` and ``FAINT`` are presentation only (secondary labels, guides, context)
and never mean a role.  The same names exist as LaTeX colors for ``\\cx``.
A box outlined in a role color gets a faint surface of that color (``boxed``,
``panel(role=...)``), which adds color without adding a meaning.  The process
slides use neutral colors only; the Proposition 4.4 slides draw the two
competing maps neutrally.

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
import contextlib
import fcntl
import functools
import os
from pathlib import Path

from manim.mobject.svg.svg_mobject import SVGMobject
from manim.mobject.text import tex_mobject
from manim_slides import Slide

from dkvis.notation import color_nouns, expand, latex_preamble
from dkvis.palette import OUTPUT_SUFFIX, PALETTE, tint


# ``dkvis.build_slides`` renders scenes in parallel processes that share manim's
# LaTeX and text caches under ``media/``.  manim touches those directories
# without any locking: after each LaTeX run it deletes every non-SVG file there,
# including other processes' half-finished ones, and it parses a cached SVG by
# writing, reading and deleting a fixed-name temporary copy next to it.  So run
# each of these steps under one cross-process lock; a cache hit holds it only
# for a moment, and each process parses a given SVG only once.
@contextlib.contextmanager
def _media_cache_lock():
    lock = Path(config.media_dir) / ".cache.lock"
    lock.parent.mkdir(parents=True, exist_ok=True)
    with open(lock, "w") as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        yield


def _under_media_cache_lock(fill):
    @functools.wraps(fill)
    def locked(*args, **kwargs):
        with _media_cache_lock():
            return fill(*args, **kwargs)

    return locked


tex_mobject.tex_to_svg_file = _under_media_cache_lock(tex_mobject.tex_to_svg_file)
Text._text2svg = _under_media_cache_lock(Text._text2svg)
SVGMobject.generate_mobject = _under_media_cache_lock(SVGMobject.generate_mobject)

BG = PALETTE["BG"]
FG = PALETTE["FG"]
MUTED = PALETTE["MUTED"]
FAINT = PALETTE["FAINT"]
PANEL = PALETTE["PANEL"]
WANTED = PALETTE["WANTED"]
UNWANTED = PALETTE["UNWANTED"]
TRIAL = PALETTE["TRIAL"]
SINE = PALETTE["SINE"]
RESID = PALETTE["RESID"]
GAP = PALETTE["GAP"]
OLD = PALETTE["OLD"]
CURRENT = PALETTE["CURRENT"]
PERTURB = PALETTE["PERTURB"]
REFUTED = PALETTE["REFUTED"]

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
\newcommand{{\norm}}[1]{{\lVert #1\rVert}}
{latex_preamble()}
"""
)

# ``Tex(r"\rule{10cm}{1pt}", font_size=s).width == 0.2953 * s`` frame units.
_UNITS_PER_CM_PER_FONT_SIZE = 14.173228 / 10 / 48


MONO_FONT = "JetBrains Mono"


def tex(body: str, size: float = 30, color: str = FG, **kwargs) -> Tex:
    """Prose with inline ``$math$``."""
    return Tex(expand(body), font_size=size, color=color, tex_template=TEMPLATE, **kwargs)


def math(*parts: str, size: float = 36, color: str = FG, **kwargs) -> MathTex:
    """Display math.  A role ``color`` colors the symbols and leaves the verbs
    (relations, operations, norm bars, delimiters) neutral; ``FG`` and the
    presentation grays color the whole formula."""
    parts = [expand(part) for part in parts]
    if color not in (FG, MUTED, FAINT):
        spec = f"[HTML]{{{_hex(color)}}}"
        parts = [color_nouns(part, spec) for part in parts]
        color = FG
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


def panel(mob, pad: float = 0.3, role: str | None = None) -> Rectangle:
    """A backing card for a formula block, neutral or in the tint of ``role``'s color."""
    rect = Rectangle(
        width=mob.width + 2 * pad,
        height=mob.height + 2 * pad,
        stroke_width=0,
        fill_color=PANEL if role is None else tint(role),
        fill_opacity=1.0,
    ).move_to(mob)
    return rect


def boxed(mob, color: str = FG, pad: float = 0.25) -> VGroup:
    """``mob`` in a box outlined in ``color``; the surface takes that role's tint
    (a neutral outline keeps the neutral panel)."""
    rect = Rectangle(
        width=mob.width + 2 * pad,
        height=mob.height + 2 * pad,
        stroke_color=color,
        stroke_width=2,
        fill_color=PANEL if color in (FG, MUTED) else tint(color),
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

    def __init__(self, *args, **kwargs) -> None:
        # ``dkvis.build_slides`` sets DKVIS_DECK so that each deck renders into
        # its own folder and numbers its slides by its own order.
        deck = os.environ.get("DKVIS_DECK")
        if deck:
            kwargs.setdefault("output_folder", Path(f"slides-{deck}{OUTPUT_SUFFIX}"))
        super().__init__(*args, **kwargs)

    def slide_number(self) -> tuple[int, int] | None:
        """``(k, N)``: this scene's position in the deck being built, if any."""
        deck = os.environ.get("DKVIS_DECK")
        if not deck:
            return None
        from dkvis.build_slides import DECK_SCENES

        order = DECK_SCENES.get(deck, [])
        name = type(self).__name__
        return (order.index(name) + 1, len(order)) if name in order else None

    def footer_text(self) -> str:
        """The part's title when rendering a part of the full talk, else the scene's own section."""
        deck = os.environ.get("DKVIS_DECK")
        if deck:
            from dkvis.build_slides import PART_TITLES

            if deck in PART_TITLES:
                return PART_TITLES[deck]
        return self.section

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
        self._head = VGroup()  # title and kicker: what content is laid out below
        if self.title:
            title = tex(self.title, size=44)
            max_w = FRAME_W - 2 * 0.55 - (1.9 if self.depth else 0.0)
            if title.width > max_w:
                title.scale_to_fit_width(max_w)
            title.move_to([LEFT_EDGE, TOP_EDGE, 0], aligned_edge=UL)
            items.add(title)
            self._head.add(title)
            if self.kicker:
                kick = tex(self.kicker, size=26, color=MUTED).next_to(
                    title, DOWN, aligned_edge=LEFT, buff=0.18
                )
                items.add(kick)
                self._head.add(kick)
        if self.depth:
            label = {"*": r"$\ast$\ optional depth", "**": r"$\ast\ast$\ backup"}[self.depth]
            badge = tex(label, size=20, color=MUTED).move_to(
                [FRAME_W / 2 - 0.45, TOP_EDGE - 0.05, 0], aligned_edge=UP + RIGHT
            )
            items.add(badge)
        footer_text = self.footer_text()
        if footer_text:
            footer = tex(footer_text, size=18, color=MUTED).move_to(
                [LEFT_EDGE, -FRAME_H / 2 + 0.3, 0], aligned_edge=LEFT
            )
            items.add(footer)
        number = self.slide_number()
        if number is not None:
            k, n = number
            label = tex(rf"{k} / {n}", size=20, color=MUTED).move_to(
                [FRAME_W / 2 - 0.45, -FRAME_H / 2 + 0.3, 0], aligned_edge=RIGHT
            )
            items.add(label)
        return items

    @property
    def content_top(self) -> float:
        """y coordinate just below the title block."""
        if self.chrome is None or not self.title:
            return TOP_EDGE
        return self._head.get_bottom()[1] - 0.25

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
