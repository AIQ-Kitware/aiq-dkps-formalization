"""Shared layout and transcript beats for short narrated learning modules."""
from functools import lru_cache

import numpy as np
from manim import Arrow, Axes, DOWN, LEFT, Line, Rectangle, RIGHT, UP, VGroup

from dkvis.presentation.narration import read_deck_narration
from dkvis.slide_style import CURRENT, FG, MUTED, DeckSlide, boxed, math, mono, para, tex


@lru_cache
def scripts(deck):
    return read_deck_narration(deck)


def stack(*items, size=31, buff=.30):
    return VGroup(*(math(item, size=size) if isinstance(item, str) else item
                    for item in items)).arrange(DOWN, buff=buff)


def plane(width=4.8, height=3.3, extent=2.7):
    x_extent = extent*width/height
    return Axes(x_range=[-x_extent, x_extent, 1], y_range=[-extent, extent, 1],
                x_length=width, y_length=height, tips=False,
                axis_config={'color': MUTED, 'include_ticks': False})


def vector(axes, xy, color=FG):
    return Arrow(axes.c2p(0, 0), axes.c2p(*xy), buff=0, color=color, stroke_width=4)


def bars(values, labels=None, *, color=CURRENT, height=2.0):
    group = VGroup()
    for i, value in enumerate(values):
        bar = Rectangle(width=.65, height=max(.025, value*height/3), color=color,
                        fill_color=color, fill_opacity=.22)
        bar.move_to([i*1.05, bar.height/2, 0])
        value_label = math(f'{value:g}', size=25).next_to(bar, DOWN, buff=.15)
        group.add(bar, value_label)
        if labels:
            group.add(tex(labels[i], size=23, color=MUTED).next_to(bar, np.array([0, 1, 0]), buff=.15))
    return group


class LessonSlide(DeckSlide):
    """Topics supply a deck name and scene bodies; content stays in transcripts."""
    lesson_deck = ''
    stage = 0
    example = False
    wait_time_between_slides = .25

    @property
    def script(self):
        return scripts(self.lesson_deck)[type(self).__name__]

    def make_chrome(self):
        self.title, self.kicker = self.script.title, self.script.motivation
        if self.example:
            self.title = r"\textbf{Example:} " + self.title
        chrome = super().make_chrome()
        if len(self._head) > 1 and self._head[1].width > 12.2:
            self._head[1].scale_to_fit_width(12.2).next_to(
                self._head[0], DOWN, aligned_edge=LEFT, buff=.18)
        stages = VGroup(*(tex(label, size=18, color=CURRENT if i == self.stage else MUTED)
                          for i, label in enumerate([
                              'Question', 'Tools', 'Use in the proof', 'Recap',
                          ]))).arrange(RIGHT, buff=.75).move_to([0, -3.15, 0])
        current = stages[self.stage]
        chrome.add(stages, Line(current.get_left()+DOWN*.17,
                                current.get_right()+DOWN*.17, color=CURRENT))
        return chrome

    def construct(self):
        self._beat = 0
        super().construct()
        if self._beat+1 != len(self.script.beats):
            raise ValueError(f'Animation/transcript mismatch: {type(self).__name__}')

    def start(self):
        self.say(self.script.beats[0])

    def beat(self):
        self.wait(self.wait_time_between_slides)
        self._beat += 1
        self.say(self.script.beats[self._beat])

    def put(self, mob, side='full', *, y=0, height=4.35):
        width = 12.0 if side == 'full' else 5.65
        factor = min(1, width/mob.width, height/mob.height)
        if factor < .72:
            raise ValueError(f'Content too dense: {type(self).__name__} ({factor:.2f})')
        mob.scale(factor).move_to([{'full': 0, 'left': -3.25, 'right': 3.25}[side], y, 0])
        self.add(mob)
        return mob

    def takeaway(self, message):
        if self.example:
            message = r"\textbf{General tool:} " + message
        label = para(message, width=12, size=25, color=CURRENT)
        if label.height > .63:
            raise ValueError(f'Takeaway too long: {type(self).__name__}')
        self.add(label.move_to([0, -2.66, 0]))

    def source(self, credit):
        self.add(tex(credit, size=19, color=MUTED).move_to([0, -1.99, 0]))


class LessonTitle(LessonSlide):
    """A static opening card with one short, independently authored speech beat."""
    title_lines = ()
    subtitle = ''
    series_title = 'Prerequisite lectures'

    def make_chrome(self):
        return None

    def body(self):
        self.start()
        title = VGroup(*(tex(line, size=54) for line in
                         (self.title_lines or (self.script.title,)))).arrange(DOWN, buff=.22)
        if title.width > 11.8:
            title.scale_to_fit_width(11.8)
        title.move_to([0, .45, 0])
        self.add(tex(self.series_title, size=24, color=MUTED).move_to([0, 2.25, 0]),
                 title, Line([-2.1, -.95, 0], [2.1, -.95, 0], color=CURRENT),
                 tex(self.subtitle, size=27, color=MUTED).move_to([0, -1.55, 0]))


class LessonLean(LessonSlide):
    """Pair symbolic facts with the checked examples applying their Lean APIs."""
    lecture_id = ''
    ownership = ''
    notation = ''
    symbolic_facts = ()
    stage = 3

    def body(self):
        import re
        from dkvis.lectures import lecture_path
        from dkvis.presentation.paths import ROOT

        self.start()
        source = (ROOT / lecture_path(self.lecture_id)).with_name('facts.lean').read_text()
        code = source.split('-- slide-begin\n', 1)[1].split('-- slide-end', 1)[0].strip()
        starts = [m.start() for m in re.finditer(r'^example\b', code, re.MULTILINE)]
        examples = [code[start:end].strip() for start, end in
                    zip(starts, starts[1:]+[len(code)])]
        if len(examples) != len(self.symbolic_facts):
            raise ValueError(f'Symbolic/Lean fact mismatch: {type(self).__name__}')
        def code_block(text, size=18):
            mob = mono(text, size=size)
            if mob.width > 8.5:
                mob.scale_to_fit_width(8.5)
            return mob
        context = code_block(code[:starts[0]].strip(), size=16) if starts[0] else None
        rows = []
        for i, ((label, statement), example) in enumerate(zip(self.symbolic_facts, examples), 1):
            formula = boxed(math(statement, size=27), color=CURRENT)
            if formula.width > 3.7:
                formula.scale_to_fit_width(3.7)
            symbolic = VGroup(tex(f'{i}. {label}', size=21), formula).arrange(DOWN, buff=.15)
            rows.append((symbolic, code_block(example)))
        height = (context.height+.18 if context is not None else 0) + sum(
            max(left.height, right.height) for left, right in rows) + .20*(len(rows)-1)
        scale = min(1, 4.1/height)
        if scale < .75:
            raise ValueError(f'Lean comparison too dense: {type(self).__name__}')
        top = .1 + height*scale/2
        if context is not None:
            context.scale(scale).move_to([-2.05, top, 0], aligned_edge=UP+LEFT)
            self.add(context)
            top -= context.height+.18*scale
        for left, right in rows:
            left.scale(scale); right.scale(scale)
            row_height = max(left.height, right.height)
            left.move_to([-4.7, top-row_height/2, 0])
            right.move_to([-2.05, top-row_height/2, 0], aligned_edge=LEFT)
            self.add(left, right)
            top -= row_height+.20*scale
        self.add(Line([-2.45, 2.1, 0], [-2.45, -2.02, 0], color=MUTED, stroke_width=1),
                 tex(self.ownership, size=19, color=MUTED).move_to([0, -2.25, 0]))
        self.takeaway(self.notation)
