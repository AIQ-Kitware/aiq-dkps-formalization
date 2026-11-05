"""Shared layout and transcript beats for short narrated learning modules."""
from functools import lru_cache

import numpy as np
from manim import Arrow, Axes, DOWN, LEFT, Line, Rectangle, RIGHT, UP, VGroup

from dkvis.presentation.narration import read_deck_narration
from dkvis.slide_style import CURRENT, FG, MUTED, DeckSlide, boxed, math, para, tex


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
    bonus = False
    wait_time_between_slides = .25

    @property
    def script(self):
        return scripts(self.lesson_deck)[type(self).__name__]

    def make_chrome(self):
        self.title, self.kicker = self.script.title, self.script.motivation
        if self.bonus:
            self.title = r'\textbf{Bonus:} ' + self.title.removeprefix('Bonus: ')
        elif self.example:
            self.title = r"\textbf{Example:} " + self.title
        chrome = super().make_chrome()
        if len(self._head) > 1 and self._head[1].width > 12.2:
            self._head[1].scale_to_fit_width(12.2).next_to(
                self._head[0], DOWN, aligned_edge=LEFT, buff=.18)
        if self.bonus:
            chrome.add(tex('Optional numerical considerations', size=21, color=MUTED).move_to([0, -3.15, 0]))
            return chrome
        stages = VGroup(*(tex(label, size=18, color=CURRENT if i == self.stage else MUTED)
                          for i, label in enumerate([
                              'Question', 'Tools', 'Applications', 'Recap',
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
        from dkvis.components.llm_credit import llm_credit
        self.add(llm_credit(self.lesson_deck))


class LessonLean(LessonSlide):
    """Pair symbolic facts with the checked examples applying their Lean APIs."""
    lecture_id = ''
    ownership = ''
    notation = ''
    symbolic_facts = ()
    stage = 3

    fact_index = 0
    assumptions = ''

    def body(self):
        import re
        from dkvis.components.lean_code import lean_code
        from dkvis.lectures import lecture_path
        from dkvis.presentation.paths import ROOT
        from dkvis.slide_style import GAP, RESID, FAINT, PANEL

        self.start()
        source = (ROOT / lecture_path(self.lecture_id)).with_name('facts.lean').read_text()
        code = source.split('-- slide-begin\n', 1)[1].split('-- slide-end', 1)[0].strip()
        starts = [m.start() for m in re.finditer(r'^example\b', code, re.MULTILINE)]
        examples = [code[start:end].strip() for start, end in
                    zip(starts, starts[1:]+[len(code)])]
        if len(examples) != len(self.symbolic_facts):
            raise ValueError(f'Symbolic/Lean fact mismatch: {type(self).__name__}')
        label, statement = self.symbolic_facts[self.fact_index]
        example = examples[self.fact_index]
        # Keep the statement separate from the library proof, without altering
        # a single token of the checked companion.
        boundary = re.search(r':=\s*(?:by\s*)?\n', example)
        if boundary is None:
            raise ValueError(f'Expected a multiline proof in {type(self).__name__}')
        declaration, proof = example[:boundary.end()].rstrip(), example[boundary.end():].rstrip()
        declaration_mob = lean_code(declaration, size=23)
        proof_mob = lean_code(proof, size=23, proof=True)
        for block in (declaration_mob,):
            if block.width > 8.35:
                factor = 8.35/block.width
                if factor < .78:
                    raise ValueError(f'Wrap Lean source lines: {type(self).__name__}')
                block.scale(factor)
        right = VGroup(tex('Lean statement',size=21,color=GAP), declaration_mob)
        right.arrange(DOWN, aligned_edge=LEFT, buff=.14)
        if right.height > 3.0:
            factor=3.0/right.height
            if factor < .82:
                raise ValueError(f'Split Lean context: {type(self).__name__}')
            right.scale(factor)
        right.move_to([-2.10,2.1,0],aligned_edge=UP+LEFT)
        if proof_mob.width>12.1:
            factor=12.1/proof_mob.width
            if factor<.82:
                raise ValueError(f'Wrap Lean proof arguments: {type(self).__name__}')
            proof_mob.scale(factor)
        proof_row=VGroup(tex('Library proof',size=19,color=RESID),proof_mob)
        proof_row.arrange(DOWN,aligned_edge=LEFT,buff=.10)
        if proof_row.height>1.35:
            raise ValueError(f'Split Lean proof: {type(self).__name__}')
        proof_row.move_to([-6.05,-.85,0],aligned_edge=UP+LEFT)
        formula = boxed(math(statement, size=33),color=CURRENT)
        if formula.width > 3.75:
            formula.scale_to_fit_width(3.75)
        scope=para(self.assumptions,width=3.75,size=22,color=MUTED)
        left=VGroup(tex(label,size=24),formula,scope,
                    tex(f'Fact {self.fact_index+1} of {len(examples)}',size=20,color=MUTED))
        left.arrange(DOWN,buff=.25).move_to([-4.7,.65,0])
        if left.height>3.8:
            raise ValueError(f'Lean scope too dense: {type(self).__name__}')
        backdrop=Rectangle(width=8.65,height=max(2.0,right.height+.30),stroke_color=FAINT,
                           fill_color=PANEL,fill_opacity=1)
        backdrop.move_to([2.13,2.25,0],aligned_edge=UP)
        self.add(backdrop,left,right,proof_row,
                 tex(self.ownership,size=18,color=MUTED).move_to([0,-2.25,0]))
        self.takeaway(self.notation)
