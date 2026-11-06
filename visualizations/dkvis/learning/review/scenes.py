"""A question build, thinking time in video, then an explained answer build."""
import os
from manim import DOWN, LEFT, SurroundingRectangle, VGroup

from dkvis.components.lesson import LessonSlide
from dkvis.quiz import questions
from dkvis.slide_style import CURRENT, MUTED, para


class ReviewSlide(LessonSlide):
    stage = 3
    question_index = 0

    @property
    def lesson_deck(self):
        return os.environ['DKVIS_DECK']

    def body(self):
        row = questions(self.lesson_deck)[self.question_index]
        self.start()
        self.put(para(row['question'], width=12, size=29), y=1.9, height=.8)
        choices = VGroup(*(para(f'{chr(65+i)}. '+text, width=11.5, size=27)
                          for i, text in enumerate(row['choices']))).arrange(DOWN, aligned_edge=LEFT, buff=.24)
        self.put(choices, y=.15, height=2.55)
        self.beat()
        for i, choice in enumerate(choices):
            choice.set_color(CURRENT if i == row['correct'] else MUTED)
        self.add(SurroundingRectangle(choices[row['correct']], color=CURRENT, buff=.10))
        self.put(para(row['explanation'], width=12, size=25, color=CURRENT), y=-1.95, height=.9)


class ReviewQuestion1(ReviewSlide):
    question_index = 0


class ReviewQuestion2(ReviewSlide):
    question_index = 1


class ReviewQuestion3(ReviewSlide):
    question_index = 2


class ReviewQuestion4(ReviewSlide):
    question_index = 3
