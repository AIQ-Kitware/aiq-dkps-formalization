"""A lecture's authored conclusions, highlighted during one coherent passage."""
import os
import yaml
from manim import Create, DOWN, LEFT, SurroundingRectangle, Transform, VGroup
from dkvis.components.lesson import LessonSlide
from dkvis.decks import get_deck
from dkvis.presentation.paths import ROOT
from dkvis.slide_style import CURRENT, para


class LectureOutcomes(LessonSlide):
    @property
    def lesson_deck(self):
        return os.environ['DKVIS_DECK']

    def body(self):
        self.start()
        path=(ROOT/get_deck(self.lesson_deck).narration).with_name('outcomes.yaml')
        plan=yaml.safe_load(path.read_text())
        rows=VGroup(*(para(f'{i}. {fact}',width=11.4,size=29)
                      for i,fact in enumerate(plan['facts'],1))).arrange(DOWN,aligned_edge=LEFT,buff=.45)
        self.put(rows,y=.4,height=3.6)
        focus=SurroundingRectangle(rows[0],color=CURRENT,buff=.14)
        self.play(Create(focus),run_time=1)
        for row in rows[1:]:
            self.play(Transform(focus,SurroundingRectangle(row,color=CURRENT,buff=.14)),run_time=1)
        self.takeaway('The explanation will connect these conclusions, then return to them at the end.')
