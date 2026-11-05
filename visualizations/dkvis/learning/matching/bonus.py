"""Optional numerical implementation, separated from the matching proof."""
import os
from dkvis.components.lesson import LessonSlide, stack
from dkvis.slide_style import CURRENT, boxed, math, tex


class MatchingComputation(LessonSlide):
    bonus=True

    @property
    def lesson_deck(self):
        return os.environ['DKVIS_DECK']

    def body(self):
        self.start()
        self.put(stack(r'a_i=\text{singleton cost},\qquad b_{ij}=\text{pair cost}',
            r'g_{ij}=a_i+a_j-b_{ij},\qquad C_0=\sum_i a_i',
            tex('Build a general graph of angle labels, with pair savings as weights.',size=28),
            boxed(math(r'\texttt{max\_weight\_matching}(G,\ \texttt{maxcardinality=False})',size=26),color=CURRENT),
            tex('Blossom-based algorithms allow unmatched vertices; do not impose bipartition.',size=27),
            tex('Floating weights near a tie need care; recover blocks and verify the computed cost.',size=26),
            buff=.32),y=.45,height=3.6)
        self.source('NetworkX max-weight-matching documentation (general graphs).')
        self.takeaway('The theorem proves the reduction; numerical precision belongs to the implementation.')
