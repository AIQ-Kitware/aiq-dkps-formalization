"""Why preserved vector spaces justify triangular and diagonal blocks."""
import numpy as np
from manim import Create, ValueTracker, VGroup, always_redraw, linear
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.slide_style import CURRENT, TRIAL, WANTED, RESID, boxed, math, tex

class BlockSlide(LessonSlide):
    lesson_deck='prereq-invariant-blocks'
    stage_labels=('Preserved vectors','Read the blocks','Use the criterion','Recap')

class IbTitle(LessonTitle):
    lesson_deck='prereq-invariant-blocks'
    title_lines=('Invariant subspaces','Why blocks are allowed')
    subtitle='Follow the vectors before drawing zero blocks.'

class IbQuestion(BlockSlide):
    example=True
    def body(self):
        self.start();axes=plane(extent=3.5);self.put(axes,'left',y=.1)
        a=ValueTracker(0)
        self.add(vector(axes,[1,0],TRIAL),vector(axes,[2,0],WANTED))
        self.put(stack(r'T=\begin{pmatrix}2&a\\0&3\end{pmatrix}',r'Te_1=2e_1',
            tex('K: the horizontal axis',size=28,color=TRIAL),
            boxed(math(r'T(K)\subseteq K',size=37),color=TRIAL),size=36,buff=.4),'right',y=.4,height=3.6)
        self.beat()
        self.add(vector(axes,[0,1],TRIAL),always_redraw(lambda:vector(axes,[a.get_value(),3],RESID)))
        self.play(a.animate.set_value(1.5),run_time=3,rate_func=linear)
        self.takeaway('The horizontal axis stays inside itself; the vertical axis can leak into it.')

class IbBlocks(BlockSlide):
    stage=1
    def body(self):
        self.start();self.put(stack(tex('Columns name inputs; rows name output components.',size=29),
            r'\begin{pmatrix}x_K\\x_{K^\perp}\end{pmatrix}\mapsto'
            r'\begin{pmatrix}A&B\\C&D\end{pmatrix}\begin{pmatrix}x_K\\x_{K^\perp}\end{pmatrix}',
            r'T(K)\subseteq K\iff C=0',
            boxed(math(r'\text{Both parts invariant}\iff B=C=0',size=32),color=CURRENT),buff=.4),y=.4,height=3.8)
        self.takeaway('One preserved subspace gives one zero block; independence needs both transfers to vanish.')

class IbSymmetry(BlockSlide):
    stage=1
    def body(self):
        self.start();self.put(stack(r'T=T^*,\quad x\in K,\quad y\in K^\perp',
            r'\langle Ty,x\rangle=\langle y,Tx\rangle=0',
            tex('Tx lies in K; y is perpendicular to every vector in K.',size=28),
            boxed(math(r'T(K)\subseteq K\ \Longrightarrow\ T(K^\perp)\subseteq K^\perp',size=31),color=CURRENT),buff=.45),y=.4,height=3.6)
        self.takeaway('Self-adjointness turns the known zero transfer into the other zero transfer.')

class IbCommute(BlockSlide):
    stage=2
    def body(self):
        self.start();self.put(stack(r'P=\begin{pmatrix}I&0\\0&0\end{pmatrix},\quad T=\begin{pmatrix}A&B\\C&D\end{pmatrix}',
            r'PT=\begin{pmatrix}A&B\\0&0\end{pmatrix},\quad TP=\begin{pmatrix}A&0\\C&0\end{pmatrix}',
            boxed(math(r'PT=TP\iff B=C=0',size=38),color=CURRENT),size=33,buff=.45),y=.4,height=3.7)
        self.takeaway('Order independence of the two maps is exactly preservation of both pieces.')

class IbExample(BlockSlide):
    example=True;stage=2
    def body(self):
        self.start();axes=plane(extent=3.5);self.put(axes,'left',y=.2)
        for v in [[1,0],[0,1]]:self.add(vector(axes,v,TRIAL))
        self.play(Create(vector(axes,[2,0],WANTED)),Create(vector(axes,[0,3],RESID)),run_time=2)
        self.put(stack(r'T=\operatorname{diag}(2,3)',r'Te_1=2e_1,\quad Te_2=3e_2',
            tex('Preserved directions can stretch.',size=28),
            tex('For larger subspaces, each scalar entry becomes a map.',size=26),buff=.5),'right',y=.3,height=3.5)
        self.takeaway('An invariant subspace is not a set of fixed points.')

class IbSummary(BlockSlide):
    stage=3
    def body(self):
        self.start();self.put(stack(r'T(K)\subseteq K\quad\Rightarrow\quad C=0',
            r'T=T^*\quad\Rightarrow\quad B=C^*',r'PT=TP\quad\iff\quad B=C=0',
            tex('A common block must be preserved by every relevant operator.',size=28),buff=.45),y=.4,height=3.5)
        self.takeaway('A block reduction is a consequence of preservation, not a restriction imposed without proof.')

class IbFacts(BlockSlide):
    stage=3
    def body(self):
        self.start();self.put(stack(r'T_{\rm off}=PT(I-P)+(I-P)TP',
            boxed(math(r'T_{\rm off}=0\iff PT=TP',size=38),color=CURRENT),
            r'Px+(I-P)x=x',buff=.5),y=.4,height=3.3)
        self.takeaway('The two transfers have perpendicular output ranges.')

class IbLean(LessonLean):
    lesson_deck='prereq-invariant-blocks';lecture_id='invariant_blocks'
    symbolic_facts=(('Off-diagonal criterion',r'T_{\rm off}=0\iff PT=TP'),('Orthogonal splitting',r'P_Kx+P_{K^\perp}x=x'))
    assumptions='Real inner product space; K has an orthogonal projection; T is bounded and linear.'
    ownership='Tau Ceti Projection/Block: the two accepted projection identities.'
    notation=r'\texttt{starProjection} is $P_K$; \texttt{Commute} says the compositions agree.'
class IbLeanSplit(IbLean):fact_index=1

class IbComputation(BlockSlide):
    bonus=True
    def body(self):
        self.start();self.put(stack(r'Q^TQ=I,\quad Z^TZ=I,\quad Q^TZ=0',
            r'C=Z^TTQ,\quad B=Q^TTZ',
            tex('Measure both directions of leakage.',size=30),
            tex('Small computed blocks support approximate invariance; exact zero needs proof.',size=27),buff=.5),y=.4,height=3.5)
        self.takeaway('Changing coordinates does not remove a real transfer between proposed spaces.')
