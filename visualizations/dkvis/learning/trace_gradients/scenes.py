"""Entrywise dot products, scalar derivatives, and restricted tests."""
import numpy as np
from manim import Create, Dot, SurroundingRectangle, Transform, ValueTracker, VGroup, always_redraw, linear
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack
from dkvis.slide_style import CURRENT, TRIAL, RESID, boxed, math, tex

class TraceSlide(LessonSlide):
    lesson_deck='prereq-trace-gradients'
    stage_labels=('Pair entries','Differentiate','Test directions','Recap')
class TgTitle(LessonTitle):
    lesson_deck='prereq-trace-gradients'
    title_lines=('Trace pairings','and matrix gradients')
    subtitle='A scalar response to a matrix-shaped change.'
class TgPairing(TraceSlide):
    example=True
    def body(self):
        self.start();rows=stack(r'X=\begin{pmatrix}1&2\\0&-1\end{pmatrix},\quad D=\begin{pmatrix}0&1\\2&0\end{pmatrix}',
            r'\langle X,D\rangle_F=1\cdot0+2\cdot1+0\cdot2+(-1)\cdot0=2',size=34,buff=.65)
        self.put(rows,y=.8,height=2.6)
        focus=SurroundingRectangle(rows[0],color=TRIAL,buff=.15);self.play(Create(focus),run_time=1)
        self.beat();self.play(Transform(focus,SurroundingRectangle(rows[1],color=RESID,buff=.15)),run_time=1)
        self.put(boxed(math(r'\langle X,D\rangle_F=\operatorname{tr}(X^TD)',size=38),color=CURRENT),y=-1.3,height=1)
        self.takeaway('Transpose aligns matching entries; the trace adds their products.')
class TgCyclic(TraceSlide):
    stage=1
    def body(self):
        self.start();self.put(stack(r'\operatorname{tr}(AB)=\sum_{i,j}a_{ij}b_{ji}=\operatorname{tr}(BA)',
            boxed(math(r'\operatorname{tr}(ABC)=\operatorname{tr}(BCA)=\operatorname{tr}(CAB)',size=30),color=CURRENT),
            tex('Cyclic rearrangement does not imply arbitrary reordering.',size=29),
            r'AB\ne BA\quad\text{can hold even when their traces agree.}',buff=.5),y=.4,height=3.5)
        self.takeaway('This is an equality of scalars, not a commutation law for matrices.')
class TgDerivative(TraceSlide):
    example=True;stage=1
    def body(self):
        from manim import Axes
        self.start();axes=Axes(x_range=[-1,1,.5],y_range=[0,9,3],x_length=5,y_length=3,tips=False)
        self.put(axes,'left',y=.2);self.add(math('t',size=25).move_to(axes.get_right()+np.array([.15,-.25,0])),math(r'F(X+tD)',size=25).move_to(axes.get_top()+np.array([0,.28,0])))
        curve=axes.plot(lambda t:3+2*t+2.5*t*t,x_range=[-1,1],color=CURRENT)
        t=ValueTracker(-.8);self.add(curve,always_redraw(lambda:Dot(axes.c2p(t.get_value(),3+2*t.get_value()+2.5*t.get_value()**2),color=TRIAL)))
        self.put(stack(r'F(X)=\tfrac12\|X\|_F^2',r'F(X+tD)=F(X)+t\langle X,D\rangle_F+\tfrac12t^2\|D\|_F^2',
            boxed(math(r'\left.\frac{d}{dt}F(X+tD)\right|_{t=0}=\langle X,D\rangle_F',size=29),color=RESID),
            r'\nabla F(X)=X',size=29,buff=.45),'right',y=.4,height=3.7)
        self.beat();self.add(axes.plot(lambda t:3+2*t,x_range=[-.8,.8],color=RESID));self.play(t.animate.set_value(.8),run_time=3,rate_func=linear)
        self.takeaway('The gradient records all directional slopes; this graph displays just one direction.')
class TgTests(TraceSlide):
    stage=2
    def body(self):
        self.start();self.put(stack(r'\langle H,D\rangle_F=0\quad\text{for every }D\quad\Rightarrow\quad H=0',
            tex('Test with D = H to obtain a sum of squares.',size=28),
            r'H=\begin{pmatrix}0&1\\2&0\end{pmatrix},\qquad D=\begin{pmatrix}a&0\\0&b\end{pmatrix}',
            boxed(math(r'\langle H,D\rangle_F=0\text{ for every diagonal }D,\quad H\ne0',size=29),color=CURRENT),buff=.4),y=.4,height=3.6)
        self.takeaway('A restricted family of tests sees only the corresponding part of a gradient.')
class TgSkew(TraceSlide):
    stage=2
    def body(self):
        self.start();self.put(stack(r'G^T=-G\quad\Rightarrow\quad\langle G,B\rangle_F=-\operatorname{tr}(GB)',
            r'J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad J^2=-I',
            r'G=aJ,\quad B=bJ\quad\Rightarrow\quad-\operatorname{tr}(GB)=2ab',
            boxed(math(r'B=G\quad\Rightarrow\quad-\operatorname{tr}(G^2)=\|G\|_F^2',size=30),color=RESID),buff=.5),y=.4,height=3.7)
        self.takeaway('The minus sign expresses skew-symmetry; it is not a different inner product.')
class TgSummary(TraceSlide):
    stage=3
    def body(self):
        self.start();self.put(stack(r'\langle X,D\rangle_F=\operatorname{tr}(X^TD)',
            r'DF(X)[D]=\langle\nabla F(X),D\rangle_F',
            tex('Specify the legal directions before interpreting a zero derivative.',size=29),
            tex('Stationarity is necessary at a differentiable minimum; it is not sufficient.',size=27),buff=.5),y=.4,height=3.4)
        self.takeaway('Pair entries, identify the response matrix, and then state which tests are available.')
class TgFacts(TraceSlide):
    stage=3
    def body(self):
        self.start();self.put(stack(boxed(math(r'\operatorname{tr}(AB)=\operatorname{tr}(BA)',size=39),color=CURRENT),
            boxed(math(r'\operatorname{tr}(C^TC)=0\iff C=0',size=39),color=RESID),
            tex('Keep the transpose: zero ordinary trace is a much weaker condition.',size=28),buff=.65),y=.4,height=3.4)
        self.takeaway('Cyclicity rearranges the scalar test; positivity detects a vanishing matrix.')
class TgLean(LessonLean):
    lesson_deck='prereq-trace-gradients';lecture_id='trace_gradients'
    symbolic_facts=(('Trace cyclicity',r'\operatorname{tr}(AB)=\operatorname{tr}(BA)'),('Positive pairing',r'\operatorname{tr}(C^TC)=0\iff C=0'))
    assumptions='Finite square real matrices; transpose and trace have their usual meanings.'
    ownership='Mathlib Matrix/Trace and Matrix/PosDef: existing trace identities.'
    notation=r'\texttt{trace} sums diagonal entries; the matrix product remains ordered.'
class TgLeanPositive(TgLean):fact_index=1
class TgComputation(TraceSlide):
    bonus=True
    def body(self):
        self.start();self.put(stack(r'\frac{F(X+hD)-F(X-hD)}{2h}\ \approx\ \langle\nabla F(X),D\rangle_F',
            tex('Try multiple directions and a range of step sizes.',size=30),
            tex('Large steps have approximation error; tiny steps can amplify roundoff.',size=27),
            tex('Automatic differentiation still needs the right shapes and conventions.',size=27),buff=.5),y=.4,height=3.4)
        self.takeaway('A numerical derivative check supplies evidence, not an exact stationarity proof.')
