"""Modulus and canonical polar partial isometry, including singular maps."""
import numpy as np
from manim import Create, Dot, ParametricFunction, SurroundingRectangle, Transform, VGroup, DOWN
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.learning.operators.model import polar_example
from dkvis.slide_style import CURRENT, TRIAL, WANTED, MUTED, boxed, math, tex


class PolarSlide(LessonSlide):
    lesson_deck='operators-polar'
    stage_labels=('Length effect', 'Construct motion', 'Collapsed inputs', 'Recap')

    def focus_rows(self, rows):
        focus=SurroundingRectangle(rows[0],color=CURRENT,buff=.14)
        self.play(Create(focus),run_time=1)
        for row in rows[1:]:
            self.play(Transform(focus,SurroundingRectangle(row,color=CURRENT,buff=.14)),run_time=1)


class PoTitle(LessonTitle):
    lesson_deck='operators-polar'
    series_title = 'Accepted operator foundations'
    title_lines=('Operator absolute value','and polar decomposition')
    subtitle='Separate the length effect from the remaining motion.'


LEARNING_FACTS = (
    'The modulus gives every input the same output length as A.',
    'A factors into a positive stretch followed by length-preserving motion.',
    'Collapsed inputs require a partial isometry, not always a unitary map.',
)


class PoOutcomes(PolarSlide):
    def body(self):
        self.start()
        rows=stack(*(tex(f'{i}. {fact}',size=29) for i,fact in enumerate(LEARNING_FACTS,1)),buff=.6)
        self.put(rows,y=.3,height=3.4)
        self.takeaway('Finite real or complex inner product spaces; singular maps are included.')
        self.focus_rows(rows)


class PoQuestion(PolarSlide):
    example=True
    def body(self):
        self.start()
        axes=plane(extent=2.3)
        self.put(axes,'left',y=.1)
        def curve(scale,angle,color):
            rot=np.array([[np.cos(angle),-np.sin(angle)],[np.sin(angle),np.cos(angle)]])
            return ParametricFunction(lambda t:axes.c2p(*(rot@(scale*np.array([np.cos(t),np.sin(t)])))),t_range=[0,2*np.pi],color=color)
        circle=curve(np.array([1,1]),0,MUTED)
        self.add(circle.copy().set_opacity(.4),circle)
        rows=stack(tex('Input circle (gray)',size=27,color=MUTED),
            math(r'|A|=\begin{pmatrix}2&0\\0&0.8\end{pmatrix}',size=32),
            tex('Positive stretch: same output lengths as A.',size=26,color=TRIAL),
            math(r'A=R_{0.6}|A|',size=33),
            tex('Then rotate to reach the actual output.',size=26,color=WANTED),buff=.25)
        self.put(rows,'right',y=.25,height=3.7)
        ellipse=curve(np.array([2,.8]),0,TRIAL)
        self.play(Transform(circle,ellipse),run_time=2)
        # Retain the intermediate ellipse: corresponding arrows show equal lengths.
        intermediate=circle.copy(); self.add(intermediate)
        first=vector(axes,[2,0],TRIAL); self.add(first)
        self.beat()
        actual=curve(np.array([2,.8]),.6,WANTED)
        self.play(Transform(circle,actual),run_time=2)
        self.play(Create(vector(axes,2*np.array([np.cos(.6),np.sin(.6)]),WANTED)),run_time=1)
        self.takeaway('The modulus retains directional stretching; it removes the remaining rotation or reflection.')


class PoModulus(PolarSlide):
    stage=0
    def body(self):
        self.start()
        rows=stack(r'\|Ax\|^2=\langle A^*Ax,x\rangle',
            tex(r'$A^*A$ records squared output lengths as an operator.',size=28),
            r'|A|=(A^*A)^{1/2},\quad |A|\ge0,\quad |A|^2=A^*A',
            boxed(math(r'\||A|x\|=\|Ax\|\quad\text{for every input }x',size=32),color=CURRENT),buff=.45)
        self.put(rows,y=.4,height=3.6)
        self.takeaway('The square root recovers length scale from squared length; it is not a smoothing operation.')
        self.focus_rows(VGroup(rows[0],rows[2],rows[3]))
        self.beat()
        self.put(tex('Positive: perpendicular eigen-directions are scaled by nonnegative amounts.',size=27),y=-1.85,height=.5)


class PoKernel(PolarSlide):
    stage=1
    def body(self):
        self.start()
        rows=stack(tex('After the stretch, where must the remaining motion send each vector?',size=27),
            boxed(math(r'U(|A|x)=Ax',size=39),color=CURRENT),
            r'|A|x=|A|y\ \Rightarrow\ |A|(x-y)=0\ \Rightarrow\ A(x-y)=0',
            r'\|U(|A|x)\|=\|Ax\|=\||A|x\|',size=30,buff=.42)
        self.put(rows,y=.6,height=3.2)
        self.focus_rows(VGroup(rows[1],rows[2],rows[3]))
        self.beat()
        self.put(stack(r'\operatorname{range}|A|=(\ker A)^\perp,\qquad U=0\text{ on }\ker A',
                       tex('Finite dimensions: these two perpendicular spaces cover all inputs.',size=26),size=29,buff=.16),y=-1.55,height=.9)
        self.takeaway('The rule is possible because the modulus and A collapse exactly the same inputs.')


class PoExample(PolarSlide):
    example=True
    stage=2
    def body(self):
        self.start()
        a,modulus,partial=polar_example()
        axes=plane(extent=2.4)
        self.put(axes,'left',y=.2)
        first=vector(axes,[2,0],TRIAL)
        second=vector(axes,a[:,0],WANTED)
        self.add(first,Dot(axes.c2p(0,0),color=CURRENT))
        rows=stack(r'A=R_{0.6}\begin{pmatrix}2&0\\0&0\end{pmatrix}',
            r'|A|=\begin{pmatrix}2&0\\0&0\end{pmatrix},\quad U=R_{0.6}\begin{pmatrix}1&0\\0&0\end{pmatrix}',
            r'Ae_2=Ue_2=0,\qquad\|Ue_1\|=1',size=29,buff=.5)
        self.put(rows,'right',y=.5,height=3.4)
        self.play(Create(second),run_time=2)
        self.beat()
        self.focus_rows(VGroup(rows[1],rows[2]))
        self.takeaway('U rotates the surviving line and kills its perpendicular line: a partial isometry.')


class PoSummary(PolarSlide):
    stage=3
    def body(self):
        self.start()
        rows=stack(*(tex(fact,size=28) for fact in LEARNING_FACTS),
                   boxed(math(r'\||A|x\|=\|Ax\|,\qquad A=U|A|,\qquad U|_{\ker A}=0',size=31),color=CURRENT),buff=.45)
        self.put(rows,y=.45,height=3.3)
        self.focus_rows(VGroup(*rows[:3]))
        self.beat()
        self.put(tex('Hilbert spaces: extend the isometry to the closure of the modulus range.',size=26),y=-1.7,height=.6)
        self.takeaway('Same directional length effect, then the motion that reaches the actual output.')


class PoComputation(PolarSlide):
    bonus = True
    stage=3
    def body(self):
        self.start()
        self.put(stack(r'A=L\Sigma V^*,\qquad |A|=V\Sigma V^*',
            boxed(math(r'U_{\rm can}=L\operatorname{diag}(1_{\{\sigma_j>0\}})V^*',size=30),color=CURRENT),
            tex('Numerical rank uses a tolerance; the exact formula uses positivity.',size=28),
            tex('Many square polar routines return a unitary extension, even for singular inputs.',size=27),
            tex('Match the routine\'s kernel convention to the formal statement.',size=28),buff=.42),y=.4,height=3.6)
        self.source('SciPy polar and SVD documentation; Tau Ceti canonical polar-factor definition.')
        self.takeaway('A factorization identity alone does not determine how a numerical factor acts on the kernel.')


class PoFacts(PolarSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Finite real inner product spaces; A is any linear map.',size=28),
            boxed(math(r'A=U|A|',size=40),color=CURRENT),
            boxed(math(r'x\in(\ker A)^\perp\ \Longrightarrow\ \|Ux\|=\|x\|',size=32),color=CURRENT),
            tex('Here U is the canonical factor, including its zero-on-kernel convention.',size=28),buff=.5),y=.4,height=3.4)
        self.takeaway('No invertibility hypothesis is needed for these two statements.')


class PoLean(LessonLean):
    assumptions = '$A:E\\to F$ is linear. Both spaces are finite real inner product spaces; $U$ is canonical.'
    lesson_deck='operators-polar'
    lecture_id='polar'
    symbolic_facts=(('Factorization',r'U|A|=A'),('Isometry on the support',r'x\in(\ker A)^\perp\Rightarrow\|Ux\|=\|x\|'))
    ownership='Tau Ceti: LinearMap.operatorAbs and LinearMap.polarFactor (accepted finite API).'
    notation=r'\texttt{operatorAbs} is $|A|$; \texttt{polarFactor} is the canonical $U$; $\circ_\ell$ is composition.'


class PoLeanSupport(PoLean):
    fact_index = 1
