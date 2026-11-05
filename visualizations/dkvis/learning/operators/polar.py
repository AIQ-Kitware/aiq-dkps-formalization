"""Modulus and canonical polar partial isometry, including singular maps."""
import numpy as np
from manim import Dot, ParametricFunction, Transform, VGroup
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.learning.operators.model import polar_example
from dkvis.slide_style import CURRENT, TRIAL, WANTED, boxed, math, tex


class PolarSlide(LessonSlide):
    lesson_deck='operators-polar'


class PoTitle(LessonTitle):
    lesson_deck='operators-polar'
    series_title = 'Accepted operator foundations'
    title_lines=('Operator absolute value','and polar decomposition')
    subtitle='Separate the length effect from the remaining motion.'


class PoQuestion(PolarSlide):
    example=True
    def body(self):
        self.start()
        axes=plane(extent=2.3)
        circle=ParametricFunction(lambda t:axes.c2p(np.cos(t),np.sin(t)),t_range=[0,2*np.pi],color=TRIAL)
        self.put(VGroup(axes,circle),'left',y=.1)
        self.put(stack(r'|z|=\sqrt{\overline z z}\quad\leadsto\quad |A|=\sqrt{A^*A}',
            tex('Scalar magnitude becomes a positive operator.',size=28),
            boxed(math(r'A=U|A|',size=40),color=CURRENT),size=31,buff=.5),'right',y=.3,height=3.2)
        stretch=ParametricFunction(lambda t:axes.c2p(2*np.cos(t),.8*np.sin(t)),t_range=[0,2*np.pi],color=CURRENT)
        self.beat();self.play(Transform(circle,stretch),run_time=1.2)
        self.takeaway('First account for how lengths change; then identify the motion needed to reach the output.')


class PoModulus(PolarSlide):
    stage=1
    def body(self):
        self.start()
        self.put(stack(r'|A|=(A^*A)^{1/2},\qquad |A|\ge0',
            r'|A|^2=A^*A',
            boxed(math(r'\||A|x\|^2=\langle A^*Ax,x\rangle=\|Ax\|^2',size=32),color=CURRENT),
            tex('The positive square root selects the unique positive candidate.',size=28),
            tex('The modulus records a length effect in every input direction.',size=29),buff=.43),y=.4,height=3.6)
        self.takeaway('Absolute value is an operator, not an entrywise absolute value of a matrix.')


class PoKernel(PolarSlide):
    stage=1
    def body(self):
        self.start()
        self.put(stack(r'U(|A|x)=Ax',
            tex('The equal-norm identity makes this rule well-defined and isometric on its initial space.',size=27),
            r'U=0\quad\text{on }\ker A',
            boxed(math(r'\|Ux\|=\|x\|\quad(x\in(\ker A)^\perp)',size=32),color=CURRENT),
            tex('A partial isometry preserves lengths on its support and vanishes on the kernel.',size=27),buff=.4),y=.4,height=3.6)
        self.takeaway('The zero-on-kernel condition distinguishes the canonical factor from arbitrary extensions.')


class PoExample(PolarSlide):
    example=True
    stage=2
    def body(self):
        self.start()
        a,modulus,partial=polar_example()
        axes=plane(extent=2.4)
        self.put(axes,'left',y=.2)
        self.add(vector(axes,[2,0],TRIAL),vector(axes,a[:,0],WANTED),Dot(axes.c2p(0,0),color=CURRENT))
        self.put(stack(r'A=R_\theta\begin{pmatrix}2&0\\0&0\end{pmatrix}',
            r'|A|=\begin{pmatrix}2&0\\0&0\end{pmatrix},\quad U=R_\theta\begin{pmatrix}1&0\\0&0\end{pmatrix}',
            r'Ae_2=Ue_2=0,\qquad\|Ue_1\|=1',size=29,buff=.5),'right',y=.5,height=3.4)
        self.takeaway('A singular map has a canonical partial isometry; that factor need not be an orthogonal matrix.')


class PoSummary(PolarSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(r'A=U|A|,\quad |A|\ge0,\quad\ker U=\ker A',
            tex('Finite matrices illustrate the geometry.',size=30),
            tex('Accepted Tau Ceti APIs also cover bounded operators between Hilbert spaces.',size=27),
            tex('In that setting, extend the isometry to the closure of the modulus range.',size=27),
            tex('A unitary extension, when available, is a separate choice on the kernel.',size=28),buff=.4),y=.4,height=3.5)
        self.source('Tau Ceti Polar/Finite and Polar/Bounded; accepted independent implementations.')
        self.takeaway('Distinguish the canonical partial factor, its support, and any selected unitary extension.')


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
