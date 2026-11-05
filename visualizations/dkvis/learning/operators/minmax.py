"""Variational eigenvalue control, using accepted Tau Ceti declarations."""
import numpy as np
from manim import Circle, DecimalNumber, ValueTracker, VGroup, always_redraw, linear
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.learning.operators.model import rayleigh_example
from dkvis.slide_style import CURRENT, FAINT, boxed, math, tex


class MinMaxSlide(LessonSlide):
    lesson_deck = 'operators-minmax'


class MmTitle(LessonTitle):
    lesson_deck = 'operators-minmax'
    series_title = 'Accepted operator foundations'
    title_lines = ('Rayleigh quotients and min-max',)
    subtitle = 'From directional measurements to eigenvalue stability.'


class MmQuestion(MinMaxSlide):
    def body(self):
        self.start()
        self.put(stack(tex('Can we control eigenvalues without tracking eigenvectors?', size=32),
            r'A=A^T,\qquad \rho_A(x)=x^TAx\quad(\|x\|=1)',
            tex('Measure the operator along a direction, then optimize over directions.', size=28),
            boxed(math(r'|\lambda_k(A+H)-\lambda_k(A)|\le\|H\|_{\rm op}', size=33), color=CURRENT),
            tex('Classical Courant--Fischer and Weyl theory; accepted Tau Ceti APIs.', size=26), buff=.45), y=.4, height=3.7)
        self.takeaway('A variational description lets a uniform form bound control every ordered eigenvalue.')


class MmRayleigh(MinMaxSlide):
    example = True
    stage = 1
    def body(self):
        self.start()
        axes=plane(extent=1.4)
        circle=Circle(radius=np.linalg.norm(axes.c2p(1,0)-axes.c2p(0,0)), color=FAINT).move_to(axes.c2p(0,0))
        self.put(VGroup(axes,circle),'left',y=.2)
        angle=ValueTracker(0)
        self.add(always_redraw(lambda:vector(axes,rayleigh_example(angle.get_value())[1],CURRENT)))
        self.put(stack(r'A=\operatorname{diag}(5,2),\quad x=(\cos t,\sin t)',
            boxed(math(r'\rho_A(x)=5\cos^2t+2\sin^2t',size=30),color=CURRENT),
            r'2\le\rho_A(x)\le5',size=29,buff=.5),'right',y=.65,height=2.7)
        value=DecimalNumber(5,num_decimal_places=2,font_size=34,color=CURRENT).move_to([3.25,-1.2,0])
        value.add_updater(lambda m:m.set_value(rayleigh_example(angle.get_value())[2]));self.add(value)
        self.beat();self.play(angle.animate.set_value(np.pi/2),run_time=4,rate_func=linear)
        self.takeaway('In an eigenbasis, the unit-vector Rayleigh quotient is a weighted average of eigenvalues.')


class MmMinMax(MinMaxSlide):
    stage=1
    def body(self):
        self.start()
        self.put(stack(r'\lambda_0\ge\cdots\ge\lambda_{n-1},\qquad 0\le k<n',
            boxed(math(r'\lambda_k=\max_{\dim V=k+1}\ \min_{x\in V,\ \|x\|=1}x^TAx',size=30),color=CURRENT),
            r'\dim V+(n-k)>n\quad\Longrightarrow\quad V\cap\operatorname{span}(e_k,\ldots,e_{n-1})\ne\{0\}',
            tex(r'Every candidate $V$ has a unit direction with quotient at most $\lambda_k$.',size=27),
            size=27,buff=.38),y=.65,height=2.9)
        self.beat()
        self.put(stack(r'V_0=\operatorname{span}(e_0,\ldots,e_k)',
            tex(r'All unit directions in $V_0$ have quotient at least $\lambda_k$; $e_k$ attains it.',size=26),buff=.25),y=-1.45,height=1.0)
        self.takeaway('The intersection argument gives one inequality; the leading eigenspace gives the other.')


class MmWeyl(MinMaxSlide):
    stage=2
    def body(self):
        self.start()
        self.put(stack(r'A=A^T,\quad H=H^T,\quad\|x\|=1',
            r'|x^THx|\le\|H\|_{\rm op}',
            r'\rho_A(x)-\varepsilon\le\rho_{A+H}(x)\le\rho_A(x)+\varepsilon,\quad\varepsilon=\|H\|_{\rm op}',
            tex('Take the same inner minimum and outer maximum on all three terms.',size=27),
            boxed(math(r'|\lambda_k(A+H)-\lambda_k(A)|\le\varepsilon',size=34),color=CURRENT),buff=.36),y=.35,height=3.7)
        self.takeaway('Ordered eigenvalues are stable in operator norm; eigenspace control additionally needs a gap.')


class MmSummary(MinMaxSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Directional form values reveal the spectrum.',size=31),
            tex('A dimension argument forces every candidate subspace to meet a low spectral sector.',size=27),
            tex('The leading spectral subspace attains the matching lower bound.',size=28),
            tex('Uniform perturbation bounds pass through both variational extrema.',size=28),buff=.45),y=.4,height=3.5)
        self.source('Tau Ceti CourantFischer; DKPS proof adaptation (PR 13599).')
        self.takeaway('The theorem is classical; the formalization makes the hypotheses and indexing explicit.')


class MmComputation(MinMaxSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex(r'Dense symmetric/Hermitian matrices: \texttt{scipy.linalg.eigh}.',size=29),
            tex('Use a symmetry-aware eigensolver and request the part of the spectrum needed.',size=28),
            r'\|Av-\mu v\|\quad\text{measures the residual of a proposed eigenpair}',
            tex('Check normalization, residuals, and the ordering returned by the routine.',size=28),
            tex('This lecture uses decreasing order; SciPy returns increasing order.',size=28),buff=.45),y=.4,height=3.5)
        self.source('SciPy eigh documentation; Tau Ceti CourantFischer indexing convention.')
        self.takeaway('The min-max characterization proves stability; a numerical eigensolver computes approximations.')


class MmFacts(MinMaxSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex(r'Finite real inner product space; $T,S$ symmetric; decreasing zero-based eigenvalues.',size=26),
            boxed(math(r'\lambda_k(T)=\max_{\dim V=k+1}\min_{x\in V,\ \|x\|=1}\langle Tx,x\rangle',size=30),color=CURRENT),
            boxed(math(r'|\lambda_k(T)-\lambda_k(S)|\le\|T-S\|',size=34),color=CURRENT),
            tex('The Lean extrema use supremum and infimum notation.',size=27),buff=.5),y=.45,height=3.5)
        self.takeaway('Keep the scalar field, symmetry, finite dimension, and eigenvalue ordering in the statement.')


class MmLean(LessonLean):
    lesson_deck='operators-minmax'
    lecture_id='minmax'
    symbolic_facts=(('Min-max',r'\lambda_k=\sup_{\dim V=k+1}\inf_{x\in V,\ \|x\|=1}\langle Tx,x\rangle'),
                    ('Weyl stability',r'|\lambda_k(T)-\lambda_k(S)|\le\|T-S\|'))
    ownership='Tau Ceti: CourantFischer; DKPS-derived proof adaptation, PR 13599.'
    notation=r'\texttt{Fin n} indexes $0,\ldots,n-1$; \texttt{IsSymmetric} is self-adjointness here.'
