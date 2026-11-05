"""A short, visual review of the mathematics assumed by the learning modules."""
import numpy as np
from manim import Arc, Circle, DashedLine, Dot, Line, ValueTracker, VGroup, always_redraw, linear
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.learning.basics.model import matrix_action, unit_direction, eigen_action, square_slope
from dkvis.slide_style import CURRENT, FAINT, GAP, MUTED, SINE, TRIAL, WANTED, boxed, math, para, tex


def note(text, width=5.3):
    return para(text, width=width, size=26)


class BasicsSlide(LessonSlide):
    lesson_deck='prereq-basics'


class BaTitle(LessonTitle):
    lesson_deck='prereq-basics'
    series_title='000010 · Before the series'
    title_lines=('A mathematics refresher',)
    subtitle='The language of vectors, geometry, and change.'


class BaNumbers(BasicsSlide):
    example=True
    def body(self):
        self.start()
        axes=plane(extent=1.8)
        self.put(axes,'left',y=.25)
        self.add(vector(axes,[1,1],CURRENT),Dot(axes.c2p(1,1),color=CURRENT),
                 math('1+i',size=29).move_to(axes.c2p(1.5,1.3)),
                 tex('real',size=23,color=TRIAL).move_to(axes.c2p(1.9,-.2)),
                 tex('imaginary',size=23,color=WANTED).move_to(axes.c2p(.6,1.6)))
        self.put(stack(r'\mathbb R:\ \text{numbers on a line}',
            r'\mathbb C:\ z=a+bi,\quad i^2=-1',
            r'\overline z=a-bi,\qquad |z|^2=a^2+b^2',
            note('A scalar is one number. A vector is an ordered collection of coordinates.'),
            r'x=\begin{pmatrix}x_1\\x_2\end{pmatrix}\in\mathbb R^2',size=29,buff=.30),'right',y=.35,height=3.7)
        self.takeaway('A complex number is one scalar; a vector may have real or complex coordinates.')


class BaMatrices(BasicsSlide):
    example=True
    stage=1
    def body(self):
        self.start()
        axes=plane(extent=3)
        self.put(axes,'left',y=.3)
        self.add(vector(axes,[1,2],TRIAL),math('x',size=26,color=TRIAL).move_to(axes.c2p(.7,2.2)))
        self.put(stack(r'A=\begin{pmatrix}2&1\\0&1\end{pmatrix},\quad x=\begin{pmatrix}1\\2\end{pmatrix}',
            r'Ax=1\begin{pmatrix}2\\0\end{pmatrix}+2\begin{pmatrix}1\\1\end{pmatrix}=\begin{pmatrix}4\\2\end{pmatrix}',
            tex('Columns = images of coordinate directions.',size=24),
            r'A(au+bv)=aAu+bAv',
            r'Ix=x;\quad A^{-1}Ax=x\ \text{if }A^{-1}\text{ exists}',size=29,buff=.40),'right',y=.55,height=3.6)
        self.beat()
        self.add(vector(axes,matrix_action([1,2]),WANTED),
            math('Ax',size=26,color=WANTED).move_to(axes.c2p(3.8,2.3)))
        self.takeaway('Matrix multiplication applies a linear rule; ABx means apply B first, then A.')


class BaSpaces(BasicsSlide):
    example=True
    stage=1
    def body(self):
        self.start()
        axes=plane(extent=3);self.put(axes,'left',y=.3)
        self.add(vector(axes,[2,0],TRIAL),vector(axes,[1,1],WANTED),
            vector(axes,[4,2],CURRENT),
            math('a_1',size=25,color=TRIAL).move_to(axes.c2p(2,-.35)),
            math('a_2',size=25,color=WANTED).move_to(axes.c2p(.6,1.3)))
        self.put(stack(r'Ax=x_1a_1+x_2a_2',
            note('Span: all combinations of the chosen vectors.'),
            note('Basis: enough independent directions to describe every vector uniquely.'),
            note('Dimension: the number of vectors in a basis.'),
            r'\ker A=\{x:Ax=0\},\quad\operatorname{range}A=\{Ax:x\}',
            size=29,buff=.30),'right',y=.4,height=3.8)
        self.takeaway('A subspace is closed under vector addition and scalar multiplication; it contains zero.')


class BaInner(BasicsSlide):
    example=True
    stage=1
    def body(self):
        self.start()
        axes=plane(extent=2);self.put(axes,'left',y=.3)
        self.add(vector(axes,[1,1],TRIAL),vector(axes,[-1,1],WANTED),
            math('u=(1,1)',size=23,color=TRIAL).move_to(axes.c2p(1.2,1.35)),
            math('v=(-1,1)',size=23,color=WANTED).move_to(axes.c2p(-1.3,1.35)))
        self.put(stack(r'\langle u,v\rangle=\sum_j u_jv_j\quad(\text{real coordinates})',
            r'\langle u,v\rangle=1(-1)+1(1)=0',
            boxed(math(r'\|x\|^2=\langle x,x\rangle',size=35),color=CURRENT),
            note('Orthogonal means inner product zero. Orthonormal adds unit length.'),
            r'\langle z,w\rangle=\sum_j\overline{z_j}w_j\quad(\text{complex coordinates})',size=27,buff=.32),'right',y=.4,height=3.7)
        self.takeaway('The inner product measures alignment and defines length; orthogonality means zero pairing.')


class BaAdjoints(BasicsSlide):
    stage=1
    def body(self):
        self.start()
        self.put(stack(tex('Move a map across an inner product',size=29),
            r'\langle Ax,y\rangle=\langle x,A^*y\rangle',
            r'A^*=\overline A^{\,T}',
            note('The adjoint is transpose over the reals; conjugate transpose over the complex numbers.'),
            r'A=A^*:\ \text{self-adjoint}',buff=.34),'left',y=.35,height=3.7)
        self.put(stack(tex('Preserve lengths and inner products',size=29),
            r'Q^*Q=I\quad\text{for a square }Q',
            note('Real: an orthogonal matrix. Complex: a unitary matrix.'),
            r'\|Qx\|=\|x\|',
            note('A symmetric real matrix is self-adjoint; it need not preserve lengths.'),buff=.35),'right',y=.35,height=3.7)
        self.takeaway('Perpendicular vectors, self-adjoint maps, and length-preserving maps are distinct ideas.')


class BaTrig(BasicsSlide):
    example=True
    stage=1
    def body(self):
        self.start()
        axes=plane(extent=1.5);self.put(axes,'left',y=.3)
        radius=np.linalg.norm(axes.c2p(1,0)-axes.c2p(0,0))
        self.add(Circle(radius=radius,color=FAINT).move_to(axes.c2p(0,0)))
        theta=ValueTracker(0)
        def picture():
            x,y=unit_direction(theta.get_value())
            return VGroup(vector(axes,[x,y],CURRENT),
                Line(axes.c2p(0,0),axes.c2p(x,0),color=TRIAL,stroke_width=5),
                DashedLine(axes.c2p(x,0),axes.c2p(x,y),color=WANTED),Dot(axes.c2p(x,y),color=CURRENT),
                Arc(radius=.35,start_angle=0,angle=max(.001,theta.get_value()),color=SINE).move_arc_center_to(axes.c2p(0,0)),
                math(r'\theta',size=24,color=SINE).move_to(axes.c2p(.5*np.cos(theta.get_value()/2),.5*np.sin(theta.get_value()/2)+.12)),
                math(r'\cos\theta',size=23,color=TRIAL).move_to(axes.c2p(x/2,-.24)),
                math(r'\sin\theta',size=23,color=WANTED).move_to(axes.c2p(x+.34,y/2)))
        self.add(always_redraw(picture))
        self.put(stack(r'x=(\cos\theta,\sin\theta)',
            r'\cos^2\theta+\sin^2\theta=1',
            r'\pi\ \text{radians}=180^\circ',
            r'\tan\theta=\sin\theta/\cos\theta\quad(\cos\theta\ne0)',
            boxed(math(r'\cos\theta=\frac{\langle u,v\rangle}{\|u\|\|v\|}',size=31),color=CURRENT),
            tex('Last formula: nonzero real vectors.',size=23),size=29,buff=.30),'right',y=.4,height=3.8)
        self.beat();self.play(theta.animate.set_value(np.pi/3),run_time=4,rate_func=linear)
        self.takeaway('Sine and cosine are unit-circle coordinates; the real inner product recovers the angle.')


class BaEigen(BasicsSlide):
    example=True
    stage=2
    def body(self):
        self.start()
        axes=plane(extent=2.5);self.put(axes,'left',y=.3)
        theta=ValueTracker(0)
        self.add(always_redraw(lambda:VGroup(vector(axes,eigen_action(unit_direction(theta.get_value())),WANTED),
            vector(axes,unit_direction(theta.get_value()),TRIAL))))
        self.put(stack(boxed(math(r'Av=\lambda v,\quad v\ne0',size=36),color=CURRENT),
            r'A=\begin{pmatrix}2&0\\0&1\end{pmatrix}',
            r'Ae_1=2e_1,\qquad Ae_2=e_2',
            note('An eigenvector is scaled without leaving its line. The scale is the eigenvalue.'),
            note('Real symmetric matrices admit an orthonormal eigenbasis. General matrices need not.'),size=29,buff=.34),'right',y=.4,height=3.8)
        self.beat();self.play(theta.animate.set_value(np.pi/2),run_time=4,rate_func=linear)
        self.takeaway('Eigenvalues describe special directions, not the action along every vector.')


class BaMeasurements(BasicsSlide):
    example=True
    stage=2
    def body(self):
        self.start()
        self.put(stack(tex('Length of a vector',size=30),
            r'\|(3,4)\|=\sqrt{3^2+4^2}=5',
            tex('Size of a linear map',size=30),
            r'\|A\|_{\rm op}=\max_{\|x\|=1}\|Ax\|',
            note('The operator norm is the largest output length for a unit input.'),buff=.34),'left',y=.35,height=3.7)
        self.put(stack(r'A=\operatorname{diag}(2,1)',
            r'\|A\|_{\rm op}=2',
            tex('Trace: add the diagonal entries',size=29),
            r'\operatorname{tr}A=2+1=3',
            note('The trace is a signed sum, not a norm. Trace norm is a different quantity, taught later.'),buff=.38),'right',y=.35,height=3.7)
        self.takeaway('Read the object being measured: vector length, operator norm, and trace answer different questions.')


class BaLimits(BasicsSlide):
    stage=1
    def body(self):
        self.start()
        self.put(stack(tex('A limit describes what values approach.',size=31),
            r'a_n=2^{-n}:\quad 1,\ \tfrac12,\ \tfrac14,\ \tfrac18,\ldots\ \longrightarrow 0',
            tex('An infinite sum is a limit of finite partial sums.',size=29),
            r'1+\tfrac12+\cdots+2^{-N}\ \longrightarrow\ 2',
            tex('Approaching a value does not mean reaching it after finitely many steps.',size=27),
            tex('Later: derivatives, power series, and integrals with an infinite endpoint.',size=26),buff=.37),y=.4,height=3.7)
        self.takeaway('Infinite formulas require convergence; not every sequence or series has a finite limit.')


class BaDerivative(BasicsSlide):
    example=True
    stage=2
    def body(self):
        self.start()
        axes=plane(extent=2.7);self.put(axes,'left',y=.3)
        curve=axes.plot(lambda t:t*t,x_range=[-1.45,1.45],color=CURRENT)
        t=ValueTracker(-1)
        def tangent():
            value,slope=square_slope(t.get_value());x=t.get_value()
            return VGroup(Dot(axes.c2p(x,value),color=GAP),
                Line(axes.c2p(x-.55,value-.55*slope),axes.c2p(x+.55,value+.55*slope),color=TRIAL))
        self.add(curve,always_redraw(tangent))
        self.put(stack(r'f^\prime(t)=\lim_{h\to0}\frac{f(t+h)-f(t)}h',
            r'f(t)=t^2,\qquad f^\prime(t)=2t',
            note('A derivative is the instantaneous rate of change, or tangent slope.'),
            r'\frac{d}{dt}f(g(t))=f^\prime(g(t))g^\prime(t)',
            note('A differentiable function at an interior local minimum has derivative zero. The converse can fail.'),size=27,buff=.32),'right',y=.4,height=3.7)
        self.beat();self.play(t.animate.set_value(1),run_time=4,rate_func=linear)
        self.takeaway('Differentiate along a scalar parameter, even when the changing object is a vector or matrix.')


class BaIntegral(BasicsSlide):
    example=True
    stage=2
    def body(self):
        self.start()
        axes=plane(extent=1.5);self.put(axes,'left',y=.3)
        curve=axes.plot(lambda t:t*t,x_range=[0,1.1],color=CURRENT)
        area=axes.get_area(curve,x_range=[0,1],color=WANTED,opacity=.25)
        self.add(area,curve,math(r'\int_0^1t^2\,dt=\tfrac13',size=29).move_to([-3.25,-1.6,0]))
        self.put(stack(note('Integration adds contributions over an interval; for a nonnegative scalar function, it is area.'),
            r'F(b)-F(a)=\int_a^b F^\prime(t)\,dt',
            tex('Displayed identity: F has a continuous derivative.',size=23),
            r'\int_0^\infty f(t)\,dt=\lim_{b\to\infty}\int_0^b f(t)\,dt',
            note('An infinite endpoint requires a convergent limit. Later, entries or vectors may be integrated too.'),size=28,buff=.38),'right',y=.4,height=3.7)
        self.takeaway('Differentiation measures local change; integration accumulates change over an interval.')


class BaRecap(BasicsSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Ready to continue?',size=34),
            tex('Can you multiply a small matrix by a vector and explain the result?',size=28),
            tex('Can you check perpendicularity and read sine and cosine on a circle?',size=28),
            tex('Can you read an eigenvector equation, a derivative, and a simple integral?',size=28),
            tex('If these are rusty, review them before relying on the later arguments.',size=27,color=MUTED),
            tex('Taught later: projections, singular values, matrix exponentials, and stationarity.',size=27),buff=.42),y=.4,height=3.8)
        self.takeaway('This is a refresher and a map of prerequisites, not a first course in linear algebra or calculus.')


class BaFacts(BasicsSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Two facts reused in later arguments',size=32),
            boxed(math(r'\langle x,x\rangle=\|x\|^2\qquad(\text{real inner product})',size=33),color=CURRENT),
            tex('Pairing a vector with itself gives its squared length.',size=28),
            boxed(math(r'\text{local minimum at }0\ +\ f^\prime(0)=d\quad\Longrightarrow\quad d=0',size=28),color=CURRENT),
            tex('The parameter ranges through an open neighborhood of zero.',size=26),
            tex('The next cards express exactly these two facts in Lean.',size=26),buff=.39),y=.4,height=3.7)
        self.takeaway('Keep the setting and hypotheses alongside the formula; a zero derivative alone does not prove a minimum.')


class BaLean(LessonLean):
    lesson_deck='prereq-basics'
    lecture_id='basics'
    assumptions='A vector x in a real inner product space E.'
    symbolic_facts=(('Length from pairing',r'\langle x,x\rangle=\|x\|^2'),
                    ('Minimum implies zero slope',r'\begin{gathered}0\text{ is a local minimum}\\f^\prime(0)=d\ \Longrightarrow\ d=0\end{gathered}'))
    ownership='Mathlib: InnerProductSpace.Basic and Calculus.LocalExtr.Basic.'
    notation=r'$\langle\cdot,\cdot\rangle_{\mathbb R}$ is the real inner product; $\|x\|$ is the norm.'


class BaLeanMinimum(BaLean):
    fact_index=1
    assumptions='A real function f has a local minimum at zero and derivative d there.'
    notation=r'\texttt{IsLocalMin} gives a local minimum; \texttt{HasDerivAt} specifies the derivative.'


class BaComputation(BasicsSlide):
    bonus=True
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Exact algebra and floating-point output answer different questions.',size=29),
            r'\langle u,v\rangle=0\quad\text{versus a computed value near zero}',
            tex('Computed angles near 90 degrees may give a tiny nonzero dot product.',size=27),
            tex('A tolerance depends on scale and numerical error; it is not an equality proof.',size=27),
            tex('For a proposed eigenpair, inspect the residual Av minus lambda v.',size=27),buff=.48),y=.4,height=3.5)
        self.takeaway('Use exact identities for proofs; interpret approximate numerical results with their scale and error.')
