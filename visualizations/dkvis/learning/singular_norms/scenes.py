"""Singular-value geometry and costs in the transport problem."""
import numpy as np
from manim import Arrow, Create, DashedLine, Dot, DOWN, Line, ParametricFunction, RIGHT, Rotate, Transform, UP, VGroup

from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, bars, plane, stack, vector
from dkvis.learning.matching.model import rotation
from dkvis.learning.singular_norms.model import block_displacement, competing_displacements, ellipse_example, overlapping_restrictions
from dkvis.slide_style import CURRENT, FAINT, FG, GAP, MUTED, RESID, SINE, TRIAL, WANTED, boxed, math, tex


class SnTitle(LessonTitle):
    lesson_deck = 'prereq-singular-norms'
    title_lines = ('Singular values', 'and displacement cost')
    subtitle = 'How a list of stretches determines the cost of a motion.'


class NormSlide(LessonSlide):
    lesson_deck = 'prereq-singular-norms'


class Sn00Question(NormSlide):
    example = True
    def body(self):
        self.start()
        reflection, turn = competing_displacements()
        self.add(tex('A: reflection', size=32, color=TRIAL).move_to([-3.25, 1.75, 0]),
                 tex('B: rotation', size=32, color=WANTED).move_to([3.25, 1.75, 0]),
                 bars(reflection, color=TRIAL).shift([-3.775, -.25, 0]),
                 bars(turn, color=WANTED).shift([2.725, -.25, 0]),
                 math(r's(I-W_A)=(2,0)', size=31).move_to([-3.25, -1., 0]),
                 math(r's(I-W_B)=(1.1,1.1)', size=31).move_to([3.25, -1., 0]))
        self.beat()
        self.add(math(r'\text{maximum: }1.1<2\ \Rightarrow B,\qquad'
                      r'\text{sum: }2<2.2\ \Rightarrow A', size=30).move_to([0, -1.65, 0]))
        self.takeaway('The cheapest map depends on what we choose to count.')


class Sn01History(NormSlide):
    def body(self):
        self.start()
        self.put(stack(tex('1936: Eckart and Young, low-rank approximation', size=32, color=CURRENT),
                       tex('Factor analysis asks for fewer independent directions.', size=28),
                       r'T=U\Sigma V^T',
                       tex('Choose input axes. Stretch. Choose output axes.', size=30),
                       tex('Our use: compute costs from the stretch list.', size=29), buff=.45),
                 y=.3, height=3.4)
        self.source('Eckart and Young (1936), The Approximation of One Matrix by Another of Lower Rank.')
        self.takeaway('Canonical coordinates reveal scalar quantities that can be compared and optimized.')


class Sn02Stretching(NormSlide):
    example = True
    stage = 1

    def body(self):
        self.start()
        t, u, singular, v = ellipse_example()
        ax = plane()
        circle = ParametricFunction(lambda a: ax.c2p(np.cos(a), np.sin(a)),
                                    t_range=[0, 2*np.pi], color=TRIAL)
        self.put(VGroup(ax, circle), 'left', y=.1)
        initial = [vector(ax, v[:, i], TRIAL) for i in range(2)]
        self.add(*initial)
        self.put(stack(r'T=U\Sigma V^T', r'\Sigma=\operatorname{diag}(2,0.75)',
                       tex('Singular values = ellipse semiaxis lengths.', size=27),
                       size=33, buff=.45), 'right', y=.65, height=2.6)
        self.beat()
        ellipse = ParametricFunction(lambda a: ax.c2p(*(t @ np.array([np.cos(a), np.sin(a)]))),
                                     t_range=[0, 2*np.pi], color=WANTED)
        self.play(Transform(circle, ellipse),
                  *(Transform(initial[i], vector(ax, singular[i]*u[:, i], WANTED)) for i in range(2)),
                  run_time=1.6)
        self.put(stack(boxed(math(r'Tv_j=s_j u_j,\quad s_j\ge0', size=28), color=CURRENT),
                       tex('Perpendicular input and output directions.', size=25), size=30),
                 'right', y=-1.2, height=1.4)
        self.takeaway('Singular values describe stretches; they need not be eigenvalues.')


class Sn03Norms(NormSlide):
    example = True
    stage = 1

    def body(self):
        self.start()
        self.put(stack(bars([2, .75]), r's(T)=(2,0.75)', size=30), 'left', y=.5, height=2.7)
        self.put(stack(r'\|T\|_{\mathrm{op}}=\max_j s_j=2',
                       r'\|T\|_F=\sqrt{\sum_j s_j^2}\approx2.136',
                       r'\|T\|_1=\sum_j s_j=2.75', size=32, buff=.5),
                 'right', y=.6, height=2.9)
        self.beat()
        self.add(math(r'T=\operatorname{diag}(-2,1):\quad'
                      r'\operatorname{tr}T=-1,\qquad\|T\|_1=3', size=28).move_to([0, -1.52, 0]),
                 math(r'\|T\|_1=\operatorname{tr}\sqrt{T^TT}', size=28, color=CURRENT).move_to([0, -2.08, 0]))
        self.takeaway('The trace norm sums nonnegative singular values, rather than signed eigenvalues.')


class Sn04Invariance(NormSlide):
    example = True
    stage = 1

    def body(self):
        self.start()
        t, u, s, v = ellipse_example()
        ax = plane()
        curve = ParametricFunction(lambda a: ax.c2p(*(t @ np.array([np.cos(a), np.sin(a)]))),
                                   t_range=[0, 2*np.pi], color=WANTED)
        self.put(VGroup(ax, curve), 'left', y=.15)
        self.put(stack(tex('Change orthonormal input or output axes.', size=28),
                       r'U_0^TU_0=I,\qquad V_0^TV_0=I',
                       r's(U_0TV_0^T)=s(T)', size=31, buff=.45), 'right', y=.6, height=2.6)
        self.beat()
        self.play(Rotate(curve, angle=.8, about_point=ax.c2p(0, 0)), run_time=1.2)
        self.put(stack(boxed(math(r'\|U_0TV_0^T\|=\|T\|', size=33), color=CURRENT),
                       tex('Operator, Frobenius, trace, and Schatten norms.', size=24)),
                 'right', y=-1.25, height=1.5)
        self.takeaway('Coordinates may change; the singular-value cost stays the same.')


class Sn05Rotation(NormSlide):
    example = True
    stage = 2

    def body(self):
        self.start()
        ax = plane(extent=1.6)
        source = Line(ax.c2p(-1.3, 0), ax.c2p(1.3, 0), color=TRIAL, stroke_width=4)
        theta = np.pi/6
        def target(angle):
            direction = np.array([np.cos(angle), np.sin(angle)])
            return Line(ax.c2p(*(-1.3*direction)), ax.c2p(*(1.3*direction)), color=WANTED, stroke_width=4)
        def mirror(angle):
            direction = np.array([np.cos(angle/2), np.sin(angle/2)])
            return DashedLine(ax.c2p(*(-1.35*direction)), ax.c2p(*(1.35*direction)), color=GAP)
        image, axis = target(theta), mirror(theta)
        self.put(VGroup(ax, source, image, axis), 'left', y=.45, height=2.8)
        label = math(r'\theta=30^\circ:\quad 4\sin(\theta/2)\approx1.035<2', size=26)
        self.add(label.move_to([-3.25, -1.45, 0]))
        self.put(stack(r'(I-R_\theta)^T(I-R_\theta)=4\sin^2(\theta/2)I',
                       r's(I-R_\theta)=(2\sin(\theta/2),2\sin(\theta/2))',
                       r'\|I-R_\theta\|_1=4\sin(\theta/2)',
                       r'\text{reflection: }s(I-W)=(2,0),\quad\|I-W\|_1=2',
                       size=27, buff=.4), 'right', y=.2, height=3.6)
        self.beat()
        delta = np.pi/2-theta
        self.play(Rotate(image, angle=delta, about_point=ax.c2p(0, 0)),
                  Rotate(axis, angle=delta/2, about_point=ax.c2p(0, 0)),
                  Transform(label, math(r'\theta=90^\circ:\quad 4\sin(\theta/2)=2\sqrt2>2',
                                        size=26).move_to(label)), run_time=1.3)
        self.add(tex('Dashed: reflection axis bisecting the source and target lines.',
                     size=23, color=MUTED).move_to([0, -2.05, 0]))
        self.takeaway(r'For one principal plane: compare $4\sin(\theta/2)$ with $2$.')


class Sn06SmoothCost(NormSlide):
    example = True
    stage = 2

    def body(self):
        self.start()
        self.put(stack(r'\|T\|_p=\left(\sum_j s_j(T)^p\right)^{1/p}',
                       r'\Phi_p(W)=\|I-W\|_p^p=\sum_j s_j(I-W)^p',
                       tex('The proof differentiates the power cost.', size=28),
                       r'p=1:\ \Phi_1(W)=\|I-W\|_1', size=29, buff=.45),
                 'left', y=.15)
        ax = plane(width=4.3, height=2.6, extent=1.3)
        cusp = ax.plot(lambda x: abs(x), x_range=[-1.1, 1.1, .02], color=GAP)
        self.put(VGroup(ax, cusp), 'right', y=.4, height=3.0)
        self.add(math(r'|t|', size=27, color=GAP).move_to([4.9, 1.15, 0]))
        self.beat()
        smooth = ax.plot(lambda x: abs(x)**1.5, x_range=[-1.1, 1.1, .02], color=CURRENT)
        self.play(Create(smooth), run_time=1)
        self.add(math(r'|t|^{1.5}', size=27, color=CURRENT).move_to([4.9, -.7, 0]),
                 tex('Scalar illustration of zero-slope smoothing.', size=24).move_to([3.25, -1.6, 0]))
        self.takeaway('Use a differentiable power cost first; later recover the trace-norm minimum.')


class Sn07BlockCosts(NormSlide):
    example = True
    stage = 2

    def body(self):
        self.start()
        self.put(stack(r'T=T_1\oplus T_2\quad\Longrightarrow\quad s(T)=s(T_1)\sqcup s(T_2)',
                       r'\|T\|_1=\|T_1\|_1+\|T_2\|_1',
                       r'\sum_j s_j(T)^p=\sum_j s_j(T_1)^p+\sum_j s_j(T_2)^p',
                       size=30, buff=.38), y=1.0, height=2.2)
        self.beat()
        first, second, full = block_displacement()
        self.put(VGroup(bars(np.linalg.svd(first, compute_uv=False), color=SINE),
                        bars(np.linalg.svd(second, compute_uv=False), color=GAP)).arrange(RIGHT, aligned_edge=DOWN, buff=1.5),
                 y=-1.0, height=1.45)
        self.put(math(r'\text{rotation displacement}:\ (1,1)\quad+\quad'
                      r'\text{reflection displacement}:\ (2,0)'
                      r'\quad\Longrightarrow\quad\text{trace cost }4', size=25),
                 y=-2.05, height=.6)
        self.takeaway('Trace costs add; Frobenius squares add; the operator norm takes the maximum.')


class Sn08Restrictions(NormSlide):
    example = True
    stage = 2

    def body(self):
        self.start()
        self.put(stack(r'T=\begin{pmatrix}1&1\\0&0\end{pmatrix}',
                       r'Te_1=Te_2=e_1',
                       tex('Orthogonal inputs, the same output direction.', size=27),
                       size=34, buff=.4), 'left', y=.6, height=3)
        a, b, out = np.array([1.7, .6, 0]), np.array([1.7, -.6, 0]), np.array([4.6, 0, 0])
        self.add(Dot(a, color=TRIAL), Dot(b, color=TRIAL), Dot(out, color=WANTED),
                 math('e_1', size=27).next_to(a, UP), math('e_2', size=27).next_to(b, DOWN),
                 math('e_1', size=27).next_to(out, RIGHT))
        self.play(Create(Arrow(a, out, buff=.1, color=TRIAL)),
                  Create(Arrow(b, out, buff=.1, color=TRIAL)), run_time=1)
        self.beat()
        singular = np.linalg.svd(overlapping_restrictions(), compute_uv=False)
        self.add(math(r'\|T|_{\mathbb R e_1}\|_1+\|T|_{\mathbb R e_2}\|_1=2',
                      size=30).move_to([0, -1.25, 0]),
                 boxed(math(rf'\|T\|_1=\sqrt2\approx{singular.sum():.4f}<2', size=33), color=CURRENT).move_to([0, -2.0, 0]))
        self.takeaway('Domain restrictions are independent blocks only when their output pieces separate too.')


class Sn09Recap(NormSlide):
    stage = 3

    def body(self):
        self.start()
        self.put(stack(tex('Singular values: coordinate-independent stretches.', size=30),
                       tex('A norm chooses how those stretches contribute.', size=30),
                       tex('Trace and power costs add on orthogonal blocks.', size=30),
                       tex('Overlapping images can break a proposed sum.', size=30), buff=.38),
                 y=.8, height=2.8)
        self.add(math(r'\text{Check: }s(T)=(3,4).\quad\|T\|_{\mathrm{op}}=?,\ \|T\|_F=?,\ \|T\|_1=?',
                      size=28).move_to([0, -1.15, 0]))
        self.beat()
        self.add(math(r'\|T\|_{\mathrm{op}}=4,\qquad\|T\|_F=5,\qquad\|T\|_1=7',
                      size=31, color=CURRENT).move_to([0, -1.9, 0]))
        self.takeaway('Next: construct motions that respect the constraints, then differentiate their cost.')


class SnFacts(NormSlide):
    stage = 3

    def body(self):
        self.start()
        self.put(stack(
            tex(r'Real finite-dimensional $E$; $A:E\to E$; $1\le p<\infty$.', size=27),
            r'\boxed{N_p(A)=\left(\sum_j s_j(A)^p\right)^{1/p}}',
            tex(r'$p=1$: add stretches. $p=2$: square, add, take the square root.', size=25),
            tex(r'For orthogonal coordinate changes $U,V$:', size=27),
            r'\boxed{s(UAV)=s(A)}',
            tex('The same stretches give the same cost in every orthonormal coordinate system.', size=25),
            size=34, buff=.32), y=.2, height=4.0)
        self.takeaway('Compute in convenient coordinates; the singular values and their Schatten cost do not change.')


class SnLean(LessonLean):
    lesson_deck = 'prereq-singular-norms'
    lecture_id = 'singular_norms'
    symbolic_facts = (
        ('Finite Schatten norm', r'N_p(A)=\left(\sum_j s_j(A)^p\right)^{1/p}'),
        ('Orthogonal coordinates', r's(UAV)=s(A)'),
    )
    ownership = 'Tau Ceti: Schatten seminorms and singular-value invariance.'
    notation = r'$\to_\ell$ means linear map; $\simeq_\ell^i$ means isometric isomorphism; $\circ_\ell$ is composition.'


class SnComputation(NormSlide):
    stage = 3

    def body(self):
        self.start()
        self.put(stack(
            r'T=U\Sigma V^T\quad\Longrightarrow\quad(s_j(T))_j=\operatorname{diag}\Sigma',
            tex(r'Dense matrices: LAPACK SVD, exposed by \texttt{scipy.linalg.svd}.', size=28),
            tex('The default dense driver uses divide and conquer.', size=27),
            boxed(math(r'N_p(T)=\|(s_j(T))_j\|_{\ell^p}', size=34), color=CURRENT),
            tex(r'Large sparse matrices: partial SVD, e.g.\ \texttt{scipy.sparse.linalg.svds}.', size=26),
            tex('A few leading singular values do not determine the full trace norm.', size=27),
            buff=.34), y=.45, height=3.5)
        self.source('SciPy: scipy.linalg.svd (gesdd); scipy.sparse.linalg.svds.')
        self.takeaway('Choose whether you need the whole singular-value list or only its leading part.')
