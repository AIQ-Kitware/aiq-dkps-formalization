"""Matrix exponentials: definition, constant flow, and exact feasible motions."""
import numpy as np
from manim import (
    Arc, Circle, Create, DOWN, Line, ParametricFunction, Polygon, RIGHT,
    Rotate, Transform, ValueTracker, VGroup, VMobject, always_redraw,
)
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.learning.matrix_exponential.model import euler_path, noncommuting_generators, shear_generator, taylor_exponential
from dkvis.slide_style import CURRENT, FAINT, GAP, MUTED, RESID, TRIAL, WANTED, boxed, math, tex


class ExTitle(LessonTitle):
    lesson_deck = 'prereq-matrix-exponential'
    title_lines = ('The exponential of a matrix',)
    subtitle = 'From a velocity rule to an exact motion.'


class ExponentialSlide(LessonSlide):
    lesson_deck = 'prereq-matrix-exponential'


def circle_picture():
    ax = plane(extent=1.8)
    radius = np.linalg.norm(ax.c2p(1, 0)-ax.c2p(0, 0))
    return ax, Circle(radius=radius, color=FAINT).move_to(ax.c2p(0, 0))


class Ex00Question(ExponentialSlide):
    def body(self):
        self.start()
        self.put(stack(tex('Scalar growth', size=33, color=TRIAL),
                       r'x\prime(t)=a x(t)', r'x(t)=e^{ta}x(0)', buff=.45), 'left')
        self.put(stack(tex('Coupled coordinates', size=33, color=WANTED),
                       r'x\prime(t)=Ax(t)',
                       boxed(math(r'x(t)=\exp(tA)x(0)', size=35), color=CURRENT),
                       tex('A velocity rule becomes a complete motion.', size=25), buff=.45), 'right')
        self.takeaway('Our goal: turn a skew-symmetric velocity into an exact orthogonal curve.')


class Ex01History(ExponentialSlide):
    def body(self):
        self.start()
        self.put(stack(tex('1858: Cayley develops matrix algebra', size=32, color=CURRENT),
                       tex('Powers make sense; multiplication order matters.', size=29),
                       tex('2005: Higham revisits scaling and squaring', size=32, color=CURRENT),
                       tex('Computing an exponential accurately is a separate problem.', size=27),
                       tex('Here: understand the function and its exact identities.', size=28), buff=.4),
                 y=.35, height=3.4)
        self.source('Cayley (1858), DOI: 10.1098/rstl.1858.0002; Higham (2005), DOI: 10.1137/04061101X.')
        self.takeaway('A matrix function uses matrix multiplication, rather than applying a scalar rule to each entry.')


class Ex02Series(ExponentialSlide):
    stage = 1

    def body(self):
        self.start()
        self.put(stack(r'\exp(tA)=\sum_{k=0}^{\infty}\frac{t^kA^k}{k!}',
                       r'=I+tA+\frac{t^2A^2}{2!}+\frac{t^3A^3}{3!}+\cdots',
                       r'A^0=I,\qquad\exp(0_{2\times2})=I_2',
                       tex('Matrix powers, rather than entrywise exponentials.', size=26),
                       size=30, buff=.4), 'left')
        self.beat()
        self.put(stack(tex('Why the series converges', size=31),
                       r'\left\|\frac{t^kA^k}{k!}\right\|\le\frac{(|t|\|A\|)^k}{k!}',
                       r'\sum_{k=0}^{\infty}\frac{(|t|\|A\|)^k}{k!}=e^{|t|\|A\|}<\infty',
                       tex('Every finite square matrix; no inverse required.', size=25),
                       size=28, buff=.45), 'right')
        self.takeaway('Absolute convergence makes the exponential well-defined even for singular matrices.')


class Ex03SmallSteps(ExponentialSlide):
    stage = 1

    def body(self):
        self.start()
        ax, circle = circle_picture()
        self.put(VGroup(ax, circle), 'left', y=.15)
        j = np.array([[0., -1.], [1., 0.]])
        def path(steps, color):
            points = euler_path(j, np.pi/2, steps, [1, 0])
            return VMobject(color=color, stroke_width=3).set_points_as_corners([ax.c2p(*p) for p in points])
        coarse = path(4, GAP)
        self.add(coarse)
        self.put(stack(r'x_{k+1}=\left(I+\frac{t}{n}A\right)x_k',
                       r'x_n=\left(I+\frac{t}{n}A\right)^n x_0',
                       r'\left(I+\frac{t}{n}A\right)^n\longrightarrow e^{tA}',
                       size=30, buff=.5), 'right', y=.55, height=2.8)
        self.beat()
        self.play(Create(path(32, CURRENT)), run_time=1.2)
        radius = np.linalg.norm(ax.c2p(1, 0)-ax.c2p(0, 0))
        self.add(Arc(radius=radius, angle=np.pi/2, color=WANTED, stroke_width=3).move_arc_center_to(ax.c2p(0, 0)))
        self.put(stack(tex('Violet: 4 steps. Steel: 32 steps. Blue: exact arc.', size=24),
                       tex('Finite Euler steps drift outward; the limit rotates.', size=25)),
                 'right', y=-1.4, height=1.1)
        self.takeaway('Repeated local updates approach the exact flow; a finite approximation need not preserve its constraints.')


class Ex04Dynamics(ExponentialSlide):
    stage = 1

    def body(self):
        self.start()
        self.put(stack(r'X(t)=I+tA+\frac{t^2A^2}{2!}+\cdots',
                       r'X\prime(t)=A+tA^2+\frac{t^2A^3}{2!}+\cdots',
                       r'=AX(t)=X(t)A', size=31, buff=.5), y=.8, height=2.6)
        self.beat()
        self.add(boxed(math(r'x(t)=X(t)x_0\quad\Longrightarrow\quad x\prime(t)=Ax(t),\ x(0)=x_0',
                            size=30), color=CURRENT).move_to([0, -1.05, 0]),
                 tex(r'In particular: $X(0)=I$ and $X\prime(0)=A$.', size=29).move_to([0, -1.95, 0]))
        self.takeaway('The generator A gives the instantaneous velocity; the exponential gives the full time evolution.')


class Ex05Diagonal(ExponentialSlide):
    stage = 1

    def body(self):
        self.start()
        ax, circle = circle_picture()
        self.put(VGroup(ax, circle), 'left', y=.1)
        time = ValueTracker(0)
        curve = always_redraw(lambda: ParametricFunction(
            lambda a: ax.c2p(np.exp(.5*time.get_value())*np.cos(a), np.exp(-.3*time.get_value())*np.sin(a)),
            t_range=[0, 2*np.pi], color=WANTED))
        self.add(curve)
        self.put(stack(r'A=\operatorname{diag}(0.5,-0.3)',
                       r'e^{tA}=\operatorname{diag}(e^{0.5t},e^{-0.3t})',
                       tex('Horizontal growth, vertical decay.', size=28),
                       tex('The faint circle is the initial shape.', size=25),
                       size=30, buff=.45), 'right', y=.45, height=3.1)
        self.beat()
        self.play(time.animate.set_value(1.2), run_time=1.6)
        self.add(tex(r'$t=1.2$: invertible, with changed lengths.', size=27).move_to([3.25, -1.6, 0]))
        self.takeaway('Diagonalization is a useful special case; the power-series definition does not require it.')


class Ex06Shear(ExponentialSlide):
    stage = 1

    def body(self):
        self.start()
        ax = plane(extent=2)
        points = np.array([[-.8, -.8], [.8, -.8], [.8, .8], [-.8, .8]])
        square = Polygon(*(ax.c2p(*p) for p in points), color=TRIAL, fill_opacity=.07)
        self.put(VGroup(ax, square), 'left', y=.2)
        self.put(stack(r'N=\begin{pmatrix}0&1\\0&0\end{pmatrix},\qquad N^2=0',
                       r'e^{tN}=I+tN=\begin{pmatrix}1&t\\0&1\end{pmatrix}',
                       r'(x,y)\mapsto(x+ty,y)', size=31, buff=.5),
                 'right', y=.8, height=2.7)
        self.beat()
        transformed = (np.eye(2)+shear_generator()) @ points.T
        self.play(Transform(square, Polygon(*(ax.c2p(*p) for p in transformed.T),
                                            color=WANTED, fill_opacity=.07)), run_time=1.4)
        self.put(stack(r'(e^{tN})^{-1}=I-tN', tex('This linear formula is exact because the series stops.', size=24)),
                 'right', y=-1.4, height=1.1)
        self.takeaway('The generator can be singular while its exponential is always invertible.')


class Ex07Rotation(ExponentialSlide):
    stage = 1

    def body(self):
        self.start()
        ax, circle = circle_picture()
        arrow = vector(ax, [1, 0], WANTED)
        self.put(VGroup(ax, circle, arrow), 'left', y=.2)
        self.put(stack(r'J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad J^2=-I',
                       r'e^{tJ}=(\cos t)I+(\sin t)J',
                       r'=\begin{pmatrix}\cos t&-\sin t\\\sin t&\cos t\end{pmatrix}',
                       size=31, buff=.5), 'right', y=.5, height=3.2)
        self.beat()
        self.play(Rotate(arrow, angle=np.pi/2, about_point=ax.c2p(0, 0)), run_time=1.5)
        self.add(math(r'e^{tbJ}=R_{bt}\quad\text{(angular speed }b\text{)}', size=29).move_to([3.25, -1.6, 0]))
        self.takeaway('Even powers give cosine; odd powers give sine. A quarter-turn velocity generates rotation.')


class Ex08Laws(ExponentialSlide):
    stage = 2

    def body(self):
        self.start()
        self.put(stack(tex('One fixed generator, successive time intervals', size=31),
                       r'e^{sA}e^{tA}=e^{(s+t)A}',
                       r'e^{0A}=I', size=36, buff=.5), y=.85, height=2.5)
        self.beat()
        self.add(boxed(math(r'(e^{tA})^{-1}=e^{-tA}', size=35), color=CURRENT).move_to([-3.15, -1.05, 0]),
                 boxed(math(r'(e^{tA})^T=e^{tA^T}', size=35), color=CURRENT).move_to([3.15, -1.05, 0]),
                 tex('Negative time reverses the motion. Transpose passes through the series.', size=28).move_to([0, -1.95, 0]))
        self.takeaway('Powers of one generator commute, so the scalar time-addition law survives.')


class Ex09Noncommuting(ExponentialSlide):
    stage = 2

    def body(self):
        self.start()
        a, b = noncommuting_generators()
        result = taylor_exponential(a+b)
        self.put(stack(r'A=\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad B=\begin{pmatrix}0&0\\1&0\end{pmatrix}',
                       r'AB\ne BA', r'e^Ae^B=\begin{pmatrix}2&1\\1&1\end{pmatrix}',
                       size=31, buff=.45), 'left')
        self.beat()
        self.put(stack(r'(A+B)^2=I',
                       r'e^{A+B}=\alpha I+\beta(A+B)',
                       r'\alpha=\sum_{k\ge0}\frac1{(2k)!}',
                       r'\beta=\sum_{k\ge0}\frac1{(2k+1)!}',
                       rf'e^{{A+B}}\approx\begin{{pmatrix}}{result[0,0]:.3f}&{result[0,1]:.3f}\\{result[1,0]:.3f}&{result[1,1]:.3f}\end{{pmatrix}}',
                       size=28, buff=.35), 'right')
        self.takeaway('For different generators, commutation is a sufficient hypothesis for the addition rule.')


class Ex10Orthogonal(ExponentialSlide):
    stage = 2

    def body(self):
        self.start()
        self.put(stack(r'B^T=-B,\qquad V(t)=e^{tB}',
                       r'V(t)^T=e^{tB^T}=e^{-tB}=V(t)^{-1}',
                       boxed(math(r'V(t)^TV(t)=I\quad\text{for every real }t', size=33), color=CURRENT),
                       size=32, buff=.5), y=.8, height=2.7)
        self.beat()
        self.add(math(r'V(0)=I,\quad V\prime(0)=B,\quad\det V(t)=1', size=31).move_to([0, -1.1, 0]),
                 tex(r'For either sign of $\det W$: $\det(We^{tB})=\det W$.', size=29).move_to([0, -1.95, 0]))
        self.takeaway('The curve preserves orthogonality and stays in its determinant component; W remains unrestricted.')


class Ex11SourcePreservation(ExponentialSlide):
    stage = 2

    def body(self):
        self.start()
        self.put(stack(r'BP=PB\quad\Longrightarrow\quad B^kP=PB^k',
                       r'\left(\sum_{k=0}^{m}\frac{t^kB^k}{k!}\right)P'
                       r'=P\left(\sum_{k=0}^{m}\frac{t^kB^k}{k!}\right)',
                       r'e^{tB}P=Pe^{tB}', size=28, buff=.5), 'left')
        self.beat()
        self.put(stack(r'e^{tB}(K)=K',
                       r'W(K)=L\quad\Longrightarrow\quad We^{tB}(K)=L',
                       tex('Skew-symmetry preserves lengths.', size=26),
                       tex('Commutation preserves the source.', size=26),
                       size=30, buff=.4), 'right')
        self.takeaway('Each hypothesis has a job: together they construct the feasible curve needed for stationarity.')


class Ex12Recap(ExponentialSlide):
    stage = 3

    def body(self):
        self.start()
        self.put(stack(r'e^{tA}=\sum_{k\ge0}\frac{t^kA^k}{k!},\qquad\frac{d}{dt}e^{tA}=Ae^{tA}',
                       r'(e^{tA})^{-1}=e^{-tA}',
                       r'B^T=-B\ \Longrightarrow\ e^{tB}\text{ orthogonal}',
                       r'BP=PB\ \Longrightarrow\ e^{tB}(K)=K', size=30, buff=.4), y=.85, height=2.8)
        self.add(tex(r'Check: $e^{0_{2\times2}}$? Can $e^B$ be a reflection when $B^T=-B$?', size=28).move_to([0, -1.25, 0]))
        self.beat()
        self.add(tex(r'$I_2$. No reflection: $\det(e^B)=1$. Both signs of $\det W$ remain available.',
                     size=27, color=CURRENT).move_to([0, -1.98, 0]))
        self.takeaway('Next: compose the exact source motion with W and extract information from its first derivative.')


class ExFacts(ExponentialSlide):
    stage = 3

    def body(self):
        self.start()
        self.put(stack(
            tex(r'Bounded operators on a real Hilbert space; $s,t\in\mathbb R$.', size=27),
            r'\boxed{e^{(s+t)A}=e^{sA}e^{tA}}',
            tex('One constant velocity gives a flow that composes over time.', size=25),
            r'\boxed{B^*=-B\ \Longrightarrow\ (e^B)^*e^B=e^B(e^B)^*=I}',
            r'\boxed{BP=PB\ \Longrightarrow\ e^BP=Pe^B}',
            tex(r'Apply the last two facts to $tB$: lengths and the source decomposition are preserved.', size=25),
            size=32, buff=.3), y=.15, height=4.0)
        self.takeaway('Skew-adjointness preserves lengths; commutation preserves the selected decomposition.')


class ExLean(LessonLean):
    lesson_deck = 'prereq-matrix-exponential'
    lecture_id = 'matrix_exponential'
    ownership = 'Tau Ceti: exponential flow. Mathlib: skew-adjoint exponential and commutation.'
    notation = r'$\to_L$ means bounded linear map; $\bullet$ is scalar multiplication; real \texttt{unitary} means orthogonal.'
