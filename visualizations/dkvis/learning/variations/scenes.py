"""Construct feasible motions and derive the gradient-compression tests."""
import numpy as np
from manim import Arc, Arrow, Circle, Create, DashedLine, Dot, DOWN, Line, RIGHT, Rotate, Transform, UP, VGroup

from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.learning.matching.model import source_plane_wiggle
from dkvis.slide_style import CURRENT, FAINT, FG, GAP, MUTED, RESID, SINE, TRIAL, WANTED, boxed, math, tex


class VaTitle(LessonTitle):
    lesson_deck = 'prereq-variations'
    title_lines = ('Feasible variations', 'and stationarity')
    subtitle = 'Move within the constraints. Test what a minimum requires.'


class VariationSlide(LessonSlide):
    lesson_deck = 'prereq-variations'


def unit_circle():
    ax = plane(extent=1.6)
    circle = Circle(radius=np.linalg.norm(ax.c2p(1, 0)-ax.c2p(0, 0)), color=FAINT).move_to(ax.c2p(0, 0))
    return ax, circle


class Va00Question(VariationSlide):
    example = True
    def body(self):
        self.start()
        ax, circle = unit_circle()
        point = Dot(ax.c2p(0, -1), color=WANTED)
        self.put(VGroup(ax, circle, point), 'left', y=.25)
        self.add(Arrow(ax.c2p(0, -1), ax.c2p(0, -1.5), buff=0, color=GAP))
        self.put(stack(r'\min_{x^2+y^2=1}y',
                       tex('Moving down lowers height but leaves the circle.', size=27),
                       tex('Allowed motions must remain on the circle.', size=27),
                       size=35, buff=.5), 'right', y=.55, height=2.8)
        self.beat()
        self.play(Rotate(point, angle=.45, about_point=ax.c2p(0, 0)), run_time=.6)
        self.play(Rotate(point, angle=-.45, about_point=ax.c2p(0, 0)), run_time=.6)
        self.put(stack(r'W^TW=I,\qquad W(K)=L',
                       tex('For matrices: preserve both constraints.', size=25), size=31),
                 'right', y=-1.4, height=1.1)
        self.takeaway('At a constrained minimum, test motion within the feasible set.')


class Va01History(VariationSlide):
    def body(self):
        self.start()
        self.put(stack(tex('1744: Euler, calculus of variations', size=34, color=CURRENT),
                       tex('Optimize curves while respecting restrictions.', size=30),
                       tex(r'Allowed variation $\longrightarrow$ first derivative $\longrightarrow$ necessary condition', size=28),
                       tex('Here the objects are finite orthogonal matrices.', size=29),
                       tex('We derive the matrix constraints directly.', size=29), buff=.45),
                 y=.3, height=3.4)
        self.source('Euler (1744), Methodus inveniendi lineas curvas, E65.')
        self.takeaway('Variations reveal the structure of a minimizer before we know it explicitly.')


class Va02Velocity(VariationSlide):
    example = True
    stage = 1

    def body(self):
        self.start()
        ax, circle = unit_circle()
        self.put(VGroup(ax, circle), 'left', y=.2)
        self.add(vector(ax, [1, 0], TRIAL),
                 Arrow(ax.c2p(1, 0), ax.c2p(1, 1), buff=0, color=RESID),
                 math('x', size=28, color=TRIAL).next_to(ax.c2p(1, 0), DOWN),
                 math('Bx', size=28, color=RESID).next_to(ax.c2p(1, 1), UP))
        self.put(stack(r'V(0)=I,\qquad B=V\prime(0)',
                       r'V(t)^TV(t)=I',
                       r'0=B^TI+IB=B^T+B', size=31, buff=.45),
                 'right', y=.7, height=2.5)
        self.beat()
        self.put(stack(boxed(math(r'B^T=-B\quad\text{(skew-symmetric)}', size=28), color=CURRENT),
                       r'B=bJ,\qquad J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}',
                       size=29, buff=.3), 'right', y=-1.25, height=1.5)
        self.takeaway('Differentiate orthogonality to obtain a skew-symmetric velocity.')


class Va03Exponential(VariationSlide):
    example = True
    stage = 1

    def body(self):
        self.start()
        ax, circle = unit_circle()
        exact, approximate = Dot(ax.c2p(1, 0), color=WANTED), Dot(ax.c2p(1, 0), color=GAP)
        self.put(VGroup(ax, circle, exact, approximate), 'left', y=.2)
        self.add(DashedLine(ax.c2p(1, -.8), ax.c2p(1, 1.3), color=GAP))
        self.put(stack(r'B=\begin{pmatrix}0&-1\\1&0\end{pmatrix}',
                       r'(I+tB)e_1=(1,t),\qquad\|(1,t)\|^2=1+t^2',
                       r'\exp(tB)e_1=(\cos t,\sin t)', size=29, buff=.45),
                 'right', y=.65, height=2.8)
        self.play(Transform(approximate, Dot(ax.c2p(1, .9), color=GAP)),
                  Rotate(exact, angle=.9, about_point=ax.c2p(0, 0)), run_time=1.2)
        self.beat()
        self.put(stack(r'\exp(tB)^T=\exp(-tB)=\exp(tB)^{-1}',
                       boxed(math(r'\exp(tB)^T\exp(tB)=I', size=29), color=CURRENT), size=29, buff=.35),
                 'right', y=-1.3, height=1.3)
        self.takeaway('The exponential follows an exact orthogonal curve instead of just its tangent approximation.')


class Va04SourceMotion(VariationSlide):
    example = True
    stage = 1

    def body(self):
        self.start()
        ax = plane(extent=1.5)
        a, b = vector(ax, [1, 0], TRIAL), vector(ax, [0, 1], TRIAL)
        self.put(VGroup(ax, a, b,
                        tex(r'Within $K=\operatorname{span}(e_1,e_2)\subset\mathbb R^3$', size=25).next_to(ax, DOWN)),
                 'left', y=.1)
        self.put(stack(r'P=\operatorname{diag}(1,1,0)',
                       r'B=\begin{pmatrix}0&-1&0\\1&0&0\\0&0&0\end{pmatrix}',
                       r'PB=BP=B', size=31, buff=.4), 'right', y=.55, height=2.9)
        self.beat()
        _, motion = source_plane_wiggle(.8)
        angle = float(np.arctan2(motion[1, 0], motion[0, 0]))
        self.play(Rotate(a, angle=angle, about_point=ax.c2p(0, 0)),
                  Rotate(b, angle=angle, about_point=ax.c2p(0, 0)), run_time=1.3)
        self.put(stack(r'e^{tB}=\operatorname{diag}(R_t,1)',
                       r'e^{tB}(K)=K', size=29, buff=.3), 'right', y=-1.4, height=1.1)
        self.takeaway('Construct B with skew diagonal blocks; source preservation then follows.')


class Va05Feasible(VariationSlide):
    stage = 2

    def body(self):
        self.start()
        self.put(stack(r'K\ \xrightarrow{\ V(t)\ }\ K\ \xrightarrow{\ W\ }\ L',
                       r'V(t)=e^{tB},\qquad B^T=-B,\quad BP=PB',
                       r'(WV(t))(K)=W(V(t)(K))=W(K)=L', size=34, buff=.6),
                 y=.9, height=2.6)
        self.beat()
        self.add(boxed(math(r'W(t)=We^{tB}\quad\text{is a feasible curve through }W',
                            size=31), color=CURRENT).move_to([0, -1.0, 0]),
                 tex(r'The velocity $B$ preserves the source; $W$ still transports it to the target.',
                     size=27).move_to([0, -1.9, 0]))
        self.takeaway('Right composition changes the vector correspondence while keeping the whole image space fixed.')


class Va06Stationarity(VariationSlide):
    example = True
    stage = 2

    def body(self):
        self.start()
        ax = plane(width=4.7, height=3.0, extent=1.4)
        minimum = ax.plot(lambda t: -np.cos(t), x_range=[-2, 2, .025], color=CURRENT)
        self.put(VGroup(ax, minimum), 'left', y=.3)
        self.put(stack(r'h_B(t)=\Phi_p(We^{tB}),\qquad 1<p<2',
                       r'W\text{ minimizes }\Phi_p\text{ on the feasible set}',
                       r'\Longrightarrow\quad h_B\prime(0)=0',
                       tex('Use positive and negative parameter values.', size=25),
                       size=29, buff=.42), 'right', y=.5, height=3.1)
        self.add(math(r'\text{Circle minimum: }h(t)=-\cos t', size=25, color=CURRENT).move_to([-3.25, -1.6, 0]))
        self.beat()
        maximum = ax.plot(lambda t: np.cos(t), x_range=[-2, 2, .025], color=GAP)
        self.play(Create(maximum), run_time=1)
        self.add(math(r'\text{Circle maximum: }h(t)=\cos t', size=25, color=GAP).move_to([3.25, -1.6, 0]))
        self.takeaway('A differentiable local minimum has zero derivative; the converse need not hold.')


class Va07Gradient(VariationSlide):
    example = True
    stage = 2

    def body(self):
        self.start()
        self.put(stack(tex('Define G using every skew velocity B.', size=27),
                       r'D(B)=\left.\frac{d}{dt}\Phi_p(We^{tB})\right|_{t=0}',
                       r'\langle G,B\rangle_F=\operatorname{tr}(G^TB)',
                       boxed(math(r'G^T=-G\ \Longrightarrow\ D(B)=-\operatorname{tr}(GB)', size=25), color=CURRENT),
                       size=28, buff=.43), 'left', y=.2)
        self.beat()
        self.put(stack(tex('Check the sign on a rotation plane', size=28),
                       r'f_p(\varphi)=(2\sin(\varphi/2))^p',
                       r'B=bJ,\quad G=f_p\prime(\varphi)J,\quad J^2=-I_2',
                       r'\left.\frac{d}{dt}2f_p(\varphi+tb)\right|_0=2bf_p\prime(\varphi)',
                       r'-\operatorname{tr}(GB)=-bf_p\prime(\varphi)\operatorname{tr}(-I_2)',
                       r'=2bf_p\prime(\varphi)', size=26, buff=.3), 'right', y=.2)
        self.takeaway('The negative trace pairing is the Frobenius pairing on skew-symmetric matrices.')


class Va08Test(VariationSlide):
    stage = 2

    def body(self):
        self.start()
        self.put(stack(r'B=PGP', r'B^T=PG^TP=-PGP=-B', r'PB=BP=B',
                       tex('An explicitly admissible direction.', size=26), size=31, buff=.42),
                 'left', y=.6, height=3.1)
        self.beat()
        self.put(stack(r'0=-\operatorname{tr}(GPGP)',
                       r'=-\operatorname{tr}(PGPGP)',
                       r'=-\operatorname{tr}((PGP)^2)',
                       r'=\operatorname{tr}((PGP)^T(PGP))',
                       r'=\|PGP\|_F^2', size=29, buff=.29), 'right', y=.6, height=3.3)
        self.beat()
        self.add(boxed(math(r'PGP=0,\qquad P^\perp G P^\perp=0', size=33),
                       color=CURRENT).move_to([0, -1.95, 0]))
        self.takeaway('A vanishing squared norm forces an entire diagonal gradient block to vanish.')


class Va09Structure(VariationSlide):
    stage = 2

    def body(self):
        self.start()
        self.put(stack(r'G=\begin{pmatrix}0&G_{01}\\-G_{01}^T&0\end{pmatrix}',
                       tex('The diagonal gradient blocks vanish.', size=27),
                       tex('The transporter W may still mix principal planes.', size=25),
                       size=36, buff=.45), 'left', y=.1)
        self.beat()
        self.put(stack(r'J_{\mathrm{src}}=2P-I=\begin{pmatrix}I&0\\0&-I\end{pmatrix}',
                       boxed(math(r'J_{\mathrm{src}}GJ_{\mathrm{src}}=-G', size=33), color=CURRENT),
                       tex('Reflection reverses the remaining off-diagonal blocks.', size=25),
                       size=30, buff=.45), 'right', y=.1)
        self.takeaway('Stationarity forces zero diagonal gradient blocks in source coordinates.')


class Va10Recap(VariationSlide):
    stage = 3

    def body(self):
        self.start()
        self.put(stack(r'B^T=-B\ \Longrightarrow\ e^{tB}\text{ orthogonal}',
                       r'BP=PB\ \Longrightarrow\ e^{tB}(K)=K',
                       r'W(K)=L\ \Longrightarrow\ We^{tB}(K)=L',
                       r'\text{stationarity with }B=PGP\ \Longrightarrow\ PGP=0',
                       size=30, buff=.4), y=.8, height=2.8)
        self.add(tex(r'Check: must $WP=PW$? Is every stationary point a minimum?',
                     size=28).move_to([0, -1.2, 0]))
        self.beat()
        self.add(tex('Neither. We derived a necessary condition on the gradient at a chosen minimizer.',
                     size=27, color=CURRENT).move_to([0, -1.95, 0]))
        self.takeaway('Construct feasible motions, then test the derivative to extract structure.')


class VaFacts(VariationSlide):
    stage = 3

    def body(self):
        self.start()
        self.put(stack(
            tex(r'Along a feasible curve, put $\phi(t)=F(W(t))$. If $0$ is a local minimum:', size=26),
            r'\boxed{\phi\text{ differentiable at }0\ \Longrightarrow\ \phi\prime(0)=0}',
            tex(r'For a finite real matrix $C$:', size=27),
            r'\boxed{\operatorname{tr}(C^TC)=0\ \Longleftrightarrow\ C=0}',
            tex(r'In our test, $C=PGP$: stationarity and the trace identity give', size=26),
            r'0=\operatorname{tr}((PGP)^T(PGP))\quad\Longrightarrow\quad PGP=0',
            size=32, buff=.3), y=.15, height=4.0)
        self.takeaway('First show the curve is feasible; then turn a zero derivative into a zero squared norm.')


class VaLean(LessonLean):
    assumptions = '$f$ is a real scalar function. Local minimum and derivative hypotheses are shown in the code.'
    lesson_deck = 'prereq-variations'
    lecture_id = 'variations'
    symbolic_facts = (
        (r'Stationarity ($f=\phi$)', r'\begin{gathered}0\text{ local min},\ f\text{ differentiable}\\\Longrightarrow\ f\prime(0)=0\end{gathered}'),
        ('Zero trace square', r'\operatorname{tr}(C^TC)=0\ \Longleftrightarrow\ C=0'),
    )
    ownership = 'Mathlib: derivative at a local minimum; faithfulness of the matrix trace square.'
    notation = r'\texttt{HasDerivAt f d 0} means $f\prime(0)=d$; \texttt{IsLocalMin f 0} is a local minimum.'


class VaComputation(VariationSlide):
    bonus = True
    stage = 3

    def body(self):
        self.start()
        self.put(stack(
            tex('Numerical manifold optimization: choose a direction, then take a legal step.', size=27),
            r'W^TW=I,\quad W(K)=L,\quad B^T=-B,\quad BP=PB',
            boxed(math(r'W_{\mathrm{new}}=W\exp(\eta B)', size=36), color=CURRENT),
            tex(r'Choose $B$ from a gradient; choose the step size $\eta$ by a search.', size=28),
            tex('QR or polar retractions give alternative local updates.', size=27),
            tex('Apply them within the source blocks to preserve the transport constraint.', size=26),
            buff=.34), y=.45, height=3.5)
        self.source('Manopt / Pymanopt: orthogonal-group optimization; QR and polar retractions.')
        self.takeaway('A numerical stationary point still needs an optimality argument; stationarity alone is not global.')


class VaLeanTrace(VaLean):
    assumptions = r'$C$ is a real matrix indexed by a finite type $n$. This algebraic fact needs no differentiability.'
    fact_index = 1
