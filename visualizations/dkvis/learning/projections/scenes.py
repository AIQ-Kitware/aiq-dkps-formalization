"""Nearest points, projection coordinates, and subspace transport."""
import numpy as np
from manim import Arrow, Create, DashedLine, Dot, DOWN, Indicate, Line, RIGHT, Rotate, Transform, UP, VGroup

from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.learning.projections.model import plane_frame, projection_example
from dkvis.slide_style import CURRENT, FAINT, FG, GAP, MUTED, RESID, TRIAL, WANTED, boxed, math, tex


class PrTitle(LessonTitle):
    lesson_deck = 'prereq-projections'
    title_lines = ('Subspaces and projections',)
    subtitle = 'From nearest points to subspace coordinates.'


class ProjectionSlide(LessonSlide):
    lesson_deck = 'prereq-projections'


def projection_picture():
    x, p, fitted, error = projection_example()
    ax = plane()
    line = Line(ax.c2p(-3.3, 0), ax.c2p(3.3, 0), color=TRIAL, stroke_width=4)
    whole = vector(ax, x)
    projected = vector(ax, fitted, TRIAL)
    residual = Arrow(ax.c2p(*fitted), ax.c2p(*x), color=RESID, buff=0)
    group = VGroup(ax, line, whole,
                   math('K', color=TRIAL, size=28).next_to(line, DOWN),
                   math('x', size=28).next_to(whole.get_end(), UP))
    return group, ax, projected, residual


class Pr00Question(ProjectionSlide):
    example = True
    def body(self):
        self.start()
        picture, ax, projected, residual = projection_picture()
        picture.add(projected, residual)
        self.put(picture, 'left', y=.1)
        self.add(math('Px', size=25, color=TRIAL).next_to(projected, DOWN, buff=.18),
                 math(r'(I-P)x', size=24, color=RESID).next_to(residual, RIGHT, buff=.15))
        self.put(stack(
            tex('A vector near a line', size=31),
            r'\min_{z\in K}\|x-z\|^2',
            tex('Which part belongs to the space?', size=27),
            tex('What changes when we choose another basis?', size=25),
            tex('How can a matrix describe the whole space?', size=25),
            buff=.42), 'right', y=.1)
        self.takeaway('A projection turns the geometry of a subspace into an operator we can calculate with.')


class Pr01History(ProjectionSlide):
    def body(self):
        self.start()
        self.put(stack(
            tex('1937: Gale Young, subspace fitting', size=34, color=CURRENT),
            tex('Choose a space that fits a cloud of measured points.', size=29),
            r'\min_{\dim K=r}\sum_j\|x_j-P_Kx_j\|^2',
            tex('For a fixed space: fitted component + perpendicular error.', size=28),
            tex('Our use: describe and transport the space itself.', size=28),
            buff=.42), y=.35, height=3.3)
        self.source('Young (1937), Matrix Approximations and Subspace Fitting. DOI: 10.1007/BF02287962')
        self.takeaway('Nearest-point geometry connects fitting data with reasoning about subspaces.')


class Pr02Decomposition(ProjectionSlide):
    example = True
    stage = 1

    def body(self):
        self.start()
        picture, ax, projected, residual = projection_picture()
        self.put(picture, 'left', y=.15)
        # Build arrows after positioning the coordinate system.
        x, p, fitted, error = projection_example()
        projected = vector(ax, fitted, TRIAL)
        residual = Arrow(ax.c2p(*fitted), ax.c2p(*x), color=RESID, buff=0)
        self.play(Create(projected), Create(residual), run_time=1)
        self.add(math('Px', size=25, color=TRIAL).next_to(projected, DOWN, buff=.18),
                 math(r'(I-P)x', size=24, color=RESID).next_to(residual, RIGHT, buff=.15))
        self.put(stack(r'x=Px+(I-P)x', r'Px\in K,\quad (I-P)x\in K^\perp',
                       r'\langle Px,(I-P)x\rangle=0', buff=.42), 'right', y=.85, height=2.2)
        self.beat()
        z = np.array([-.8, 0.])
        self.add(Dot(ax.c2p(*z), color=GAP),
                 math('z', size=25, color=GAP).next_to(ax.c2p(*z), DOWN),
                 DashedLine(ax.c2p(*z), ax.c2p(*x), color=GAP))
        self.put(stack(r'\|x-z\|^2=\|(I-P)x\|^2+\|Px-z\|^2',
                       r'\|x-z\|^2\ge\|(I-P)x\|^2', size=27, buff=.35),
                 'right', y=-1.30, height=1.2)
        self.takeaway('The perpendicular error is unavoidable; every other choice adds a nonnegative term.')


class Pr03Projector(ProjectionSlide):
    example = True
    stage = 1

    def body(self):
        self.start()
        picture, ax, projected, residual = projection_picture()
        self.put(picture, 'left', y=.25)
        arrow = vector(ax, [2, 1.2], color=WANTED)
        self.add(arrow)
        self.put(stack(r'P=\begin{pmatrix}1&0\\0&0\end{pmatrix}',
                       r'P(x_1,x_2)=(x_1,0)', r'P(Px)=Px', size=32, buff=.4),
                 'right', y=.75, height=2.8)
        self.play(Transform(arrow, vector(ax, [2, 0], WANTED)), run_time=1)
        self.add(math('Px', size=25, color=WANTED).next_to(arrow, DOWN, buff=.18))
        self.beat()
        self.play(Indicate(arrow), run_time=.6)
        self.put(stack(boxed(math(r'P^2=P,\qquad P^T=P', size=28), color=CURRENT),
                       r'\operatorname{range}P=K,\quad\ker P=K^\perp',
                       r'P^\perp:=I-P', size=28, buff=.3), 'right', y=-1.2, height=1.6)
        self.takeaway('Idempotence keeps projected vectors fixed; symmetry makes the projection orthogonal.')


class Pr04Frames(ProjectionSlide):
    example = True
    stage = 1

    def body(self):
        self.start()
        ax = plane(extent=1.5)
        frame = plane_frame()
        a, b = vector(ax, frame[:2, 0], TRIAL), vector(ax, frame[:2, 1], TRIAL)
        picture = VGroup(ax, a, b,
                         tex(r'Inside the fixed $xy$-plane in $\mathbb R^3$', size=25).next_to(ax, DOWN))
        self.put(picture, 'left', y=.15)
        self.put(stack(r'E^TE=I,\qquad \operatorname{range}E=K',
                       r'P=EE^T=\operatorname{diag}(1,1,0)',
                       r'\text{new frame }\widetilde E=EC,\quad C^TC=I',
                       size=29, buff=.45), 'right', y=.65, height=2.7)
        self.beat()
        rotated = plane_frame(.85)
        angle = float(np.arctan2(rotated[1, 0], rotated[0, 0]))
        self.play(Rotate(a, angle=angle, about_point=ax.c2p(0, 0)),
                  Rotate(b, angle=angle, about_point=ax.c2p(0, 0)), run_time=1.3)
        self.put(stack(boxed(math(r'\widetilde E\widetilde E^T=ECC^TE^T=EE^T=P', size=25), color=CURRENT),
                       tex('Basis vectors moved. The subspace stayed fixed.', size=25), size=27),
                 'right', y=-1.35, height=1.1)
        self.takeaway('A frame is a choice of coordinates; the projector describes the underlying space.')


class Pr05Blocks(ProjectionSlide):
    stage = 1

    def body(self):
        self.start()
        self.put(stack(r'x=\binom{x_K}{x_\perp}',
                       r'T=\begin{pmatrix}T_{00}&T_{01}\\T_{10}&T_{11}\end{pmatrix}',
                       r'\mathbb R^n=K\oplus K^\perp', size=36, buff=.4), 'left')
        self.put(stack(tex('Input selects a column.', size=30),
                       tex('Output component selects a row.', size=30),
                       tex(r'$T_{10}$: source input to complementary output.', size=26),
                       tex(r'$T_{01}$: complementary input to source output.', size=26),
                       buff=.4), 'right', y=.4, height=3.0)
        self.beat()
        self.add(math(r'Tx=\binom{T_{00}x_K+T_{01}x_\perp}{T_{10}x_K+T_{11}x_\perp}',
                      size=30).move_to([3.25, -1.65, 0]))
        self.takeaway('Off-diagonal blocks record transfer between spaces. Writing blocks does not make them zero.')


class Pr06Commutation(ProjectionSlide):
    stage = 2

    def body(self):
        self.start()
        self.put(stack(r'P=\begin{pmatrix}I&0\\0&0\end{pmatrix}',
                       r'PT=\begin{pmatrix}T_{00}&T_{01}\\0&0\end{pmatrix}',
                       r'TP=\begin{pmatrix}T_{00}&0\\T_{10}&0\end{pmatrix}',
                       size=32, buff=.35), 'left')
        self.put(stack(r'PT=TP', r'\Longrightarrow\quad T_{01}=T_{10}=0',
                       tex('Preserve the source and its complement.', size=27),
                       size=32, buff=.4), 'right', y=.65, height=2.3)
        self.beat()
        self.put(stack(boxed(math(r'T=\begin{pmatrix}T_{00}&0\\0&T_{11}\end{pmatrix}', size=31), color=CURRENT),
                       tex('Each diagonal block may still act nontrivially.', size=25), buff=.3),
                 'right', y=-1.2, height=1.7)
        self.takeaway('Commuting with a projector means no component crosses its orthogonal decomposition.')


class Pr07Transport(ProjectionSlide):
    example = True
    stage = 2

    def body(self):
        self.start()
        ax = plane(extent=1.5)
        source = Line(ax.c2p(-1.3, 0), ax.c2p(1.3, 0), color=TRIAL, stroke_width=5)
        target = source.copy().set_color(WANTED)
        self.put(VGroup(ax, source, target), 'left', y=.1)
        self.put(stack(r'P=P_K,\quad Q=P_L,\quad W^TW=I',
                       r'W(K)=L\quad\Longleftrightarrow\quad Q=WPW^T',
                       tex('Conjugation transports the projection.', size=27),
                       size=30, buff=.45), 'right', y=.6, height=2.5)
        self.beat()
        theta = .7
        self.play(Rotate(target, angle=theta, about_point=ax.c2p(0, 0)), run_time=1.2)
        self.put(stack(boxed(math(r'QW=WP', size=37), color=CURRENT),
                       tex('Project before or after transport: same result.', size=24)),
                 'right', y=-1.3, height=1.4)
        self.takeaway('The transporter constraint is an operator equation that a feasible curve must preserve.')


class Pr08Recap(ProjectionSlide):
    stage = 3

    def body(self):
        self.start()
        self.put(stack(r'P=EE^T\quad\text{describes }K\text{ independently of its basis}',
                       r'PT=TP\quad\text{means preserve }K\text{ and }K^\perp',
                       r'Q=WPW^T\quad\text{means }W(K)=L\text{ for orthogonal }W',
                       size=29, buff=.43), y=.9, height=2.3)
        self.add(tex(r'Check: $P=\operatorname{diag}(1,0,0)$, $T=\operatorname{diag}(1,R_t)$. Does $PT=TP$?',
                     size=28).move_to([0, -.95, 0]))
        self.beat()
        self.add(tex('Yes: T rotates within the complement and never mixes the two pieces.',
                     size=28, color=CURRENT).move_to([0, -1.75, 0]))
        self.takeaway('Next: singular values measure how much an operator moves vectors.')


class PrFacts(ProjectionSlide):
    stage = 3

    def body(self):
        self.start()
        self.put(stack(
            tex(r'$P=P_K$, $P^\perp=P_{K^\perp}$; orthogonal projections on a real Hilbert space.', size=27),
            r'\boxed{Px+P^\perp x=x}',
            tex('Split any vector into its two perpendicular components.', size=25),
            r'T_{\mathrm{off}}=PTP^\perp+P^\perp TP',
            r'\boxed{T_{\mathrm{off}}=0\ \Longleftrightarrow\ PT=TP}',
            tex('Commutation is exactly the absence of transfer between the two spaces.', size=25),
            size=32, buff=.28), y=.2, height=4.0)
        self.takeaway('Use the first identity to split a calculation; use the second to certify block structure.')


class PrLean(LessonLean):
    lesson_deck = 'prereq-projections'
    lecture_id = 'projections'
    symbolic_facts = (
        ('Projection split', r'Px+P^\perp x=x'),
        ('Block criterion', r'T_{\mathrm{off}}=0\ \Longleftrightarrow\ PT=TP'),
    )
    ownership = 'Mathlib: projection splitting. Tau Ceti: off-diagonal block criterion.'
    notation = r'\texttt{starProjection} is $P_K$; \texttt{Commute P T} means $PT=TP$.'
