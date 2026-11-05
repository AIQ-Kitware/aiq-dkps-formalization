"""I minus P as a complementary projection and a geometric error extractor."""
import numpy as np
from manim import Arrow, Axes, Dot, VGroup, VMobject, ValueTracker, always_redraw, linear
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, stack, vector
from dkvis.learning.complementary_projection.model import line_error, rotation_displacement
from dkvis.slide_style import CURRENT, MUTED, SINE, TRIAL, WANTED, boxed, math, tex


class ComplementSlide(LessonSlide):
    lesson_deck='prereq-complementary-projection'


def projection_plane(scene):
    axes=Axes(x_range=[-.2,1.3,.5],y_range=[-.2,1.3,.5],
              x_length=4.0,y_length=4.0,tips=False,
              axis_config={'color':MUTED,'include_ticks':False})
    labels=VGroup(math('K',size=25,color=WANTED).move_to(axes.c2p(1.2,-.12)),
                  math(r'K^\perp',size=24,color=SINE).move_to(axes.c2p(-.09,1.22)))
    scene.put(VGroup(axes,labels),'left',y=.2,height=3.9)
    return axes


def geometry(axes, angle):
    _,v,fitted,error=line_error(angle)
    square=VMobject(color=MUTED,stroke_width=2).set_points_as_corners([
        axes.c2p(fitted[0]-.07,0),axes.c2p(fitted[0]-.07,.07),axes.c2p(fitted[0],.07)])
    return VGroup(square,vector(axes,v,TRIAL),vector(axes,fitted,WANTED),
        Arrow(axes.c2p(*fitted),axes.c2p(*v),buff=0,color=SINE,stroke_width=5),
        Dot(axes.c2p(*fitted),radius=.04,color=WANTED))


class CpTitle(LessonTitle):
    lesson_deck='prereq-complementary-projection'
    title_lines=('Thinking about I minus P',)
    subtitle='What remains after the projected component is removed?'


class CpQuestion(ComplementSlide):
    def body(self):
        self.start()
        self.put(stack(tex('A classical least-squares question:',size=31),
            tex('How much of a vector lies outside the subspace used to approximate it?',size=29),
            r'x=Px+(x-Px)',
            boxed(math(r'(I-P)x=x-Px',size=40),color=CURRENT),
            tex('Subtract outputs on the same input; do not subtract subspaces.',size=28),buff=.42),y=.4,height=3.7)
        self.takeaway('Read I minus P as an operation on a vector before thinking of it as a matrix.')


class CpSplit(ComplementSlide):
    example=True
    stage=1
    def body(self):
        self.start()
        axes=projection_plane(self)
        self.add(geometry(axes,.65))
        self.put(stack(r'K=\operatorname{span}(e_1),\qquad P=\begin{pmatrix}1&0\\0&0\end{pmatrix}',
            r'v=\begin{pmatrix}\cos\theta\\\sin\theta\end{pmatrix},\quad Pv=\begin{pmatrix}\cos\theta\\0\end{pmatrix}',
            tex('Amber: original vector. Blue: projected component.',size=25),size=30,buff=.43),'right',y=.75,height=2.5)
        self.beat()
        self.put(stack(boxed(math(r'e=v-Pv=\begin{pmatrix}0\\\sin\theta\end{pmatrix}',size=33),color=SINE),
            tex('Pink points from the projected tip back to the original tip.',size=24),buff=.25),'right',y=-1.3,height=1.5)
        self.takeaway('The error vector and its translated copy have the same direction and length.')


class CpKeep(ComplementSlide):
    stage=1
    def body(self):
        self.start()
        self.put(stack(r'x=k+z,\qquad k\in K,\quad z\in K^\perp',
            r'Px=k,\qquad(I-P)x=z',
            boxed(math(r'(I-P)k=0,\qquad(I-P)z=z',size=35),color=CURRENT),
            r'(I-P)^2=I-P,\qquad P(I-P)=0',
            tex('It removes the chosen subspace and keeps the perpendicular part unchanged.',size=28),buff=.4),y=.4,height=3.7)
        self.takeaway('I minus P is itself the orthogonal projection onto the complementary subspace.')


class CpAngle(ComplementSlide):
    example=True
    stage=1
    def body(self):
        self.start()
        axes=projection_plane(self)
        angle=ValueTracker(.8)
        self.add(always_redraw(lambda:geometry(axes,angle.get_value())))
        self.put(stack(r'\|v\|=1,\qquad\angle(v,K)=\theta',
            boxed(math(r'\|(I-P)v\|=\sin\theta',size=35),color=SINE),
            r'\|v\|^2=\|Pv\|^2+\|(I-P)v\|^2',
            tex('The right triangle measures the distance to the subspace.',size=26),size=28,buff=.45),'right',y=.35,height=3.2)
        self.beat();self.play(angle.animate.set_value(.12),run_time=3,rate_func=linear)
        self.takeaway('For a unit vector, the norm of the perpendicular component is the sine of its angle to K.')


class CpRestricted(ComplementSlide):
    stage=2
    def body(self):
        self.start()
        self.put(stack(tex('Why can the error be small if the operator has norm one?',size=31),
            r'\|I-P\|_{\rm op}=1\quad\text{when }K^\perp\ne\{0\}',
            tex('That norm tests all unit vectors, including vectors entirely outside K.',size=28),
            r'E_0:a\longmapsto\text{a trial vector with coordinates }a,\qquad E_0^TE_0=I',
            boxed(math(r'\|(I-P)E_0\|_{\rm op}=\sup_{\|a\|=1}\|(I-P)E_0a\|',size=29),color=CURRENT),
            tex('This tests only the trial subspace. For one trial line, its value is sin theta.',size=27),buff=.34),y=.4,height=3.8)
        self.takeaway('Subspace accuracy comes from restricting the inputs, not from making I minus P small everywhere.')


class CpSineBlock(ComplementSlide):
    stage=2
    def body(self):
        self.start()
        self.put(stack(r'P=F_0F_0^T,\qquad I-P=F_1F_1^T,\qquad F_1^TF_1=I',
            tex('F zero spans the wanted space; F one spans its orthogonal complement.',size=27),
            boxed(math(r'S=(I-P)E_0=F_1X,\qquad X=F_1^TE_0',size=32),color=SINE),
            r'\|Sa\|=\|Xa\|,\qquad\|S\|_{\rm op}=\|X\|_{\rm op}',
            tex('S is the error in ambient coordinates; X records it in unwanted coordinates.',size=27),
            tex(r'The operator residual $R=\widehat A E_0-E_0A_0$ is a different map.',size=26),buff=.34),y=.4,height=3.8)
        self.takeaway('The sine block applies the complementary projection to trial vectors, then may change coordinates.')


class CpDisplacement(ComplementSlide):
    example=True
    stage=2
    def body(self):
        self.start()
        theta=.8
        axes=projection_plane(self)
        _,v,fitted,error=line_error(theta)
        _,u,_,d=rotation_displacement(theta)
        self.add(geometry(axes,theta),Dot(axes.c2p(*u),color=CURRENT),
            Arrow(axes.c2p(*v),axes.c2p(*u),buff=0,color=CURRENT,stroke_width=5))
        self.put(stack(r'v=Wu,\quad\|u\|=\|v\|=1,\quad W=\text{rotation by }\theta',
            boxed(math(r'e(v)=v-Pv,\qquad\|e(v)\|=\sin\theta',size=29),color=SINE),
            boxed(math(r'd(u)=u-Wu,\qquad\|d(u)\|=2\sin(\theta/2)',size=29),color=CURRENT),
            tex('P drops a component. W preserves lengths while moving vectors.',size=26),size=26,buff=.4),'right',y=.35,height=3.5)
        self.takeaway('I minus P is also the displacement of P in the original-minus-output convention; P is not a rotation.')


class CpSummary(ComplementSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(r'(I-P)x=x-Px\in K^\perp',
            tex('The actual move from x to Px has the opposite sign: Px minus x.',size=28),
            tex('Orthogonality makes I minus P a complementary projection and a distance extractor.',size=27),
            tex('Restrict its input to a trial subspace to measure subspace error.',size=28),
            tex('I minus W measures displacement for a general map W; it need not be a projection.',size=27),buff=.4),y=.4,height=3.6)
        self.takeaway('Same subtraction pattern, with additional geometric structure when the map is an orthogonal projection.')


class CpFacts(ComplementSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('P is the orthogonal projection onto K.',size=30),
            boxed(math(r'P_{K^\perp}=I-P_K',size=38),color=CURRENT),
            boxed(math(r'x-P_Kx\in K^\perp',size=38),color=SINE),
            tex('Orthogonality is essential: an arbitrary idempotent need not project onto the perpendicular complement.',size=27),buff=.5),y=.4,height=3.5)
        self.takeaway('These are the two projection facts recorded on the following Lean cards.')


class CpLeanOperator(LessonLean):
    lesson_deck='prereq-complementary-projection'
    lecture_id='complementary_projection'
    assumptions=r'Real inner product space $E$; $K$ admits an orthogonal projection.'
    symbolic_facts=(('Complementary projection',r'P_{K^\perp}=I-P_K'),
                    ('Perpendicular error',r'x-P_Kx\in K^\perp'))
    ownership='Mathlib: orthogonal complement projection and projection error.'
    notation=r'\texttt{starProjection} is the ambient orthogonal projection; \texttt{id} is the identity map.'


class CpLeanError(CpLeanOperator):
    fact_index=1


class CpComputation(ComplementSlide):
    bonus=True
    def body(self):
        self.start()
        self.put(stack(r'Q^TQ=I,\qquad P=QQ^T',
            boxed(math(r'e=x-Q(Q^Tx)',size=38),color=CURRENT),
            tex('Apply the frame and its transpose; avoid storing a dense identity-minus-projector matrix.',size=27),
            r'e=Q_\perp(Q_\perp^Tx)\quad\text{if a complementary frame is available}',
            tex('Full QR supplies complementary columns; economy QR supplies only the fitted-space frame.',size=26),
            tex('Very small errors need care with cancellation and floating-point precision.',size=27),buff=.36),y=.4,height=3.7)
        self.source('SciPy QR documentation: full and economic modes; LAPACK Householder QR.')
        self.takeaway('The numerical bonus concerns how to compute the same geometric error, not a different definition.')
