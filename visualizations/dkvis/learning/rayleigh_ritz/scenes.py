"""Rayleigh–Ritz as a restricted search, with a geometric residual explanation."""
import numpy as np
from manim import Axes, Arrow, Line, RightAngle, ValueTracker, VGroup, DecimalNumber, always_redraw, linear
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.learning.rayleigh_ritz.model import line_example
from dkvis.slide_style import CURRENT, TRIAL, RESID, MUTED, boxed, math, tex


class RitzSlide(LessonSlide):
    lesson_deck = 'operators-rayleigh-ritz'
    stage = 1

    def card(self, *items, size=32):
        return self.put(stack(*items, size=size, buff=.38), y=.35, height=3.6)


class RrTitle(LessonTitle):
    lesson_deck = 'operators-rayleigh-ritz'
    series_title = 'Spectral approximation foundations'
    title_lines = ('Rayleigh–Ritz', 'Trial spaces and residuals')
    subtitle = 'Choose a search space. Solve within it. Check the full error.'


class RrQuestion(RitzSlide):
    stage = 0
    def body(self):
        self.start()
        self.card(r'Au=\lambda u\quad\text{in }\mathbb R^n',
                  tex('Search among combinations of a smaller collection of directions.',size=29),
                  boxed(math(r'\text{choose}\ \longrightarrow\ \text{compress}\ \longrightarrow\ \text{solve}\ \longrightarrow\ \text{check}',size=30),color=CURRENT))
        self.beat(); self.takeaway('A small eigenproblem is affordable; the full residual tells us what it has left unsolved.')
        self.source('Rayleigh, The Theory of Sound (1877); Ritz, variational approximation (1909).')


class RrSpace(RitzSlide):
    stage = 0
    def body(self):
        self.start()
        self.card(r'\mathcal T=\operatorname{span}(q_1,\ldots,q_k)',
                  tex('Trial space: the candidate vectors we allow in our search.',size=30),
                  tex('Invariant space: applying A never leaves the space.',size=30),
                  tex('Wanted spectral space: the exact target we hope to approximate.',size=30))
        self.beat(); self.takeaway('Choosing the trial space establishes neither invariance nor closeness to a target.')


class RrFrame(RitzSlide):
    def body(self):
        self.start()
        self.card(r'Q\in\mathbb R^{n\times k},\quad Q^TQ=I_k,\quad\mathcal T=\operatorname{range}Q',
                  boxed(math(r'y\in\mathbb R^k\ \xrightarrow{\ Q\ }\ u=Qy\in\mathcal T,\qquad\|Qy\|=\|y\|',size=31),color=TRIAL),
                  r'v\in\mathbb R^n\ \xrightarrow{\ Q^T\ }\ Q^Tv\ \xrightarrow{\ Q\ }\ Pv,\quad P=QQ^T')
        self.beat(); self.takeaway('Q supplies coordinates; P projects ambient vectors. A different frame can span the same trial space.')


class RrCompress(RitzSlide):
    def body(self):
        self.start()
        self.card(r'y\ \xrightarrow{Q}\ Qy\ \xrightarrow{A}\ AQy\ \xrightarrow{Q^T}\ Q^TAQy',
                  boxed(math(r'B=Q^TAQ\in\mathbb R^{k\times k}',size=42),color=CURRENT),
                  r'QBy=PAQy')
        self.beat(); self.takeaway('Compression applies A and projects back; it is a restriction only when the trial space is invariant.')


class RrQuotient(RitzSlide):
    def body(self):
        self.start()
        self.card(r'\|y\|=1,\quad u=Qy\quad\Longrightarrow\quad\|u\|=1',
                  boxed(math(r'u^TAu=y^T(Q^TAQ)y=y^TBy',size=37),color=CURRENT),
                  r'B^T=Q^TA^TQ=B')
        self.beat(); self.takeaway('The small problem preserves every Rayleigh quotient on the trial space exactly.')


class RrSolve(RitzSlide):
    def body(self):
        self.start()
        self.card(r'By=\theta y,\quad\|y\|=1\quad\Longrightarrow\quad u=Qy,\quad\|u\|=1',
                  tex('Ritz value: theta. Ritz vector: the lifted vector u.',size=29),
                  r'PAu=\theta u\qquad\text{(projected equation)}')
        self.beat()
        self.put(boxed(math(r'r=Au-\theta u\qquad\text{(full residual)}',size=32),color=RESID),y=-1.55,height=.7)
        self.takeaway('The projected equation is exact. The full eigenpair equation still has to be checked.')


class RrGeometry(RitzSlide):
    example = True
    def body(self):
        self.start()
        axes=Axes(x_range=[-.3,2.7,1],y_range=[-.3,2.075,1],
                  x_length=4.8,y_length=3.8,tips=False,
                  axis_config={'color':MUTED,'include_ticks':False})
        self.put(axes,'left',y=.15)
        angle=ValueTracker(np.pi/6)
        def data():
            return line_example(angle.get_value())
        self.add(always_redraw(lambda:Line(axes.c2p(*(-.2*data()[1])),axes.c2p(*(2.3*data()[1])),color=MUTED)))
        self.add(always_redraw(lambda:vector(axes,data()[1],TRIAL)))
        self.add(always_redraw(lambda:vector(axes,data()[0]@data()[1],CURRENT)))
        self.add(always_redraw(lambda:vector(axes,data()[2]*data()[1],TRIAL)))
        self.add(always_redraw(lambda:Arrow(axes.c2p(*(data()[2]*data()[1])),axes.c2p(*(data()[0]@data()[1])),buff=0,color=RESID,stroke_width=6)))
        def perpendicular_mark():
            a,q,theta,r=data()
            foot=theta*q
            return RightAngle(Line(axes.c2p(*foot),axes.c2p(*(foot+.3*q))),
                              Line(axes.c2p(*foot),axes.c2p(*(a@q))),length=.14,color=RESID)
        self.add(always_redraw(perpendicular_mark))
        self.put(stack(r'A=\operatorname{diag}(1,4)',math(r'q,\ \theta q\quad\text{on the trial line}',size=28,color=TRIAL),
                       math(r'Aq\quad\text{true output}',size=29,color=CURRENT),
                       math(r'r=Aq-\theta q\quad\perp q',size=29,color=RESID),size=31),'right',y=.7,height=2.6)
        label=tex('Residual length:',size=25).move_to([2.5,-1.3,0])
        value=DecimalNumber(np.linalg.norm(data()[3]),num_decimal_places=3,font_size=30,color=RESID).move_to([4.4,-1.3,0])
        value.add_updater(lambda m:m.set_value(np.linalg.norm(data()[3])));self.add(label,value)
        self.beat(); self.play(angle.animate.set_value(np.pi/9),run_time=4,rate_func=linear)
        self.takeaway('The residual is the output discarded by projection; orthogonal error can still be large.')


class RrExample(RitzSlide):
    example = True
    def body(self):
        self.start()
        self.card(r'A=\begin{pmatrix}2&1&1\\1&2&-1\\1&-1&5\end{pmatrix},\quad Q=(e_1,e_2),\quad B=\begin{pmatrix}2&1\\1&2\end{pmatrix}',
                  r'u_+=\tfrac1{\sqrt2}(1,1,0)^T,\quad\theta_+=3,\quad r_+=0',
                  r'u_-=\tfrac1{\sqrt2}(1,-1,0)^T,\quad\theta_-=1,\quad r_-=\sqrt2\,e_3',size=31)
        self.beat(); self.takeaway('One Ritz vector can be exact while the trial space as a whole is not invariant.')


class RrBlock(RitzSlide):
    def body(self):
        self.start()
        self.card(r'[Q\ Q_\perp]^TA[Q\ Q_\perp]=\begin{pmatrix}B&C^T\\C&D\end{pmatrix}',
                  tex('First block column: output from an input in the trial space.',size=29),
                  math(r'B:\ \text{retained output}\qquad C:\ \text{escaping output}',size=31))
        self.beat()
        self.put(math(r'R=AQ-QB=Q_\perp C,\qquad\mathcal T\text{ invariant}\iff C=0',size=31),y=-1.55,height=.65)
        self.takeaway('The block C measures failure of invariance; the block form itself assumes no invariance.')


class RrOrthogonality(RitzSlide):
    def body(self):
        self.start()
        self.card(r'R=AQ-QB,\qquad B=Q^TAQ',
                  r'Q^TR=Q^TAQ-Q^TQB=B-B=0',
                  tex('Each residual column is perpendicular to every trial direction.',size=29))
        self.beat()
        self.put(boxed(math(r'R=(I-P)AQ,\qquad r=Ry',size=33),color=RESID),y=-1.55,height=.7)
        self.takeaway('Galerkin orthogonality says where the error lies, not that the error vanishes.')


class RrModel(RitzSlide):
    def body(self):
        self.start()
        self.card(r'AQ-QM=\underbrace{R}_{\text{outside }\mathcal T}+\underbrace{Q(B-M)}_{\text{inside }\mathcal T}',
                  tex('The two pieces are orthogonal column by column.',size=28),
                  r'\|AQ-QM\|_F^2=\|R\|_F^2+\|B-M\|_F^2')
        self.beat(); self.takeaway('B is the unique best small model in Frobenius norm for fixed Q; the trial space remains a choice.')


class RrQuality(RitzSlide):
    stage = 2
    def body(self):
        self.start()
        self.card(r'\|u\|=1,\quad u=\sum_jc_jv_j,\quad Av_j=\lambda_jv_j',
                  r'\|Au-\theta u\|^2=\sum_j|c_j|^2|\lambda_j-\theta|^2',
                  boxed(math(r'\min_j|\lambda_j-\theta|\le\|r\|',size=35),color=CURRENT))
        self.beat(); self.takeaway('A small residual locates some eigenvalue. An angle bound to a specified target also needs separation.')


class RrMinmax(RitzSlide):
    stage = 2
    def body(self):
        self.start()
        self.card(r'\lambda_{\min}(B)=\min_{u\in\mathcal T,\ \|u\|=1}u^TAu\ \ge\ \lambda_{\min}(A)',
                  r'\mathcal T_1\subseteq\mathcal T_2\quad\Longrightarrow\quad\lambda_{\min}(B_1)\ge\lambda_{\min}(B_2)',
                  tex('Larger search: smallest Ritz value moves down; largest moves up.',size=29))
        self.beat(); self.takeaway('Nested trial spaces give monotone extremal bounds, without an automatic convergence rate.')


class RrPaper(RitzSlide):
    stage = 2
    def body(self):
        self.start()
        self.card(r'Q\leftrightarrow E_0,\qquad\mathcal T=\operatorname{range}E_0',
                  r'R=\widehat A E_0-E_0A_0',
                  boxed(math(r'\text{Rayleigh--Ritz choice:}\quad A_0=E_0^*\widehat A E_0',size=32),color=CURRENT),
                  tex('A general trial residual may use a different small model A zero.',size=28))
        self.beat(); self.takeaway('For unbounded operators, trial vectors must lie in the domain; retain the theorem\'s analytic hypotheses.')


class RrSummary(RitzSlide):
    stage = 3
    def body(self):
        self.start()
        self.card(r'\mathcal T\ \xrightarrow{\ \text{frame }Q\ }\ B=Q^*AQ\ \xrightarrow{By=\theta y}\ u=Qy',
                  r'R=AQ-QB=(I-P)AQ,\qquad r=Ry',
                  tex('The projected equation is solved; the full residual is measured.',size=29),
                  tex('A target and spectral separation turn residual information into angle control.',size=27))
        self.beat(); self.takeaway('Trial space, compression, Ritz pair, and full residual are four distinct parts of the approximation.')


class RrFacts(RitzSlide):
    stage = 3
    def body(self):
        self.start()
        self.card(r'B=Q^*AQ',r'Q^*R=0\qquad(R=AQ-QB)',r'AQ-QM=R+Q(B-M)',
                  tex('Q is isometric. The algebra works for bounded operators on Hilbert spaces.',size=27))
        self.takeaway('These three identities correspond to the next three accepted Tau Ceti statements.')


class RrLean(LessonLean):
    lesson_deck = 'operators-rayleigh-ritz'
    lecture_id = 'rayleigh_ritz'
    assumptions = 'A is bounded on a real Hilbert space; X maps trial coordinates isometrically into it.'
    symbolic_facts = (('Compression',r'B=Q^*AQ'),('Residual orthogonality',r'Q^*R=0'),
                      ('Residual splitting',r'AQ-QM=R+Q(B-M)'))
    ownership = 'Accepted Tau Ceti: Compression and RayleighRitz; exact scope and ancestry in sources.md.'
    notation = r'\texttt{X} is $Q$; \texttt{compression} is $B$; \texttt{A.sylvester M X} is $AQ-QM$.'


class RrLeanOrthogonal(RrLean):
    fact_index = 1


class RrLeanSplit(RrLean):
    fact_index = 2


class RrComputation(RitzSlide):
    bonus = True
    stage = 3
    def body(self):
        self.start()
        self.card(r'\text{orthogonalize}\ \longrightarrow\ AQ\ \longrightarrow\ B=Q^*AQ\ \longrightarrow\ By=\theta y',
                  tex('QR supplies Q. Apply a sparse or implicit A to its columns.',size=28),
                  r'V\text{ not orthonormal:}\quad V^*AVy=\theta(V^*V)y',
                  tex('Krylov and subspace methods build and improve the trial spaces.',size=28))
        self.takeaway('Check orthogonality and the full lifted residual; a small reduced residual alone is insufficient.')
