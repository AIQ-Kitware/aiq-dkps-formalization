"""Spectral selection, strong additivity, scalar measures, and operator domains."""
import numpy as np
from manim import Axes, Dot, Line, Rectangle, Transform, VGroup, DOWN
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, stack
from dkvis.slide_style import CURRENT, TRIAL, WANTED, GAP, MUTED, boxed, math, tex
from dkvis.learning.pvm.model import atom_masses, example_vector

class PvmSlide(LessonSlide):
    lesson_deck='operators-pvm'
    stage=1

    def card(self, *items):
        return self.put(stack(*items, size=33, buff=.38),y=.35,height=3.65)

class PvTitle(LessonTitle):
    lesson_deck='operators-pvm'
    series_title='Spectral foundations'
    title_lines=('Projection-valued','measures')
    subtitle='Select spectral components. Then integrate them.'

class PvQuestion(PvmSlide):
    stage=0
    def body(self):
        self.start()
        self.card(r'Av_j=\lambda_jv_j',tex('Choose eigenvectors, or select the entire eigenspace?',size=29),
                  r'B\subseteq\mathbb R\quad\longmapsto\quad E(B)')
        self.beat()
        self.takeaway('A spectral set selects a subspace; the PVM returns its orthogonal projection.')
        self.source('Spectral-theorem tradition; Kato, Perturbation Theory for Linear Operators (1966).')

class PvWindow(PvmSlide):
    example=True
    def body(self):
        self.start()
        axes=Axes(x_range=[0,5,1],y_range=[0,2,1],x_length=10,y_length=2,
                  tips=False,axis_config={'include_ticks':False,'color':MUTED}).move_to([0,.55,0])
        dots=VGroup(*(Dot(axes.c2p(v,h),color=WANTED if v==2 else MUTED)
                       for v,h in [(1,.3),(2,.3),(2,1.1),(4,.3)]))
        labels=VGroup(*(math(str(v),size=28).move_to(axes.c2p(v,-.35)) for v in [1,2,4]))
        window=Rectangle(width=2,height=2.1,color=GAP,fill_opacity=.12).move_to(axes.c2p(2,.6))
        self.add(axes,window,dots,labels)
        formula=math(r'E([1.5,2.5])=\operatorname{diag}(0,1,1,0)',size=34).move_to([0,-1.5,0]);self.add(formula)
        self.beat()
        larger=Rectangle(width=6,height=2.1,color=GAP,fill_opacity=.12).move_to(axes.c2p(3,.6))
        self.play(Transform(window,larger),dots[-1].animate.set_color(WANTED),
                  Transform(formula,math(r'E([1.5,4.5])=\operatorname{diag}(0,1,1,1)',size=34).move_to(formula)))
        self.takeaway('A spectral window selects the whole eigenspace at each included eigenvalue.')

class PvMatrix(PvmSlide):
    example=True
    def body(self):
        self.start()
        self.card(r'A=\sum_j\lambda_jP_j,\qquad \sum_jP_j=I',
                  boxed(math(r'E(B)=\sum_{\lambda_j\in B}P_j',size=40),color=WANTED),
                  tex('One projector per distinct eigenvalue, including its full multiplicity.',size=28))
        self.beat();self.takeaway('Changing a basis inside an eigenspace leaves the spectral projection unchanged.')

class PvLaws(PvmSlide):
    def body(self):
        self.start()
        self.card(r'E(B)^*=E(B),\quad E(B)^2=E(B)',r'E(\varnothing)=0,\quad E(\mathbb R)=I',
                  boxed(math(r'E(B)E(C)=E(B\cap C)',size=38),color=WANTED))
        self.beat();self.takeaway('Within one PVM: complements give I minus E(B), and disjoint sets give orthogonal ranges.')

class PvCountable(PvmSlide):
    def body(self):
        self.start()
        self.card(tex('Disjoint Borel sets: apply the partial sums to a fixed vector.',size=28),
                  r'E\!\left(\bigcup_{j\ge1}B_j\right)x=\lim_{N\to\infty}\sum_{j=1}^N E(B_j)x',
                  boxed(math(r'\text{limit in the Hilbert-space norm, for each fixed }x',size=29),color=CURRENT))
        self.beat();self.takeaway('Countable additivity is strong convergence; operator-norm convergence is not required.')

class PvMass(PvmSlide):
    example=True
    def body(self):
        self.start()
        masses=atom_masses(example_vector())
        group=VGroup()
        for i,(value,mass) in enumerate(zip([1,2,4],masses)):
            bar=Rectangle(width=1,height=mass*4,color=WANTED,fill_opacity=.4).move_to([i*2-2,mass*2,0])
            group.add(bar,math(fr'{mass:g}',size=29).next_to(bar,DOWN),math(str(value),size=28).move_to([i*2-2,-.85,0]))
        self.put(group,'left',y=.35,height=3)
        self.put(stack(r'\mu_x(B)=\|E(B)x\|^2',r'\mu_x(\mathbb R)=\|x\|^2',
                       r'\mu_x(\{2\})=1/2',r'\operatorname{rank}E(\{2\})=2',size=31),'right',y=.3,height=3.3)
        self.beat();self.takeaway('The scalar measure records this vector\'s energy, rather than the selected subspace dimension.')

class PvIntegral(PvmSlide):
    def body(self):
        self.start()
        self.card(r'f=\sum_j c_j1_{B_j}\quad\Longrightarrow\quad\int f\,dE=\sum_jc_jE(B_j)',
                  tex('Select each piece, then multiply it by its function value.',size=28),
                  r'f(A)=\int_{\mathbb R}f(\lambda)\,dE(\lambda)')
        self.beat();self.takeaway('Spectral integration extends eigenvalue weighting: f(lambda) = lambda squared gives A squared.')

class PvContinuous(PvmSlide):
    example=True
    def body(self):
        self.start()
        axes=Axes(x_range=[0,1,.25],y_range=[0,1.5,.5],x_length=5,y_length=2.4,tips=False).move_to([-3.2,.4,0])
        original=Line(axes.c2p(0,1),axes.c2p(1,1),color=TRIAL,stroke_width=7)
        area=Rectangle(width=2,height=1.6,color=WANTED,fill_opacity=.35).move_to(axes.c2p(.4,.5))
        self.add(axes,original,area,
                 math(r'x(t)=1',size=27,color=TRIAL).move_to([-4.4,2,0]),
                 math(r'E(B)x=1_B',size=27,color=WANTED).move_to([-2.1,2,0]),
                 math('0',size=23).move_to(axes.c2p(0,-.18)),
                 math('1',size=23).move_to(axes.c2p(1,-.18)))
        self.put(stack(r'H=L^2([0,1]),\quad (Af)(t)=tf(t)',r'(E(B)f)(t)=1_B(t)f(t)',
                       r'x(t)=1,\quad\mu_x([a,b])=b-a',
                       r'0\le a\le b\le1',size=28),'right',y=.4,height=3)
        self.beat();self.play(area.animate.stretch(1.5,0,about_edge=np.array([-1,0,0])))
        self.takeaway('Spectral selection still works when no nonzero eigenvectors exist.')

class PvStrong(PvmSlide):
    example=True
    def body(self):
        self.start()
        bars=VGroup()
        for n in range(1,9):
            bar=Rectangle(width=.65,height=2/n,color=WANTED if n==1 else MUTED,fill_opacity=.4).move_to([-4+n,1/n,0])
            bars.add(bar)
        self.add(bars,tex('Infinitely many coordinates continue beyond the picture ...',size=25).move_to([0,-.7,0]))
        self.put(math(r'P_Nx\to x\quad\text{for each fixed }x\in\ell^2',size=33),y=1.95,height=.6)
        self.put(math(r'\|I-P_N\|_{\rm op}=1\quad\text{(test }e_{N+1}\text{)}',size=33),y=-1.5,height=.7)
        self.beat();self.play(*(bar.animate.set_color(WANTED) for bar in bars[:5]))
        self.takeaway('A fixed vector loses less tail energy; a new unit vector can always lie beyond the cutoff.')

class PvUnbounded(PvmSlide):
    example=True
    def body(self):
        self.start()
        self.card(r'(Ax)_n=nx_n,\qquad (E(B)x)_n=1_B(n)x_n',
                  r'\operatorname{Dom}A=\{x\in\ell^2:\sum_{n\ge1}n^2|x_n|^2<\infty\}',
                  r'x_n=1/n:\quad x\in\ell^2,\quad Ax=(1,1,\ldots)\notin\ell^2')
        self.beat();self.takeaway('Every spectral projection is bounded; the unbounded spectral integral has a domain condition.')

class PvCutoff(PvmSlide):
    stage=2
    def body(self):
        self.start()
        self.card(r'\operatorname{Dom}A=\{x:\int\lambda^2\,d\mu_x(\lambda)<\infty\}',
                  r'B\subseteq[-M,M],\ M\ge0\quad\Longrightarrow\quad E(B)H\subseteq\operatorname{Dom}A',
                  boxed(math(r'\|AE(B)x\|\le M\|x\|',size=39),color=CURRENT))
        self.beat();self.takeaway('A bounded spectral window produces vectors on which the operator can safely act.')

class PvDk(PvmSlide):
    stage=2
    def body(self):
        self.start()
        self.card(r'A\quad\longrightarrow\quad\widehat A=A+H',
                  r'P=E_A(B),\qquad Q=E_{\widehat A}(\widehat B)',
                  tex('Select the reducing subspaces; then ask how much they moved.',size=29),
                  r'\text{separation + residual + domain conditions}\ \Longrightarrow\ \text{angle bound}')
        self.beat();self.takeaway('PVMs define the spectral subspaces. Perturbation theorems control their change.')

class PvSummary(PvmSlide):
    stage=3
    def body(self):
        self.start()
        self.card(r'\text{set}\ B\ \longmapsto\ \text{projection}\ E(B)',
                  r'\text{vector}\ x\ \longmapsto\ \text{scalar measure}\ \mu_x',
                  r'\text{function}\ f\ \longmapsto\ \text{operator}\ f(A)',
                  tex('Strong limits and operator domains remain part of the statement.',size=28))
        self.beat();self.takeaway('Selection, energy measurement, and spectral integration are three views of the same structure.')

class PvFacts(PvmSlide):
    stage=3
    def body(self):
        self.start()
        self.card(r'E(B)E(C)=E(B\cap C)',r'E(B^c)=I-E(B)',r'\|E(B)x\|^2=\mu_x(B)',
                  tex('B and C are Borel sets; x is any vector in the complex Hilbert space.',size=27))
        self.takeaway('These three symbolic facts correspond to the next three checked Lean examples.')

class PvLean(LessonLean):
    lesson_deck='operators-pvm'
    lecture_id='pvm'
    assumptions='P is a PVM on a complex Hilbert space; B and C are measurable spectral sets.'
    symbolic_facts=(('Intersection',r'E(B)E(C)=E(B\cap C)'),('Complement',r'E(B^c)=I-E(B)'),
                    ('Vector energy',r'\|E(B)x\|^2=\mu_x(B)'))
    ownership='Accepted Tau Ceti abstract PVM laws; Spectra ancestry is recorded in sources.md.'
    notation=r'\texttt{P.proj B hB} is $E(B)$; \texttt{hB} proves measurability; \texttt{P.diag x} is $\mu_x$.'

class PvLeanComplement(PvLean):
    fact_index=1

class PvLeanMass(PvLean):
    fact_index=2

class PvComputation(PvmSlide):
    bonus=True
    stage=3
    def body(self):
        self.start()
        self.card(r'A=Q\Lambda Q^*,\qquad E(B)x=Q_B(Q_B^*x)',
                  tex('Q B contains the eigenvectors selected by the spectral window.',size=28),
                  tex('Window membership is sensitive near its boundary; check the gap.',size=28),
                  tex('Finite discretizations do not automatically converge in operator norm.',size=28))
        self.takeaway('Apply a selected eigenframe without forming a dense projector; keep numerical and analytic limits distinct.')
