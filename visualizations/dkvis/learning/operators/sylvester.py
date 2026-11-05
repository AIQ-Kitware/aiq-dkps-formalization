"""Residual inversion and the precise role of ordered spectral separation."""
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, stack
from dkvis.learning.operators.model import sylvester_example
from dkvis.slide_style import CURRENT, boxed, math, tex


class SylvesterSlide(LessonSlide):
    lesson_deck='operators-sylvester'


class SyTitle(LessonTitle):
    lesson_deck='operators-sylvester'
    series_title = 'Accepted operator foundations'
    title_lines=('Sylvester equations','and spectral separation')
    subtitle='A gap turns a residual equation into an error estimate.'


class SyQuestion(SylvesterSlide):
    def body(self):
        self.start()
        self.put(stack(r'AX-XB=R',
            tex('A and B are known. X is the unknown map. R is a measured residual.',size=29),
            r'(a-b)x=r\quad\Longrightarrow\quad x=\frac{r}{a-b}',
            boxed(math(r'\text{small residual} + \text{certified gap} \Longrightarrow \text{small solution}',size=29),color=CURRENT),
            tex('Classical Sylvester/Rosenblum theory supplies a mechanism behind angle bounds.',size=27),buff=.45),y=.4,height=3.7)
        self.takeaway('Residual size is informative only after the inverse problem has been controlled.')


class SyEntries(SylvesterSlide):
    stage=1
    def body(self):
        self.start()
        self.put(stack(r'A=\operatorname{diag}(a_i),\quad B=\operatorname{diag}(b_j)',
            r'(AX-XB)_{ij}=(a_i-b_j)x_{ij}',
            boxed(math(r'x_{ij}=\frac{r_{ij}}{a_i-b_j}\quad(a_i\ne b_j)',size=35),color=CURRENT),
            tex('In orthonormal eigenbases, the matrix equation becomes scalar division.',size=28),
            tex('Small denominators amplify errors. This is the geometric role of separation.',size=28),buff=.45),y=.4,height=3.5)
        self.takeaway('Entrywise solvability is not yet a dimension-free operator-norm estimate.')


class SyGap(SylvesterSlide):
    stage=1
    def body(self):
        self.start()
        self.put(stack(r'A\ge(c+\delta)I,\quad B\le cI,\quad\delta>0',
            r'Y(t)=e^{-tA}Xe^{tB},\quad Y^\prime(t)=-e^{-tA}Re^{tB}',
            r'\|Y(t)\|\le e^{-\delta t}\|X\|\longrightarrow0',
            tex('Bounded self-adjoint operators on Hilbert spaces; use the ordered form gap.',size=26),size=29,buff=.35),y=1.2,height=2.3)
        self.beat()
        self.put(stack(r'X=\int_0^\infty e^{-tA}Re^{tB}\,dt',
            boxed(math(r'\|X\|\le\|R\|\int_0^\infty e^{-\delta t}dt=\frac{\|R\|}{\delta}',size=29),color=CURRENT),buff=.18),y=-1.2,height=1.9)
        self.takeaway('Exponential decay makes the inverse integral converge and gives the constant one.')


class SyExample(SylvesterSlide):
    example=True
    stage=2
    def body(self):
        self.start()
        a,b,r,x=sylvester_example()
        self.put(stack(r'A=\operatorname{diag}(3,4),\quad B=\operatorname{diag}(0,1),\quad\delta=2',
            r'R=\begin{pmatrix}1&2\\3&4\end{pmatrix},\qquad(a_i-b_j)=\begin{pmatrix}3&2\\4&3\end{pmatrix}',
            boxed(math(r'X=\begin{pmatrix}1/3&1\\3/4&4/3\end{pmatrix}',size=34),color=CURRENT),
            r'AX-XB=R,\qquad2\|X\|\le\|R\|',size=29,buff=.48),y=.4,height=3.7)
        self.takeaway('The entrywise formula solves this example; the ordered gap controls its operator norm.')


class SySummary(SylvesterSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('The Sylvester map is linear in its unknown.',size=31),
            tex('Spectral separation controls inversion, with hypotheses depending on the norm.',size=28),
            tex('The constant-one estimate here uses an ordered quadratic-form gap.',size=28),
            tex('Tau Ceti also has separate domain-aware partial-map Sylvester results.',size=28),
            tex('Those results explicitly retain domains; they are not asserted by these matrix examples.',size=26),buff=.43),y=.4,height=3.5)
        self.source('Accepted Tau Ceti: Sylvester; LinearPMap/Sylvester. See the provenance guide.')
        self.takeaway('State the separation configuration and operator/domain scope before using a gap bound.')


class SyComputation(SylvesterSlide):
    bonus = True
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Dense numerical solution: Bartels--Stewart via Schur decompositions.',size=28),
            tex('Transform to triangular equations, solve, then transform back.',size=29),
            boxed(math(r'AX-XB=R\quad\leadsto\quad\texttt{solve\_sylvester}(A,-B,R)',size=29),color=CURRENT),
            tex('SciPy uses a plus sign in its second term, so our call passes minus B.',size=27),
            r'\|AX-XB-R\|\quad\text{checks the computed residual}',buff=.42),y=.4,height=3.5)
        self.source('SciPy Sylvester-solver documentation; LAPACK TRSYL.')
        self.takeaway('A small computed residual becomes a solution-error estimate only with a valid inverse bound.')


class SyFacts(SylvesterSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(boxed(math(r'\mathcal S_{A,B}(X)=AX-XB',size=35),color=CURRENT),
            r'\langle Ax,x\rangle\ge(c+\delta)\|x\|^2,\quad\langle By,y\rangle\le c\|y\|^2',
            boxed(math(r'\delta\|X\|\le\|\mathcal S_{A,B}(X)\|',size=35),color=CURRENT),
            tex('The accepted bounded-operator norm lemma needs these form bounds, not finite dimension.',size=27),buff=.5),y=.4,height=3.5)
        self.takeaway('The Lean norm theorem also works beyond the self-adjoint examples used to motivate it.')


class SyLean(LessonLean):
    assumptions = '$A,B,X$ are bounded real operators on an inner product space $E$. Form hypotheses are explicit below.'
    lesson_deck='operators-sylvester'
    lecture_id='sylvester'
    symbolic_facts=(('Define the linear map',r'\mathcal S_{A,B}(X)=AX-XB'),
                    ('Ordered form gap',r'\delta\|X\|\le\|\mathcal S_{A,B}(X)\|'))
    ownership='Accepted Tau Ceti: bounded Sylvester definition and ordered form-gap estimate.'
    notation=r'$\to_L$ means bounded linear map; $\langle\cdot,\cdot\rangle$ is the real inner product here.'


class SyLeanGap(SyLean):
    fact_index = 1
