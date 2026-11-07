"""An error band controls minimum values, but not optimizer locations."""
from manim import Axes, Dot, ValueTracker, always_redraw, linear
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, stack
from dkvis.slide_style import CURRENT, TRIAL, WANTED, SINE, boxed, math, tex
from dkvis.learning.uniform_minima.model import band_cost,moving_dip

class UniformSlide(LessonSlide):
    lesson_deck='prereq-uniform-minima'
    stage_labels=('One error band','Compare minima','Test the limits','Recap')
class UmTitle(LessonTitle):
    lesson_deck='prereq-uniform-minima'
    title_lines=('Uniform approximation','What happens to a minimum?')
    subtitle='The optimizer can move; the same bound must still apply.'
class UmBand(UniformSlide):
    example=True
    def body(self):
        self.start();axes=Axes(x_range=[-2,2,1],y_range=[-1,5,1],x_length=5.2,y_length=3.3,tips=False);self.put(axes,'left',y=.2)
        eps=ValueTracker(.8)
        self.add(axes.plot(lambda x:x*x,color=WANTED),always_redraw(lambda:axes.plot(lambda x:band_cost(x,eps.get_value()),color=TRIAL)),
            always_redraw(lambda:axes.plot(lambda x:x*x+eps.get_value(),color=SINE,stroke_opacity=.5)),
            always_redraw(lambda:axes.plot(lambda x:x*x-eps.get_value(),color=SINE,stroke_opacity=.5)))
        self.put(stack(r'f(x)=x^2,\quad g(x)=x^2+\varepsilon\sin(3x)',
            boxed(math(r'|g(x)-f(x)|\le\varepsilon\quad\text{for every }x',size=31),color=CURRENT),
            tex('The tolerance does not depend on the candidate.',size=28),buff=.5),'right',y=.4,height=3.5)
        self.beat();self.play(eps.animate.set_value(.1),run_time=3,rate_func=linear)
        self.takeaway('Uniform means every input is inside the same error band at once.')
class UmUpper(UniformSlide):
    stage=1
    def body(self):
        self.start();self.put(stack(r'x_*\in\arg\min f,\qquad y_*\in\arg\min g',
            tex('Test the approximate problem at the old minimizer.',size=30),
            boxed(math(r'g(y_*)\le g(x_*)\le f(x_*)+\varepsilon',size=36),color=TRIAL),
            tex('The new minimum cannot be too high.',size=30),buff=.6),y=.4,height=3.6)
        self.takeaway('The minimizing property chooses the first inequality; the error band supplies the second.')
class UmLower(UniformSlide):
    stage=1
    def body(self):
        self.start();self.put(stack(r'g(y_*)\ge f(y_*)-\varepsilon\ge f(x_*)-\varepsilon',
            tex('Now the true minimum controls the moving candidate.',size=29),
            boxed(math(r'|\min g-\min f|\le\varepsilon',size=41),color=CURRENT),
            tex('Minimizers are assumed supplied; the comparison does not require compactness.',size=26),buff=.6),y=.4,height=3.6)
        self.takeaway('The same band controls both sides of the minimum-value difference.')
class UmDip(UniformSlide):
    example=True;stage=2
    def body(self):
        self.start();axes=Axes(x_range=[0,1,.25],y_range=[-1.3,.4,.5],x_length=5.2,y_length=3.3,tips=False);self.put(axes,'left',y=.2)
        n=ValueTracker(2)
        self.add(always_redraw(lambda:axes.plot(lambda x:moving_dip(x,n.get_value()),x_range=[0,1,.001],color=TRIAL,use_smoothing=False)),
            always_redraw(lambda:Dot(axes.c2p(1/n.get_value(),-1),color=SINE)))
        self.put(stack(r'f_n(x)=-\max(0,1-3n|x-1/n|),\quad n\ge2',
            r'f_n(x)\to0\quad\text{for each fixed }x\in[0,1]',
            boxed(math(r'\min f_n=-1\ne0=\min f',size=34),color=SINE),
            tex(r'Limit: $f(x)=0$ for every x.',size=27),buff=.5),'right',y=.4,height=3.6)
        self.beat();self.play(n.animate.set_value(10),run_time=4,rate_func=linear)
        self.takeaway('An optimizer can follow a region that each fixed input eventually misses.')
class UmLocations(UniformSlide):
    example=True;stage=2
    def body(self):
        self.start();self.put(stack(r'g_n(x)=\frac{(-1)^n x}{n},\quad x\in[0,1],\ n\ge1',
            r'\|g_n\|_\infty\le1/n\longrightarrow0',
            r'\arg\min g_n=\{0\}\text{ for even }n,\quad\{1\}\text{ for odd }n',
            boxed(math(r'\min g_n\to0\quad\text{but the minimizers alternate.}',size=32),color=CURRENT),buff=.55),y=.4,height=3.7)
        self.takeaway('Value convergence does not establish convergence to one optimizer.')
class UmSummary(UniformSlide):
    stage=3
    def body(self):
        self.start();self.put(stack(r'\sup_x|g_n(x)-f(x)|\le\varepsilon_n\longrightarrow0',
            boxed(math(r'|\min g_n-\min f|\le\varepsilon_n\longrightarrow0',size=35),color=CURRENT),
            tex('The feasible set stays the same; every candidate obeys the bound.',size=28),
            tex('Optimizer locations need additional information.',size=29),buff=.55),y=.4,height=3.5)
        self.takeaway('Establish uniform objective control before moving an optimization through a limit.')
class UmFacts(UniformSlide):
    stage=3
    def body(self):
        self.start();self.put(stack(r'g(y_*)\le g(x_*)\le f(x_*)+\varepsilon',
            r'f(x_*)-\varepsilon\le f(y_*)-\varepsilon\le g(y_*)',
            boxed(math(r'f(x_*)-\varepsilon\le g(y_*)\le f(x_*)+\varepsilon',size=34),color=CURRENT),buff=.65),y=.4,height=3.2)
        self.takeaway('Only order comparisons and the band bound are used once minimizers exist.')
class UmLean(LessonLean):
    lesson_deck='prereq-uniform-minima';lecture_id='uniform_minima'
    symbolic_facts=(('Upper comparison',r'g(y)\le f(x)+\varepsilon'),('Lower comparison',r'f(x)-\varepsilon\le g(y)'))
    assumptions='Real-valued costs on the same candidate type; the hypotheses specify the minimizer and band bound.'
    ownership='Direct applications of Mathlib order transitivity; local examples state the two comparison steps.'
    notation=r'\texttt{hmin} supplies a minimizing inequality; the band bound holds for every candidate.'
class UmLeanLower(UmLean):fact_index=1
class UmComputation(UniformSlide):
    bonus=True
    def body(self):
        self.start();self.put(stack(tex('A grid can miss a narrow dip between sampled points.',size=31),
            r'|h(x)-h(x_i)|\le L|x-x_i|\quad\text{can control between-sample error.}',
            tex('An analytic bound over the full feasible set gives the required certificate.',size=28),
            tex('A small error at sampled points alone does not.',size=28),buff=.55),y=.4,height=3.5)
        self.takeaway('Keep a numerical illustration separate from an all-candidate bound.')
