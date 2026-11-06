"""Historical orientation: people, publications, and recurring geometric questions."""
from pathlib import Path
import numpy as np
import yaml
from manim import (
    Arc, Arrow, Circle, DashedLine, Dot, DOWN, Indicate, LEFT, Line,
    Rectangle, RIGHT, ValueTracker, VGroup, always_redraw, linear,
)
from dkvis.components.lesson import LessonSlide, LessonTitle, plane, stack, vector
from dkvis.slide_style import (
    CURRENT, FAINT, FG, GAP, MUTED, PANEL, RESID, SINE, TRIAL, WANTED,
    boxed, math, para, tex,
)

def prepare(refresh=False):
    from dkvis.presentation.external_assets import fetch
    fetch(['sylvester'],refresh=refresh)


PUBLICATIONS = yaml.safe_load(Path(__file__).with_name('publications.yaml').read_text())


def prose(text, width=5.4, size=26, color=FG):
    return para(text, width=width, size=size, color=color)


def card(key):
    p = PUBLICATIONS[key]
    content = VGroup(
        prose(p['author'], size=25, color=CURRENT),
        prose(p['year'], size=22, color=GAP),
        prose(p['title'], size=21),
        prose(p['venue'], size=18, color=MUTED),
    ).arrange(DOWN, aligned_edge=LEFT, buff=.10)
    return content


def node(text, position, color=CURRENT, width=4.5):
    label = prose(text, width=width-.35, size=25)
    border = Rectangle(width=width, height=max(.7, label.height+.28), color=color,
                       fill_color=PANEL, fill_opacity=1)
    return VGroup(border, label).move_to(position)


def join(a, b, color=MUTED):
    return Arrow(a.get_bottom(), b.get_top(), buff=.08, color=color, stroke_width=3)


class HistorySlide(LessonSlide):
    lesson_deck = 'history-overview'
    epoch = 1970
    stage = 1

    def make_chrome(self):
        chrome = super().make_chrome()
        # Dates are landmarks, not a numerical time axis. Keep them visible as
        # the narrative revisits parallel traditions rather than one lineage.
        years = [1875, 1912, 1936, 1956, 1970, 2015, 2026]
        index = min(range(len(years)), key=lambda i: abs(years[i]-self.epoch))
        axis = Line([-5.4, -2.02, 0], [5.4, -2.02, 0], color=FAINT)
        chrome.add(axis)
        for i, year in enumerate(years):
            x = -5.4+1.8*i
            color = CURRENT if i == index else MUTED
            chrome.add(Dot([x, -2.02, 0], radius=.035, color=color),
                       tex(str(year), size=17, color=color).move_to([x, -2.23, 0]))
        return chrome

    def publications(self, *keys):
        cards = VGroup(*(card(key) for key in keys)).arrange(DOWN, aligned_edge=LEFT, buff=.28)
        self.put(cards, 'right', y=.35, height=3.7)
        return cards

    def message(self, *items):
        return self.put(stack(*items, size=32, buff=.32), 'left', y=.35, height=3.6)

    def angles(self, pairs=False):
        centers = [(-4.5,.5), (-1.7,.5)] if pairs else [(-3.25,.5)]
        angle = ValueTracker(.12)
        self.add(tex('Schematic principal-plane views' if pairs else 'Schematic subspace view',
                     size=21, color=MUTED).move_to([-3.25,1.95,0]))
        for i, (x,y) in enumerate(centers):
            center=np.array([x,y,0])
            radius=1.15 if pairs else 1.7
            self.add(Line(center+LEFT*radius,center+RIGHT*radius,color=WANTED,stroke_width=5))
            def moving(center=center, radius=radius, i=i):
                theta=angle.get_value()*(1 if i==0 else 1.9)
                d=np.array([np.cos(theta),np.sin(theta),0])*radius
                return VGroup(Line(center-d,center+d,color=TRIAL,stroke_width=5),
                              Arc(radius=.45,start_angle=0,angle=theta,color=SINE).shift(center))
            self.add(always_redraw(moving))
        self.add(tex('reference',size=23,color=WANTED).move_to([-4.4,-1.1,0]),
                 tex('changed',size=23,color=TRIAL).move_to([-2,-1.1,0]))
        return angle


class HiTitle(LessonTitle):
    lesson_deck='history-overview'
    series_title='Mathematical history · Davis–Kahan and beyond'
    title_lines=('How eigenvector stability', 'became a subject')
    subtitle='People, publications, and the questions connecting them.'


class HiQuestion(HistorySlide):
    stage=0
    def body(self):
        self.start()
        angle=self.angles()
        self.put(stack(tex('Geometry',size=33,color=WANTED),
                       tex('Operator theory',size=33),
                       tex('Numerical analysis',size=33,color=RESID),
                       tex('Statistics',size=33,color=TRIAL),buff=.40),'right',y=.4)
        self.beat();self.play(angle.animate.set_value(.55),run_time=3,rate_func=linear)
        self.takeaway('One recurring question: how does a small change affect a selected subspace?')


class HiJordan(HistorySlide):
    epoch=1875
    def body(self):
        self.start();self.publications('jordan');angle=self.angles(pairs=True)
        self.beat();self.play(angle.animate.set_value(.45),run_time=3,rate_func=linear)
        self.takeaway('Principal angles describe how two spaces differ, direction by direction.')


class HiSylvester(HistorySlide):
    epoch=1884
    def body(self):
        from dkvis.components.attributed_image import add_attributed_image
        self.start()
        add_attributed_image(self,'sylvester',center=(-3.45,.95,0),height=2.7,credit_y=-1.15)
        self.publications('sylvester')
        self.beat()
        self.add(math(r'AX-XB=Y',size=35).move_to([3.25,-1.15,0]))
        self.takeaway('Sylvester supplies the matrix-equation background; later work develops operator estimates.')


class HiRayleighRitz(HistorySlide):
    epoch=1909
    def body(self):
        self.start();cards=self.publications('rayleigh','ritz')
        axes=plane(extent=2);self.put(axes,'left',y=.5,height=2.8)
        self.add(vector(axes,[1.2,.4],TRIAL),
                 math('v',size=28,color=TRIAL).move_to(axes.c2p(1.35,.2)),
                 tex('Trial approximation',size=25).move_to([-3.25,2,0]))
        self.beat()
        self.add(vector(axes,[1.2,1.2],WANTED),
                 Arrow(axes.c2p(1.2,.4),axes.c2p(1.2,1.2),buff=0,color=RESID),
                 math(r'Av-\rho v',size=27,color=RESID).move_to([-3.25,-1.3,0]))
        self.play(Indicate(cards[1]),run_time=1)
        self.takeaway('Residual: the part of the chosen eigen-equation that the approximation fails to satisfy.')


class HiWeyl(HistorySlide):
    epoch=1912
    def body(self):
        self.start();self.publications('weyl')
        self.add(tex('Example: a selected eigenvalue cluster',size=24).move_to([-3.25,1.9,0]),
                 Line([-5.8,.65,0],[-.7,.65,0],color=MUTED))
        dots=VGroup(Dot([-4.9,.65,0],color=WANTED),Dot([-3.5,.65,0],color=WANTED),
                    Dot([-1,.65,0],color=MUTED));self.add(dots)
        self.add(prose('Courant–Fischer: characterize eigenvalues through extremal Rayleigh quotients.',size=24)
                 .move_to([-3.25,-.9,0]))
        self.beat();self.play(dots[0].animate.shift(RIGHT*.8),dots[1].animate.shift(LEFT*.4),run_time=3)
        self.add(Rectangle(width=2.35,height=.75,color=GAP).move_to([-3.95,.65,0]))
        self.takeaway('A separated cluster may define a stable space even when its individual basis is ambiguous.')


class HiHotelling(HistorySlide):
    epoch=1936
    def body(self):
        self.start();self.publications('hotelling')
        self.message(tex('Two collections of variables',size=29),
                     math(r'X\qquad\longleftrightarrow\qquad Y',size=40),
                     prose('Choose combinations that are as strongly associated as possible.'),
                     tex('Canonical correlations',size=30,color=CURRENT))
        self.beat()
        self.add(boxed(tex('Compare best-aligned directions',size=23),color=WANTED).move_to([-3.25,-1.35,0]))
        self.takeaway('Subspace geometry appears in statistics as well as in operator theory.')


class HiProjectionPeople(HistorySlide):
    epoch=1956
    def body(self):
        self.start();self.publications('sznagy','davis58');angle=self.angles()
        self.beat();self.play(angle.animate.set_value(.6),run_time=3,rate_func=linear)
        self.takeaway('A projection identifies a space; a transporter carries that entire space to another.')


class HiKatoHalmos(HistorySlide):
    epoch=1966
    def body(self):
        self.start();cards=self.publications('kato','halmos')
        top=node('Spectral projections\nfollow a changing operator',[-3.25,1.25,0],WANTED)
        bottom=node('Two projections\nreveal common and interacting parts',[-3.25,-.7,0],TRIAL)
        self.add(top)
        self.beat();self.add(bottom);self.play(Indicate(cards[1]),run_time=1)
        self.takeaway('Hilbert-space operator structure extends the finite principal-plane picture.')


class HiRosenblum(HistorySlide):
    epoch=1956
    def body(self):
        self.start();self.publications('rosenblum')
        self.message(tex('Sylvester: matrix equations (1884)',size=24,color=MUTED),
                     math(r'BX-XA=Y',size=40),
                     prose('An operator equation can encode the unwanted part of a trial subspace.'))
        self.beat()
        self.add(VGroup(math(r'(b-a)x=y',size=31),
                        math(r'|b-a|\ge\delta>0\ \Longrightarrow\ |x|\le |y|/\delta',size=29))
                 .arrange(DOWN,buff=.18).move_to([-3.25,-1.0,0]))
        self.takeaway('Scalar intuition: separation makes the unknown error controllable.')


class HiDavisKahan(HistorySlide):
    epoch=1970
    def body(self):
        self.start();cards=self.publications('davis63','dk')
        self.message(tex('1963 $\to$ 1965 $\to$ 1969 $\to$ 1970',size=28,color=GAP),
                     prose('Davis\'s earlier papers $\to$ joint announcement $\to$ extended joint treatment.'),
                     tex('Several angle theorem families',size=28,color=CURRENT),
                     math(r'\sin\Theta,\quad\tan\Theta,\quad\sin 2\Theta,\quad\tan 2\Theta',size=29))
        self.beat();self.play(Indicate(cards[1]),run_time=1)
        self.takeaway('Davis and Kahan connect subspace rotation with quantitative error and spectral separation.')


class HiBound(HistorySlide):
    epoch=1970
    def body(self):
        self.start();angle=self.angles()
        self.put(stack(tex('The sine-theta mechanism',size=31),
                       boxed(math(r'\text{error}\ \le\ \frac{\text{residual}}{\text{separation}}',size=34),color=CURRENT),
                       prose('Under the theorem\'s spectral, norm, and domain assumptions.'),
                       tex('residual',size=30,color=RESID),
                       tex('certified separation',size=30,color=GAP),buff=.30),'right',y=.45)
        self.beat();self.play(angle.animate.set_value(.6),run_time=3)
        self.takeaway('A residual measures equation error; separation makes it informative about the selected space.')


class HiWedinGolub(HistorySlide):
    epoch=1973
    def body(self):
        self.start();cards=self.publications('wedin','golub')
        a=node('Wedin: how singular subspaces change',[-3.25,1.2,0],WANTED)
        b=node('Björck–Golub: how to compute angles',[-3.25,-.7,0],TRIAL)
        self.add(a)
        self.beat();self.add(b);self.play(Indicate(cards[1]),run_time=1)
        self.takeaway('Perturbation estimates and numerical methods answer distinct, complementary questions.')


class HiYws(HistorySlide):
    epoch=2015;stage=2
    def body(self):
        self.start();self.publications('yws')
        population=node('Population matrix A',[-3.25,1.5,0],WANTED)
        sample=node('Estimated matrix A-hat',[-3.25,-.15,0],TRIAL)
        self.add(population,sample,join(population,sample))
        self.beat()
        self.add(prose('YWS: place the gap condition on the population eigenvalues.',size=27,color=GAP)
                 .move_to([-3.25,-1.3,0]))
        self.takeaway('A population gap is useful when the matrix estimated from data is random.')


class HiQuench(HistorySlide):
    epoch=2026;stage=2
    def body(self):
        self.start();self.publications('quench')
        nodes=[node(label,[-3.25,y,0],color) for label,y,color in [
            ('Cached responses',1.65,TRIAL),('Model geometry / embedding',.55,WANTED),
            ('Predict benchmark performance',-.55,CURRENT)]]
        self.add(*nodes,join(nodes[0],nodes[1]),join(nodes[1],nodes[2]),
                 tex('Several statistical steps are needed.',size=23,color=MUTED).move_to([-3.25,-1.45,0]))
        self.takeaway('Quench is a brief application of stable geometry within a larger statistical argument.')


class HiNormPeople(HistorySlide):
    epoch=1951;stage=2
    def body(self):
        self.start();self.publications('vonneumann','schatten','fan')
        self.message(tex('Example: two singular-value lists',size=24),
                     math(r'a=(2,0),\qquad b=(1.2,1.2)',size=31),
                     tex('Largest entry: b is smaller.',size=27,color=WANTED))
        self.beat()
        self.add(tex('Sum of entries: a is smaller.',size=27,color=TRIAL).move_to([-3.25,-1.1,0]))
        self.takeaway('The norm is part of an optimality claim: different costs can favor different motions.')


class HiCorrection(HistorySlide):
    epoch=2026;stage=2
    def body(self):
        self.start();self.publications('dk')
        claim=node('Printed Proposition 4.4',[-3.25,1.6,0])
        counter=node('Real trace-norm counterexample',[-3.25,.3,0],TRIAL)
        repair=node('Separate Q-norm repair',[-3.25,-1.0,0],RESID)
        self.add(claim,counter,join(claim,counter))
        self.beat();self.add(repair,join(counter,repair))
        self.takeaway('The source correction concerns full-displacement optimality and its norm class.')


class HiMatching(HistorySlide):
    epoch=2026;stage=2
    def body(self):
        self.start()
        positions=[[-4.8,1.2,0],[-1.7,1.2,0],[-4.8,-.7,0],[-1.7,-.7,0]]
        for i,pos in enumerate(positions):
            self.add(Dot(pos,radius=.12,color=WANTED),
                     math(r'\theta_'+str(i+1),size=30).move_to(np.array(pos)+DOWN*.4))
        self.put(stack(tex('Unrestricted real transport',size=30),
                       math(r'\min_{W(K)=L}\|I-W\|_{S_p}^{p}',size=36),
                       math(r'1\le p<2,\qquad W\in O(n)',size=30),
                       prose('Equal-dimensional real subspaces; finite ambient dimension.'),
                       tex('minimum value + attainment',size=27,color=CURRENT)),
                 'right',y=.35,height=3.6)
        self.beat();self.add(Line(positions[0],positions[1],color=CURRENT,stroke_width=6),
                             Circle(radius=.23,color=TRIAL).move_to(positions[2]),
                             Circle(radius=.23,color=TRIAL).move_to(positions[3]))
        self.takeaway('Labelled angles become vertices: choose disjoint pairs and pay for unmatched vertices.')


class HiEvidence(HistorySlide):
    epoch=2026;stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Teaching prerequisites',size=32,color=WANTED),
                       prose('Which explanation helps a learner understand another?',width=10,size=27),
                       tex('Formal proof dependencies',size=32,color=RESID),
                       prose('Which precise statements does a Lean proof use?',width=10,size=27),buff=.25),y=.65,height=3.1)
        self.beat()
        self.add(VGroup(tex('Historical development',size=32,color=TRIAL),
                        prose('Who published what, when, and with what documented connections?',width=10,size=27))
                 .arrange(DOWN,buff=.18).move_to([0,-1.15,0]))
        self.takeaway('Lean checks formal propositions; history and human understanding require their own evidence.')


class HiSummary(HistorySlide):
    epoch=2026;stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Compare spaces',size=31,color=WANTED),
                       prose('Jordan · Sz.-Nagy · Davis · Kato · Halmos'),
                       tex('Control approximation error',size=31,color=RESID),
                       prose('Rayleigh · Ritz · Weyl · Rosenblum · Davis–Kahan'),
                       prose('Wedin: singular subspaces\nBjörck–Golub: numerical angles',size=23),buff=.25),
                 'left',y=.4,height=3.7)
        self.beat()
        self.put(stack(tex('Use geometry in statistics',size=31,color=TRIAL),
                       prose('Hotelling · Yu–Wang–Samworth\nHelm–Johnson–Priebe'),
                       tex('Measure and optimize movement',size=31,color=CURRENT),
                       prose('von Neumann · Schatten · Ky Fan\nSource correction $\to$ transport extensions'),
                       prose('Next: projections, angles, residuals, gaps; or norms and feasible variations.',size=23),buff=.25),
                 'right',y=.4,height=3.7)
        self.takeaway('Follow the problems as well as the names: geometry $\to$ error control $\to$ applications and new questions.')
