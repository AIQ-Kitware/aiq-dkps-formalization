"""Rayleigh–Ritz as a restricted search, with a geometric residual explanation."""
import numpy as np
from manim import (Axes, Arrow, Line, RightAngle, Transform, ValueTracker, VGroup,
                   DecimalNumber, always_redraw, linear, UP, DOWN, RIGHT, LEFT,
                   Dot, DashedLine, ParametricFunction, Matrix, GrowArrow, Create,
                   Indicate, SurroundingRectangle, NumberLine, RoundedRectangle, Circle, FadeIn, DashedVMobject)
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.learning.rayleigh_ritz.model import trial_example, trial_action, trial_quotient, nested_extrema
from dkvis.learning.rayleigh_ritz.visuals import TrialPlane, formula, matrix_tiles
from dkvis.slide_style import CURRENT, TRIAL, RESID, MUTED, WANTED, FG, boxed, math, tex


class RitzSlide(LessonSlide):
    lesson_deck = 'operators-rayleigh-ritz'
    stage = 1
    stage_labels = ('Search space', 'Small model', 'Full residual', 'Recap')

    def card(self, *items, size=32, first=None):
        card = self.put(stack(*items, size=size, buff=.38), y=.35, height=3.6)
        if first is not None:
            self.remove(card)
            self.add(*card[:first])
        return card


class RrTitle(LessonTitle):
    lesson_deck = 'operators-rayleigh-ritz'
    series_title = 'Spectral approximation foundations'
    title_lines = ('Rayleigh–Ritz', 'Trial spaces and residuals')
    subtitle = 'What can a smaller eigenproblem tell us about the original one?'


class RrQuestion(RitzSlide):
    stage=0
    def body(self):
        self.start()
        large=matrix_tiles(8,CURRENT).move_to([-3.4,.5,0])
        small=matrix_tiles(3,TRIAL,cell=.42).move_to([3.4,.5,0])
        self.add(large,tex('Original operator A',size=28,color=CURRENT).next_to(large,UP),
                 math(r'n\times n',size=28,color=CURRENT).next_to(large,DOWN))
        arrow=Arrow([-1.65,.5,0],[1.65,.5,0],color=MUTED,buff=0)
        self.play(GrowArrow(arrow),run_time=1)
        self.add(tex('fewer candidate directions?',size=23).move_to([0,1.1,0]),small,
                 tex('Small model B',size=28,color=TRIAL).next_to(small,UP),
                 math(r'k\times k,\quad k\ll n',size=28,color=TRIAL).next_to(small,DOWN))
        self.beat()
        self.put(tex('What must the small problem preserve, and how do we check its answer?',size=28),y=-1.5,height=.7)
        self.source('Rayleigh (1877); Ritz (1909): variational approximation of eigenproblems.')
        self.takeaway('A smaller problem needs a meaningful link to A and a way to check what it leaves out.')


class RrSpace(RitzSlide):
    stage=0
    example=True
    def body(self):
        self.start()
        view=TrialPlane(); self.add(view)
        basis=view.basis(); self.play(Create(basis),run_time=1.5)
        x,y=ValueTracker(1),ValueTracker(0)
        chosen=always_redraw(lambda:view.arrow([x.get_value(),y.get_value(),0],TRIAL,width=7))
        self.add(chosen)
        self.put(stack(formula(('u',TRIAL),'=',('y_1q_1+y_2q_2',TRIAL),size=35),
                       math(r'\mathcal T=\operatorname{span}(q_1,q_2)',size=31,color=TRIAL),
                       tex('All linear combinations are allowed.',size=27),buff=.4),'right',y=.8,height=2.4)
        self.play(x.animate.set_value(.4),y.animate.set_value(1.4),run_time=2)
        self.play(x.animate.set_value(-1.2),y.animate.set_value(.5),run_time=2)
        self.beat()
        self.put(stack(tex('Trial: where we search.',size=27,color=TRIAL),
                       tex('Invariant: A always stays inside.',size=27),
                       tex('Wanted: the exact spectral target.',size=27,color=WANTED),buff=.22),'right',y=-1.15,height=1.4)
        self.takeaway('Choosing a trial plane allows these inputs. Its invariance and accuracy still need to be checked.')


class RrFrame(RitzSlide):
    stage=0
    example=True
    def body(self):
        self.start()
        axes=Axes(x_range=[-1.4,1.4,1],y_range=[-1.4,1.4,1],x_length=3.3,y_length=3.3,
                  tips=False,axis_config={'color':MUTED}).move_to([-3.5,.35,0])
        circle=ParametricFunction(lambda t:axes.c2p(np.cos(t),np.sin(t)),t_range=[0,2*np.pi],color=TRIAL)
        view=TrialPlane(origin=(3.25,-.4,0),scale=.65)
        unit=ParametricFunction(lambda t:view.point([np.cos(t),np.sin(t),0]),t_range=[0,2*np.pi],color=TRIAL)
        t=ValueTracker(0)
        dot1=always_redraw(lambda:Dot(axes.c2p(np.cos(t.get_value()),np.sin(t.get_value())),color=TRIAL))
        dot2=always_redraw(lambda:Dot(view.point([np.cos(t.get_value()),np.sin(t.get_value()),0]),color=TRIAL))
        self.add(axes,circle,view,unit,dot1,dot2)
        self.add(tex('Small coordinates y',size=26,color=TRIAL).move_to([-3.5,2.05,0]),
                 formula(('u=Qy',TRIAL),size=33).move_to([3.25,1.8,0]),
                 Arrow([-1.3,.7,0],[.6,.7,0],color=TRIAL),math('Q',size=34,color=TRIAL).move_to([-.35,1.15,0]))
        self.play(t.animate.set_value(np.pi/4),run_time=3,rate_func=linear)
        self.put(formula((r'\|y\|',TRIAL),'=',(r'\|Qy\|',TRIAL),'=1',size=32),'left',y=-1.75,height=.6)
        self.beat()
        q=np.array([1,1,0])/np.sqrt(2); v=q+np.array([0,0,1])
        self.play(GrowArrow(view.arrow(v,CURRENT)),run_time=1)
        self.add(DashedLine(view.point(v),view.point(q),color=RESID),
                 math('v',size=28,color=CURRENT).move_to(view.point(v)+RIGHT*.25))
        self.add(Arrow([.6,-.75,0],[-1.3,-.75,0],color=TRIAL),
                 math(r'Q^T',size=31,color=TRIAL).move_to([-.35,-1.1,0]))
        self.put(formula(('P=QQ^T',TRIAL),size=32),y=-1.75,height=.55)
        self.takeaway(r'$Q$ lifts coordinates; $Q^T$ reads them. $P=QQ^T$ projects onto the trial space.')


class RrCompress(RitzSlide):
    example=True
    def body(self):
        self.start()
        view=TrialPlane(); self.add(view,view.basis())
        u,true,retained,escaping=trial_action([1,0])
        actual=view.arrow(true,CURRENT); kept=view.arrow(retained,TRIAL)
        discarded=view.arrow(true,RESID,start=retained)
        self.add(view.arrow(u,TRIAL,width=7))
        question=self.put(tex('Can the model reproduce the full output?',size=27),'right',y=.65,height=1)
        self.beat()
        self.remove(question)
        self.play(GrowArrow(actual),run_time=2)
        self.put(formula(('y',TRIAL),r'\xrightarrow{Q}',('Qy',TRIAL),r'\xrightarrow{A}',('AQy',CURRENT),size=31),'right',y=1.55,height=.7)
        self.put(tex('The true output can leave the plane.',size=26,color=CURRENT),'right',y=.95,height=.5)
        self.beat()
        self.add(DashedLine(view.point(true),view.point(retained),color=RESID))
        self.put(formula(('By',TRIAL),'=',('Q^TAQy',TRIAL),size=33),'right',y=.3,height=.55)
        self.put(VGroup(tex('Compression',size=23,color=TRIAL),
                        boxed(formula(('B',TRIAL),'=',('Q^T',TRIAL),('A',CURRENT),('Q',TRIAL),size=38),color=TRIAL)
                        ).arrange(DOWN,buff=.12),'right',y=-.55,height=1.1)
        self.play(GrowArrow(kept),run_time=1.5)
        self.beat(); self.play(GrowArrow(discarded),run_time=1)
        self.put(formula(('QBy',TRIAL),'=',('PAQy',TRIAL),size=33),'right',y=-1.55,height=.6)
        self.takeaway('B records the projected output. The green component is the information this model discards.')


class RrQuotient(RitzSlide):
    example=True
    def body(self):
        self.start()
        axes=Axes(x_range=[0,2*np.pi,np.pi/2],y_range=[0,4,1],x_length=5.1,y_length=3,
                  tips=False,axis_config={'color':MUTED}).move_to([-3.35,.15,0])
        original=axes.plot(lambda a:trial_quotient(a)[2],x_range=[0,2*np.pi],color=CURRENT)
        compressed=DashedVMobject(axes.plot(lambda a:trial_quotient(a)[2],x_range=[0,2*np.pi],
                                          color=TRIAL,stroke_width=5),num_dashes=65)
        t=ValueTracker(0)
        dot=always_redraw(lambda:Dot(axes.c2p(t.get_value(),trial_quotient(t.get_value())[2]),color=CURRENT))
        view=TrialPlane(origin=(3.35,.35,0),scale=.46)
        view.caption.move_to([3.35,-.7,0])
        direction=always_redraw(lambda:view.arrow(trial_quotient(t.get_value())[1],TRIAL,width=6))
        label=math('u=Qy(t)',size=27,color=TRIAL).move_to([5.4,.6,0])
        self.add(axes,original,dot,view,view.basis().set_opacity(.45),direction,label,
                 formula(('u^TAu',CURRENT),size=29).move_to([-3.35,2,0]))
        for value in [1,2,3]:
            self.add(math(str(value),size=22).move_to(axes.c2p(-.32,value)))
        self.add(tex('Direction angle t',size=23).move_to([-3.35,-1.7,0]))
        numbers=self.put(formula((r'B=\begin{pmatrix}2&1\\1&2\end{pmatrix}',TRIAL),size=29),'right',y=1.7,height=.9)
        self.play(t.animate.set_value(np.pi/4),run_time=3,rate_func=linear)
        self.beat()
        first=self.put(formula(('u^TAu',CURRENT),'=',r'(Qy)^TA(Qy)',size=29),'right',y=-1.2,height=.6)
        self.remove(first);self.play(FadeIn(first),run_time=1)
        second=self.put(formula('=',r'y^T(',('Q^TAQ',TRIAL),r')y=',('y^TBy',TRIAL),size=29),'right',y=-1.9,height=.6)
        self.remove(second);self.play(FadeIn(second),run_time=1)
        self.play(Create(compressed),run_time=1)
        self.add(formula(('u^TAu',CURRENT),'=',('y^TBy',TRIAL),size=28).move_to([-3.35,-2.1,0]))
        self.beat()
        self.remove(numbers)
        symmetry=self.put(formula(('B^T',TRIAL),'=',r'Q^TA^TQ=',('B',TRIAL),size=28),'right',y=1.7,height=.6)
        self.remove(symmetry);self.play(FadeIn(symmetry),run_time=1)
        high=Dot(axes.c2p(np.pi/4,3),color=TRIAL)
        low=Dot(axes.c2p(3*np.pi/4,1),color=TRIAL)
        high_label=math(r'\max=3',size=23,color=TRIAL).next_to(high,UP,buff=.15)
        self.play(FadeIn(high),FadeIn(high_label),run_time=1)
        self.play(t.animate.set_value(3*np.pi/4),run_time=2,rate_func=linear)
        self.add(low,math(r'\min=1',size=23,color=TRIAL).next_to(low,DOWN,buff=.15))
        self.takeaway('The full and compressed curves coincide. Their extrema are the Ritz values.')


class RrSolve(RitzSlide):
    example=True
    def body(self):
        self.start()
        view=TrialPlane(); self.add(view)
        a,q,b,r=trial_example(); y=np.array([1,-1])/np.sqrt(2)
        u,true,kept,escaping=trial_action(y)
        self.put(stack(formula((r'B=\begin{pmatrix}2&1\\1&2\end{pmatrix}',TRIAL),size=34),
                       formula((r'y=\tfrac1{\sqrt2}(1,-1)^T',TRIAL),size=30),
                       formula(('By',TRIAL),'=',(r'1\cdot y',TRIAL),r',\quad',(r'\theta=1',TRIAL),size=30),buff=.32),'right',y=.85,height=2.6)
        self.beat(); self.play(GrowArrow(view.arrow(u,TRIAL,width=7)),run_time=1)
        self.put(formula(('u=Qy',TRIAL),r',\quad',('PAu=u',TRIAL),size=31),'right',y=-.9,height=.6)
        self.beat()
        self.play(GrowArrow(view.arrow(true,CURRENT)),run_time=1.2)
        self.play(GrowArrow(view.arrow(true,RESID,start=kept)),run_time=1.2)
        self.put(formula(('r',RESID),'=',('Au',CURRENT),'-',(r'\theta u',TRIAL),size=33),'right',y=-1.65,height=.6)
        self.takeaway('The small equation holds inside the plane. The full equation has the green residual outside it.')


class RrGeometry(RitzSlide):
    example=True
    def body(self):
        self.start()
        view=TrialPlane(); self.add(view,view.basis())
        a,q,b,r=trial_example()
        y1,y2=ValueTracker(1),ValueTracker(0)
        def data():
            return trial_action([y1.get_value(),y2.get_value()])
        arrows=always_redraw(lambda:view.selection(data()[1],data()[2]))
        self.add(arrows)
        self.put(formula(('R',RESID),'=',('AQ',CURRENT),'-',('QB',TRIAL),size=34),'right',y=1.6,height=.7)
        matrix=Matrix([['0','0'],['0','0'],['1','-1']],element_to_mobject=lambda v:math(v,size=29))
        matrix.get_entries().set_color(RESID)
        question=self.put(tex('What does one column record?',size=29),'right',y=.2,height=1)
        self.beat()
        self.remove(question)
        matrix.get_columns()[1].set_opacity(0)
        self.put(VGroup(math('R=',size=32,color=RESID),matrix).arrange(RIGHT,buff=.15),'right',y=.15,height=2)
        first=SurroundingRectangle(matrix.get_columns()[0],color=RESID,buff=.1)
        self.play(Create(first),run_time=.8)
        self.put(tex('Each column is one discarded output.',size=25),'right',y=-1.15,height=.6)
        self.beat()
        self.play(y1.animate.set_value(0),y2.animate.set_value(1),
                  matrix.get_columns()[1].animate.set_opacity(1),
                  Transform(first,SurroundingRectangle(matrix.get_columns()[1],color=RESID,buff=.1)),run_time=2)
        self.beat()
        self.play(y1.animate.set_value(1/np.sqrt(2)),y2.animate.set_value(1/np.sqrt(2)),
                  Transform(first,SurroundingRectangle(matrix.get_entries(),color=RESID,buff=.1)),run_time=3)
        self.put(formula(('Ry',RESID),'=','0',r'\quad\text{for }y=(1,1)^T/\sqrt2',size=29),'right',y=-1.8,height=.5)
        self.takeaway('R acts on all trial coordinates. For a small eigenvector y, its eigenpair residual is Ry.')


class RrExample(RitzSlide):
    example=True
    def body(self):
        self.start()
        view=TrialPlane(); self.add(view,view.basis())
        matrix=Matrix([['2','1','1'],['1','2','-1'],['1','-1','5']],element_to_mobject=lambda v:math(v,size=29))
        for i,entry in enumerate(matrix.get_entries()):
            entry.set_color(TRIAL if i in [0,1,3,4] else RESID if i in [2,5,6,7] else MUTED)
        self.put(VGroup(math('A=',size=31,color=CURRENT),matrix).arrange(RIGHT,buff=.1),'right',y=1.05,height=2.2)
        self.beat()
        plus=trial_action(np.array([1,1])/np.sqrt(2)); minus=trial_action(np.array([1,-1])/np.sqrt(2))
        arrows=view.selection(plus[1],plus[2]); self.play(Create(arrows),run_time=1.5)
        self.put(formula((r'u_+=(1,1,0)^T/\sqrt2',TRIAL),size=28),'right',y=-.55,height=.5)
        self.put(formula((r'\theta_+=3',TRIAL),r',\quad',('r_+=0',RESID),size=31),'right',y=-1.1,height=.5)
        self.beat(); self.play(Transform(arrows,view.selection(minus[1],minus[2])),run_time=2)
        self.put(formula((r'u_-=(1,-1,0)^T/\sqrt2',TRIAL),size=27),'right',y=-1.6,height=.45)
        self.put(formula((r'\theta_-=1',TRIAL),r',\quad',(r'r_-=\sqrt2e_3',RESID),size=29),'right',y=-2.12,height=.45)
        self.takeaway('The sum direction cancels the escaping outputs; the difference direction reinforces them.')


class RrBlock(RitzSlide):
    example=True
    def body(self):
        self.start()
        view=TrialPlane(); self.add(view,view.basis())
        one=trial_action([1,0]); two=trial_action([0,1])
        self.add(view.arrow(one[1],CURRENT),view.arrow(two[1],CURRENT))
        blocks=Matrix([['B','C^T'],['C','D']],element_to_mobject=lambda v:math(v,size=35))
        for entry,color in zip(blocks.get_entries(),[TRIAL,RESID,RESID,MUTED]):entry.set_color(color)
        question=self.put(stack(tex('Where does a trial input send its output?',size=25),
                                formula(('AQ',CURRENT),'=',('QB',TRIAL),'+',('R',RESID),size=34),buff=.45),'right',y=.7,height=2)
        self.beat()
        self.remove(question)
        retained=VGroup(view.arrow(one[2],TRIAL),view.arrow(two[2],TRIAL))
        escapes=VGroup(view.arrow(one[1],RESID,start=one[2]),view.arrow(two[1],RESID,start=two[2]))
        self.play(Create(retained),Create(escapes),run_time=2)
        self.put(VGroup(math(r'[Q\ Q_\perp]^TA[Q\ Q_\perp]=',size=26),blocks).arrange(RIGHT,buff=.12),'right',y=1.0,height=2)
        self.put(tex('First block column: trial input, two output destinations.',size=24),'right',y=-.25,height=.8)
        self.play(Indicate(blocks.get_entries()[2],color=RESID),run_time=1)
        self.put(formula((r'C=(1\ \ -1)',RESID),r',\quad',(r'R=Q_\perp C',RESID),size=30),'right',y=-1.05,height=.6)
        self.beat()
        self.put(formula(r'\mathcal T\text{ invariant}\iff',('C=0',RESID),size=31),'right',y=-1.75,height=.55)
        self.takeaway('B keeps the in-plane output. C collects the normal components already drawn in green.')


class RrOrthogonality(RitzSlide):
    def body(self):
        self.start()
        view=TrialPlane(); self.add(view,view.basis())
        u,true,kept,escaping=trial_action([1,0])
        self.add(view.arrow(true,CURRENT),view.arrow(kept,TRIAL))
        green=view.arrow(true,RESID,start=kept); self.add(green)
        self.put(formula(('R',RESID),'=',('AQ',CURRENT),'-',('QB',TRIAL),size=34),'right',y=1.5,height=.7)
        self.beat()
        proof=self.put(stack(formula(('Q^TR',RESID),'=',('Q^TAQ',TRIAL),'-',('Q^TQB',TRIAL),size=29),
                             formula('=',('B',TRIAL),'-',('B',TRIAL),'=0',size=32),buff=.3),'right',y=.25,height=1.8)
        self.play(Indicate(green,color=RESID),run_time=1)
        self.beat()
        self.put(formula(('R',RESID),'=',('(I-P)AQ',RESID),r',\quad',('r=Ry',RESID),size=30),'right',y=-1.25,height=.7)
        self.takeaway(r'$Q^T R=0$: every residual is perpendicular to the trial space.')


class RrModel(RitzSlide):
    def body(self):
        self.start()
        origin=np.array([-5.4,-.9,0]); foot=origin+RIGHT*3.1; end=foot+UP*1.6
        full=Arrow(origin,end,buff=0,color=CURRENT,stroke_width=6)
        self.play(GrowArrow(full),run_time=1)
        self.add(tex('One trial input y',size=25).move_to([-3.8,1.9,0]))
        self.put(formula(('AQ-QM',CURRENT),size=34),'right',y=1.65,height=.7)
        self.beat()
        inside=Arrow(origin,foot,buff=0,color=TRIAL,stroke_width=6)
        outside=Arrow(foot,end,buff=0,color=RESID,stroke_width=6)
        self.play(GrowArrow(inside),GrowArrow(outside),run_time=1.5)
        self.add(RightAngle(Line(foot,origin),Line(foot,end),length=.2,color=RESID),
                 math(r'Q(B-M)y',size=28,color=TRIAL).move_to((origin+foot)/2+DOWN*.35),
                 math('Ry',size=28,color=RESID).move_to((foot+end)/2+RIGHT*.35))
        self.put(stack(formula(('AQ-QM',CURRENT),'=',('R',RESID),'+',('Q(B-M)',TRIAL),size=29),
                       tex('Changing M only adds an in-plane component.',size=25),buff=.4),'right',y=.35,height=1.8)
        self.beat()
        self.put(formula((r'\|AQ-QM\|_F^2',CURRENT),'=',(r'\|R\|_F^2',RESID),'+',(r'\|B-M\|_F^2',TRIAL),size=27),y=-1.85,height=.6)
        self.takeaway('Pythagoras: the added amber component cannot cancel the perpendicular green component.')


class RrQuality(RitzSlide):
    stage=2
    example=True
    def body(self):
        self.start()
        a,q,b,r=trial_example(); eigenvalues=np.linalg.eigvalsh(a)
        axes=NumberLine(x_range=[-1,6,1],length=10,include_numbers=True,font_size=23,color=MUTED).move_to([0,-.2,0])
        self.add(axes,tex('Exact eigenvalues',size=27).move_to([0,1.05,0]))
        for v in eigenvalues:self.add(Dot(axes.n2p(v),color=FG,radius=.065))
        theta=Dot(axes.n2p(1)+UP*.35,color=TRIAL)
        self.add(theta,math(r'\theta=1',size=28,color=TRIAL).next_to(theta,UP))
        self.put(formula(('u',TRIAL),'=',r'\sum_jc_jv_j',r',\quad Av_j=\lambda_jv_j',size=29),y=1.7,height=.6)
        self.beat()
        self.put(formula((r'\|r\|^2',RESID),'=',r'\sum_j|c_j|^2|\lambda_j-\theta|^2',size=31),y=-1.25,height=.65)
        self.beat()
        interval=Line(axes.n2p(1-np.sqrt(2))+DOWN*.35,axes.n2p(1+np.sqrt(2))+DOWN*.35,color=RESID,stroke_width=7)
        self.play(Create(interval),Create(Circle(radius=.13,color=RESID).move_to(axes.n2p(eigenvalues[0]))),run_time=1.5)
        self.put(formula(r'\min_j|\lambda_j-\theta|\le',(r'\|r\|=\sqrt2',RESID),size=31),y=-1.9,height=.6)
        self.takeaway('The green interval must contain some eigenvalue. It does not identify a chosen spectral target.')


class RrMinmax(RitzSlide):
    stage=2
    example=True
    def body(self):
        self.start()
        spaces=VGroup()
        for width,height,label in [(4.8,3.2,r'\mathbb R^3'),(3.4,2.1,r'\operatorname{span}(e_1,e_2)'),(1.7,.9,r'\operatorname{span}(e_1)')]:
            rectangle=RoundedRectangle(width=width,height=height,corner_radius=.12,color=TRIAL,fill_opacity=.035)
            rectangle.move_to([-3.4,.15,0])
            spaces.add(rectangle,math(label,size=23,color=TRIAL).move_to(rectangle.get_top()+DOWN*.25))
        self.add(spaces)
        self.put(stack(formula((r'\lambda_{\min}(B)',TRIAL),'=',r'\min_{u\in\mathcal T,\|u\|=1}u^TAu',size=29),
                       math(r'\mathcal T_1\subseteq\mathcal T_2\ \Longrightarrow\ \lambda_{\min}(B_1)\ge\lambda_{\min}(B_2)',size=25),buff=.45),'right',y=1,height=2)
        self.beat()
        values=[p[0] for p in nested_extrema()]
        number=NumberLine(x_range=[0,2.5,.5],length=4.9,include_numbers=True,font_size=20,color=MUTED).move_to([3.3,-.7,0])
        dot=Dot(number.n2p(values[0]),color=TRIAL)
        self.add(number,dot)
        self.play(dot.animate.move_to(number.n2p(values[1])),run_time=1.5)
        self.play(dot.animate.move_to(number.n2p(values[2])),run_time=1.5)
        self.put(formula('2',r'\longrightarrow','1',r'\longrightarrow',r'3-\sqrt6',size=29),'right',y=-1.55,height=.6)
        self.takeaway('More allowed directions can lower the minimum quotient: line, then plane, then the full space.')


class RrPaper(RitzSlide):
    stage=2
    def body(self):
        self.start()
        view=TrialPlane(); self.add(view,view.basis())
        u,true,kept,escaping=trial_action([1,0]); self.add(view.selection(true,kept))
        self.put(stack(formula(('Q',TRIAL),r'\longleftrightarrow',('E_0',TRIAL),size=35),
                       formula(('B',TRIAL),r'\longleftrightarrow',(r'A_0\ \text{(Ritz choice)}',TRIAL),size=29),
                       formula(('R',RESID),'=',(r'\widehat A E_0',CURRENT),'-',('E_0A_0',TRIAL),size=32),buff=.35),'right',y=.85,height=2.7)
        self.beat()
        self.put(boxed(formula((r'A_0=E_0^*\widehat A E_0',TRIAL),size=30),color=TRIAL),'right',y=-1.1,height=.8)
        self.put(tex('Other trial models are allowed in the general residual theorem.',size=23),'right',y=-1.9,height=.5)
        self.takeaway('For unbounded operators, retain domain inclusion and bounded-residual hypotheses.')


class RrSummary(RitzSlide):
    stage=3
    def body(self):
        self.start()
        labels=[('Search space',r'\mathcal T',TRIAL),('Coordinates','Q',TRIAL),('Small model','B=Q^TAQ',TRIAL),
                ('Ritz pair',r'By=\theta y',TRIAL),('Full error',r'r=Au-\theta u',RESID)]
        panels=VGroup()
        for i,(title,expression,color) in enumerate(labels):
            x=-5.2+i*2.6
            panel=RoundedRectangle(width=2.25,height=1.55,corner_radius=.12,color=color,fill_opacity=.06).move_to([x,.65,0])
            panels.add(panel,tex(title,size=25,color=color).move_to([x,1.05,0]),math(expression,size=25,color=color).move_to([x,.4,0]))
            if i:self.add(Arrow([x-1.45,.65,0],[x-1.15,.65,0],buff=0,color=MUTED))
        self.add(panels)
        self.beat()
        self.put(formula(('AQ',CURRENT),'=',('QB',TRIAL),'+',('R',RESID),r',\qquad',('Q^TR=0',RESID),size=36),y=-.9,height=.8)
        self.takeaway('The model keeps the amber component. The green residual records exactly what remains outside.')


class RrFacts(RitzSlide):
    stage=3
    def body(self):
        self.start()
        self.card(formula(('B',TRIAL),'=',('Q^T',TRIAL),('A',CURRENT),('Q',TRIAL),size=39),
                  formula(('Q^TR',RESID),'=0',size=39),
                  formula(('AQ-QM',CURRENT),'=',('R',RESID),'+',('Q(B-M)',TRIAL),size=35),
                  tex('Q is isometric; R is the Ritz residual.',size=28))
        self.takeaway('Compression, orthogonality, and the orthogonal splitting: the three facts to connect to Lean.')


class RrLean(LessonLean):
    stage_labels = RitzSlide.stage_labels
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
