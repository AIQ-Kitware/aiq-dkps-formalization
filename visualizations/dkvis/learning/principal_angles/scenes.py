"""From line angles to singular values and principal-plane error."""
import numpy as np
from manim import Arc, Line, ValueTracker, VGroup, always_redraw, linear
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.slide_style import CURRENT, TRIAL, WANTED, SINE, boxed, math, tex

class AngleSlide(LessonSlide):
    lesson_deck='prereq-principal-angles'
    stage_labels=('Compare spaces','Find directions','Measure error','Recap')
class PaTitle(LessonTitle):
    lesson_deck='prereq-principal-angles'
    title_lines=('Principal angles','Comparing whole subspaces')
    subtitle='The space stays the same when its basis changes.'
class PaLines(AngleSlide):
    example=True
    def body(self):
        self.start();axes=plane(extent=1.7);self.put(axes,'left',y=.2)
        a=.5;self.add(Line(axes.c2p(-2,0),axes.c2p(2,0),color=WANTED))
        self.add(Line(axes.c2p(-2*np.cos(a),-2*np.sin(a)),axes.c2p(2*np.cos(a),2*np.sin(a)),color=TRIAL))
        sign=ValueTracker(1);self.add(always_redraw(lambda:vector(axes,sign.get_value()*np.array([np.cos(a),np.sin(a)]),TRIAL)))
        self.put(stack(r'\cos\theta=|\langle u,v\rangle|',r'0\le\theta\le\pi/2',tex('Lines have no preferred sign.',size=30),buff=.5),'right',y=.4,height=3)
        self.beat();self.play(sign.animate.set_value(-1),run_time=2)
        self.takeaway('Reversing a spanning arrow does not move its line.')
class PaSeveral(AngleSlide):
    example=True
    def body(self):
        self.start();beta=ValueTracker(.6)
        left=plane(width=5,height=2.7,extent=1.5);right=plane(width=5,height=2.7,extent=1.5)
        self.put(left,'left',y=.15);self.put(right,'right',y=.15)
        for axes,label in [(left,r'\operatorname{span}(e_1,e_3)'),(right,r'\operatorname{span}(e_2,e_4)')]:
            self.add(vector(axes,[1,0],WANTED),math(label,size=27).move_to(axes.get_top()+np.array([0,.5,0])))
        self.add(vector(left,[np.cos(np.pi/9),np.sin(np.pi/9)],TRIAL),always_redraw(lambda:vector(right,[np.cos(beta.get_value()),np.sin(beta.get_value())],TRIAL)))
        self.add(Arc(radius=.42,start_angle=0,angle=np.pi/9,arc_center=left.c2p(0,0),color=TRIAL),
            always_redraw(lambda:Arc(radius=.42,start_angle=0,angle=beta.get_value(),arc_center=right.c2p(0,0),color=TRIAL)),
            math(r'\alpha=20^\circ',size=28,color=TRIAL).move_to([-3.25,-1.4,0]),
            math(r'\beta\text{ varies}',size=28,color=TRIAL).move_to([3.25,-1.4,0]))
        self.add(tex('Two coordinate slices of one 4-D example',size=26).move_to([0,-1.95,0]))
        self.beat();self.play(beta.animate.set_value(1.2),run_time=3,rate_func=linear)
        self.takeaway('One angle per paired direction; a single average can hide the worst error.')
class PaOverlap(AngleSlide):
    stage=1
    def body(self):
        self.start();self.put(stack(r'x=Qa\quad\longmapsto\quad Z^TQa',
            r'Z^TQ=UCV^T,\qquad C=\operatorname{diag}(\cos\theta_j)',
            boxed(math(r'(ZU)^T(QV)=C',size=37),color=CURRENT),
            tex('The new frames reveal aligned pairs and zero cross-pair overlap.',size=27),buff=.5),y=.4,height=3.7)
        self.takeaway('The SVD chooses useful bases inside the given spaces; it does not change the spaces.')
class PaError(AngleSlide):
    stage=2
    def body(self):
        self.start();axes=plane(extent=1.5);self.put(axes,'left',y=.3)
        a=.7;tip=[np.cos(a),np.sin(a)]
        self.add(vector(axes,tip,TRIAL),vector(axes,[tip[0],0],WANTED),Line(axes.c2p(tip[0],0),axes.c2p(*tip),color=SINE))
        self.put(stack(r'\|(I-P_L)q_j\|=\sin\theta_j',
            boxed(math(r'\|(I-P_L)Q\|_{\rm op}=\max_j\sin\theta_j',size=29),color=SINE),
            r'\|(I-P_L)Q\|_F^2=\sum_j\sin^2\theta_j',buff=.5),'right',y=.4,height=3.4)
        self.takeaway('The sine is missed perpendicular length, with unit input length held fixed.')
class PaBasis(AngleSlide):
    stage=2
    def body(self):
        self.start();self.put(stack(r'Q\mapsto QC,\quad Z\mapsto ZD\qquad(C,D\text{ orthogonal})',
            r'Z^TQ\mapsto D^T(Z^TQ)C',
            boxed(math(r'\sigma_j(D^T(Z^TQ)C)=\sigma_j(Z^TQ)',size=31),color=CURRENT),
            tex('Repeated angles need not determine unique principal vectors.',size=28),buff=.5),y=.4,height=3.6)
        self.takeaway('Angles are properties of the spaces, not the names of their basis columns.')
class PaSummary(AngleSlide):
    stage=3
    def body(self):
        self.start();self.put(stack(r'\cos\theta_j=\sigma_j(Z^TQ),\quad0\le\theta_1\le\cdots\le\theta_k\le\pi/2',
            r'\theta=0:\text{ common direction}\qquad\theta=\pi/2:\text{ perpendicular pair}',
            tex('Equal-dimensional spaces here; directed conventions matter beyond this setting.',size=27),
            tex('Keep the dimension when retaining zero cosine values.',size=28),buff=.5),y=.4,height=3.5)
        self.takeaway('Use the largest sine for worst-direction error and the sum of squared sines for Frobenius error.')
class PaFacts(AngleSlide):
    stage=3
    def body(self):
        self.start();self.put(stack(r'c_i(U,V):\text{ principal cosine data}',
            boxed(math(r'0\le c_i(U,V)\le1',size=40),color=CURRENT),
            r'c(U,V)=c(V,U)',tex('Lean represents this data as a finite-support function padded with zeros.',size=27),buff=.5),y=.4,height=3.6)
        self.takeaway('The companion uses cosines; it does not conflate different directed angle conventions.')
class PaLean(LessonLean):
    lesson_deck='prereq-principal-angles';lecture_id='principal_angles'
    symbolic_facts=(('Cosine bounds',r'0\le c_i(U,V)\le1'),('Exchange symmetry',r'c(U,V)=c(V,U)'))
    assumptions='Finite-dimensional real inner product space; U and V are subspaces.'
    ownership='Tau Ceti Projection/PrincipalAngle: principalCosines bounds and symmetry.'
    notation=r'\texttt{principalCosines} is the zero-padded singular-value data of $P_VP_U$.'
class PaLeanSymmetry(PaLean):fact_index=1
class PaComputation(AngleSlide):
    bonus=True
    def body(self):
        self.start();self.put(stack(tex('Orthonormalize first: QR, then SVD of the frame overlap.',size=29),
            r'Q=\operatorname{orth}(A),\quad Z=\operatorname{orth}(B),\quad\theta_j=\arccos\sigma_j(Z^TQ)',
            tex('Near zero angles, inspect the perpendicular residual for sine information.',size=27),
            tex('Tiny roundoff excursions may be clamped; substantial violations need diagnosis.',size=26),buff=.5),y=.4,height=3.5)
        self.takeaway('Raw scaled columns do not supply cosine data.')
