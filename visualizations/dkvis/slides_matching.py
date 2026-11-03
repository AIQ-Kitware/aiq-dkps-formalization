"""Theorem 5 as a sequence of inferences, with separately authored narration."""
from __future__ import annotations

import numpy as np
from manim import (
    Arc, Arrow, Axes, Circle, Create, DashedLine, Dot, DOWN, LEFT, Line,
    Rectangle, RIGHT, Rotate, Transform, UP, VGroup,
)

from dkvis.matching_math import (
    paired_power_cost, pair_parameters, phase_derivative,
    phase_level_roots, phase_rectangle_edge,
)
from dkvis.matching_narration import read_narration
from dkvis.novelty_math import nuclear_matching_graph_example
from dkvis.slide_style import (
    CURRENT, FAINT, FG, GAP, MUTED, RESID, SINE, TRIAL, WANTED,
    DeckSlide, boxed, math, para, tex,
)

SCRIPTS = read_narration()


def column(*items, size=32, buff=.22):
    return VGroup(*(math(item, size=size) if isinstance(item, str) else item
                    for item in items)).arrange(DOWN, buff=buff)


def card(label, color=FG, size=30):
    return boxed(math(label, size=size), color=color, pad=.18)


def block_matrix(labels, *, color=RESID):
    group = VGroup()
    for i, row in enumerate(labels):
        for j, label in enumerate(row):
            cell = Rectangle(width=1.8, height=1.03, stroke_color=FAINT,
                             fill_opacity=.06, fill_color=color)
            cell.move_to([(j-.5)*1.8, (.5-i)*1.03, 0])
            text = math(label, size=32, color=color)
            if text.width > 1.62:
                text.scale_to_fit_width(1.62)
            group.add(cell, text.move_to(cell))
    return group


def principal_plane(theta=.7, label=None):
    origin = Dot([0,0,0], radius=.035, color=FG)
    u = Line([-1.3,0,0],[1.3,0,0], color=TRIAL, stroke_width=4)
    direction = np.array([np.cos(theta), np.sin(theta), 0])
    v = Line(-1.3*direction, 1.3*direction, color=WANTED, stroke_width=4)
    group = VGroup(origin,u,v, Arc(radius=.52, angle=theta, color=SINE),
                   math(r"\like{Usource}{K}",size=26).move_to([1.45,-.18,0]),
                   math(r"\like{Vtarget}{L}",size=26).move_to(1.5*direction+UP*.1),
                   math(r"\theta",size=26,color=SINE).move_to([.66,.22,0]))
    if label:
        group.add(tex(label,size=24,color=MUTED).next_to(group,DOWN,buff=.16))
    return group


def graph_example(*, selected=True):
    ex = nuclear_matching_graph_example()
    points = np.array([[-1.7,.7,0],[1.7,.7,0],[0,-1.05,0]])
    graph = VGroup()
    positions = {(0,1):[0,1.,0],(0,2):[-1.15,-.35,0],(1,2):[1.15,-.35,0]}
    chosen = VGroup()
    for (i,j), weight in ex['savings'].items():
        graph.add(DashedLine(points[i],points[j],color=FAINT))
        graph.add(math(f"{weight:+.4f}",size=25,color=CURRENT).move_to(positions[i,j]))
        if selected and (i,j) in ex['pairs']:
            chosen.add(Line(points[i],points[j],color=CURRENT,stroke_width=6))
    for i,(point,angle) in enumerate(zip(points,ex['angles_deg'])):
        graph.add(Dot(point,color=SINE,radius=.07),
                  math(rf"{i+1}:\ {angle:.0f}^\circ",size=28,color=SINE).next_to(
                      Dot(point), UP if i<2 else DOWN,buff=.18))
    return VGroup(graph,chosen), chosen


class MatchingSlide(DeckSlide):
    section = "Real trace-norm matching"
    wait_time_between_slides = .6

    def make_chrome(self):
        self.title = SCRIPTS[type(self).__name__].title
        return super().make_chrome()

    def start(self, inference, justification):
        self.say(SCRIPTS[type(self).__name__].text)
        top = para(r"\textbf{Inference.} "+inference,width=12.2,size=26)
        top.move_to([0,self.content_top-.35,0])
        if top.height > .8:
            raise ValueError(f"inference is too long: {type(self).__name__}")
        reason = para(r"\textbf{Justification.} "+justification,width=12.2,size=23)
        if reason.height > .95:
            raise ValueError(f"justification is too long: {type(self).__name__}")
        reason.move_to([0,-2.76,0])
        self.add(top,reason)

    def put(self,mob,side="full"):
        width = 12.2 if side=="full" else 5.7
        factor = min(1,width/mob.width,3.35/mob.height)
        if factor < .56:
            raise ValueError(f"content too dense in {type(self).__name__}: {factor:.2f}")
        mob.scale(factor).move_to([{"full":0,"left":-3.23,"right":3.23}[side],-.13,0])
        self.add(mob)
        return mob


class M00Problem(MatchingSlide):
    kicker = "Goal: a finite real transport problem"
    def body(self):
        self.start("Find the smallest full trace displacement of an orthogonal transporter.",
                   "Only the image subspace is prescribed; all ambient orthogonal competitors are allowed.")
        self.put(principal_plane(label="source and target"),"left")
        self.put(column(r"K,L\subseteq\mathbb R^n,\quad\dim K=\dim L",
                        r"W^TW=I,\qquad W(K)=L",
                        r"\mathrm{OPT}=\min_W\|I-W\|_1",
                        tex("Trace norm = sum of singular values",size=25)),"right")


class M01PrincipalPlanes(MatchingSlide):
    kicker = "Geometry: decompose the subspaces before studying the optimizer"
    def body(self):
        self.start("Positive principal angles give mutually orthogonal real planes.",
                   "The SVD diagonalizes source--target overlaps. This does not yet constrain the minimizing W.")
        planes=VGroup(principal_plane(.45,"first principal plane"),
                      principal_plane(.9,"second principal plane")).arrange(RIGHT,buff=.65)
        self.put(planes,"left")
        self.put(column(r"\langle u_i,v_j\rangle=\delta_{ij}\cos\theta_i",
                        r"q_i=\frac{v_i-\cos\theta_i\,u_i}{\sin\theta_i}",
                        r"\Pi_i=\operatorname{span}(u_i,q_i)",
                        r"\Pi_i\perp\Pi_j\quad(i\ne j)",size=30),"right")


class M02Singleton(MatchingSlide):
    kicker = "Local construction: one angle, two determinant classes"
    def body(self):
        self.start("A singleton chooses the cheaper of a rotation and a reflection.",
                   "A rotation has two equal displacement singular values; a reflection has values 0 and 2.")
        self.put(principal_plane(.9,label="unoriented source and target lines"),"left")
        self.put(column(tex("Rotation",size=29,color=WANTED),r"4\sin(\theta_i/2)",
                        tex("Reflection",size=29,color=TRIAL),r"2",
                        card(r"s_i=\min\{4\sin(\theta_i/2),2\}",CURRENT,size=29),buff=.12),"right")


class M03PairedBlock(MatchingSlide):
    kicker = "Local construction: a block diagram of four real dimensions"
    def body(self):
        self.start("Two principal planes can interact within one four-dimensional block.",
                   "The paired construction rotates a different invariant plane and fixes its orthogonal complement.")
        left=column(card(r"\Pi_i\oplus\Pi_j\cong\mathbb R^4",SINE),
                    math(r"\Downarrow"),
                    VGroup(card(r"R_{\theta_i+\theta_j}",WANTED),card(r"I_2",MUTED)).arrange(RIGHT,buff=.3),
                    tex("Moving plane + fixed plane",size=26))
        self.put(left,"left")
        self.put(column(r"s(I-W_{ij})=",
                        r"\bigl(2\sin h,2\sin h,0,0\bigr)",
                        r"h=(\theta_i+\theta_j)/2",
                        card(r"e_{ij}=4\sin h",CURRENT)),"right")


class M04Graph(MatchingSlide):
    kicker = "Finite general graph: each label belongs to at most one edge"
    def body(self):
        self.start("Pair choices form a maximum-weight matching problem.",
                   r"Selecting edge $\{i,j\}$ replaces singleton costs $s_i+s_j$ by $e_{ij}$; shared endpoints are disallowed.")
        graph,chosen=graph_example()
        self.put(graph,"left")
        self.put(column(r"g_{ij}=s_i+s_j-e_{ij}",
                        r"C(M)=\sum_i s_i-\sum_{\{i,j\}\in M}g_{ij}",
                        r"M=\{\{1,2\}\},\quad 3\ \text{unmatched}",
                        tex("An empty matching is allowed",size=25),size=30),"right")
        self.remove(chosen)
        self.play(Create(chosen),run_time=1.)


class M05TwoBounds(MatchingSlide):
    kicker = "Proof plan: construction and global optimality are separate"
    def body(self):
        self.start("We need both inequalities to identify the unrestricted minimum.",
                   "A block construction gives an upper bound. The converse must rule out improvement by unrestricted mixing.")
        self.put(column(tex("Construct from a matching",size=28,color=WANTED),
                        r"M\longmapsto W_M",
                        card(r"\mathrm{OPT}\le\min_M C(M)",WANTED),size=32),"left")
        self.put(column(tex("Analyze a global minimizer",size=28,color=TRIAL),
                        r"W_*\longmapsto\text{small blocks}\longmapsto M_*",
                        card(r"\mathrm{OPT}\ge\min_M C(M)",TRIAL),size=29),"right")


class M06SmoothCost(MatchingSlide):
    kicker = "Step 1: work with a differentiable auxiliary objective"
    def body(self):
        self.start("Replace the trace norm by a smooth power cost for $1<p<2$.",
                   "The matrix power sum is differentiable for p>1, including zero singular values; return to p=1 by a limit.")
        ax=Axes(x_range=[-1.5,1.5,1],y_range=[0,2,.5],x_length=5,y_length=2.5,
                axis_config={"color":MUTED,"include_tip":False})
        curves=VGroup(ax,ax.plot(lambda t:abs(t),color=MUTED),
                      ax.plot(lambda t:abs(t)**1.5,color=CURRENT),
                      math("t",size=23).next_to(ax.x_axis,RIGHT,buff=.12))
        self.put(column(curves,math(r"|t|\quad\text{and}\quad|t|^{3/2}",size=27)),"left")
        self.put(column(r"\Phi_p(W)=\sum_j s_j(I-W)^p",
                        r"1<p<2",
                        tex("A new minimizer for each p",size=27),
                        tex("Later: p approaches 1 from above",size=25),size=32),"right")


class M07Existence(MatchingSlide):
    kicker = "Step 1(a): compactness permits choosing an actual minimizer"
    def body(self):
        self.start("The smooth cost attains a global minimum on the feasible set.",
                   "Extend orthonormal bases for nonemptiness; use closedness, boundedness, and continuity for attainment.")
        self.put(column(r"\mathcal F=\{W\in O(n):WPW^T=Q\}",
                        VGroup(card(r"\mathcal F\ne\varnothing",WANTED),
                               card(r"\mathcal F\ \text{compact}",TRIAL),
                               card(r"\Phi_p\ \text{continuous}",CURRENT)).arrange(RIGHT,buff=.5),
                        math(r"\Downarrow"),r"\exists W_*\in\mathcal F:\ \Phi_p(W_*)=\min_{\mathcal F}\Phi_p"))


class M08FeasibleCurves(MatchingSlide):
    kicker = "Step 2(a): rotate within the source and its complement"
    def body(self):
        self.start(r"Skew B commuting with P gives a feasible curve $W\exp(tB)$.",
                   "The exponential and its inverse are orthogonal and preserve K, so composition still carries K onto L.")
        self.put(column(block_matrix([[r"B_{00}","0"],["0",r"B_{11}"]],color=TRIAL),
                        tex(r"Coordinates: $K\oplus K^\perp$",size=25)),"left")
        self.put(column(r"B^T=-B,\qquad BP=PB",
                        r"\exp(tB)^T=\exp(-tB)",
                        r"\exp(tB)K=K",
                        r"W\exp(tB)K=L",size=32),"right")


class M09RotationCost(MatchingSlide):
    kicker = "Step 2(b): a rotation contributes two chord singular values"
    def body(self):
        self.start("A real rotation plane contributes $2f_p(t)$ to the power cost.",
                   "Every unit vector has chord displacement 2 sin(t/2); the plane supplies two singular values.")
        origin=Dot(radius=.03,color=FG)
        reference=Arrow([0,0,0],[1.3,0,0],buff=0,color=FG)
        image=Arrow([0,0,0],[1.3,0,0],buff=0,color=WANTED)
        diagram=VGroup(Circle(radius=1.3,color=FAINT),origin,reference,image)
        self.put(diagram,"left")
        self.put(column(r"(I-R_t)^T(I-R_t)=4\sin^2(t/2)I_2",
                        r"f_p(t)=(2\sin(t/2))^p",
                        card(r"\Phi_p(R_t)=2f_p(t)",CURRENT),size=30),"right")
        self.play(Rotate(image,angle=np.pi/3,about_point=origin.get_center()),run_time=1.4)
        chord=Line(image.get_end(),reference.get_end(),color=RESID,stroke_width=5)
        self.play(Create(chord),run_time=.6)
        self.add(math("x",size=25).next_to(reference.get_end(),DOWN,buff=.1),
                 math(r"R_t x",size=25,color=WANTED).next_to(image.get_end(),UP,buff=.12),
                 Arc(radius=.45,angle=np.pi/3,color=SINE).shift(origin.get_center()),
                 math("t",size=24,color=SINE).move_to(origin.get_center()+[.58,.25,0]),
                 math(r"2\sin(t/2)",size=25,color=RESID).next_to(chord,RIGHT,buff=.16))


class M10SignAverage(MatchingSlide):
    kicker = "Step 2(b): justify the derivative for directions that mix planes"
    def body(self):
        self.start("Averaging sign conjugations removes off-diagonal blocks of B without changing the derivative.",
                   "The first variation is linear; block sign changes commute with W and preserve displacement singular values.")
        before=block_matrix([[r"B_{00}",r"B_{01}"],[r"B_{10}",r"B_{11}"]])
        after=block_matrix([[r"B_{00}","0"],["0",r"B_{11}"]])
        self.put(before,"left")
        self.put(column(r"S=\operatorname{diag}(I,-I)",
                        r"\mathcal L(SBS)=\mathcal L(B)",
                        r"\mathcal L(B)=\mathcal L\left(\frac{B+SBS}{2}\right)",
                        tex("Repeat signs independently for all blocks",size=24),size=30),"right")
        after.scale(before.width/after.width).move_to(before)
        self.play(Transform(before,after),run_time=1.3)


class M11TracePairing(MatchingSlide):
    kicker = "Step 2(b): identify G, including the sign and factor two"
    def body(self):
        self.start(r"The general first variation is $-\operatorname{tr}(GB)$.",
                   "After sign averaging, compute on each rotation plane and add; scalar lines have zero diagonal skew direction.")
        self.put(column(r"J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}",
                        r"B_{aa}=bJ_0,\qquad G_{aa}=f'_p(\theta)J_0",
                        r"J_0^2=-I_2",size=31),"left")
        self.put(column(r"\frac{d}{dt}\,2f_p(\theta+tb)\Big|_{t=0}=2bf'_p(\theta)",
                        r"-\operatorname{tr}(G_{aa}B_{aa})=2bf'_p(\theta)",
                        card(r"\frac{d}{dt}\Phi_p(We^{tB})\Big|_0=-\operatorname{tr}(GB)",RESID,size=29),size=29),"right")


class M12Stationarity(MatchingSlide):
    kicker = "Step 2(c): test the gradient with its own source compression"
    def body(self):
        self.start("Stationarity forces both diagonal source blocks of G to vanish.",
                   "Choose B=PGP; it is feasible and -tr(B squared) is its squared Frobenius norm. Repeat on the complement.")
        grid=block_matrix([[r"G_{00}",r"G_{01}"],[r"-G_{01}^T",r"G_{11}"]])
        self.put(grid,"left")
        self.put(column(r"B=PGP",
                        r"0=-\operatorname{tr}(GB)=-\operatorname{tr}(B^2)=\|B\|_F^2",
                        r"J=2P-I,\qquad JGJ=-G",size=31),"right")
        zero=block_matrix([["0",r"G_{01}"],[r"-G_{01}^T","0"]])
        zero.scale(grid.width/zero.width).move_to(grid)
        self.play(Transform(grid,zero),run_time=1.2)


class M13TwoDecompositions(MatchingSlide):
    kicker = "Checkpoint: the two coordinate systems have different jobs"
    def body(self):
        self.start("W's rotation planes and the source decomposition need not coincide.",
                   "The equations GW=WG and JGJ=-G connect them; neither equation assumes W preserves the original principal planes.")
        self.put(column(tex("Rotation-plane coordinates of W",size=28,color=WANTED),
                        block_matrix([[r"R_{\theta_a}","0"],["0",r"R_{\theta_b}"]],color=WANTED),
                        r"G_{aa}=f'_p(\theta_a)J_0",size=29),"left")
        self.put(column(tex("Source coordinates",size=28,color=TRIAL),
                        block_matrix([["0",r"G_{01}"],[r"-G_{01}^T","0"]]),
                        r"K\oplus K^\perp",size=29),"right")


class M14GradientLevels(MatchingSlide):
    kicker = "Step 3(a): first find simultaneous invariant spaces"
    def body(self):
        self.start("Eigenspaces of $-G^2$ are preserved by W, P, and Q.",
                   "The square commutes with both W and J; commuting operators preserve its eigenspaces, and Q=WPW transpose.")
        self.put(column(r"\langle-G^2x,x\rangle=\|Gx\|^2\ge0",
                        r"GW=WG,\quad JGJ=-G",
                        r"[G^2,W]=[G^2,J]=0",size=32),"left")
        self.put(column(VGroup(card(r"V_{g_1}",RESID),card(r"V_{g_2}",RESID),
                               card(r"\ker G",MUTED)).arrange(RIGHT,buff=.25),
                        r"-G^2|_{V_g}=g^2I",
                        r"P=(I+J)/2,\qquad Q=WPW^T",size=30),"right")


class M15ComplexCoordinates(MatchingSlide):
    kicker = "Step 3(a): normalize a positive gradient level"
    def body(self):
        self.start(r"On $V_g$ with g>0, $\mathcal I_g=G/g$ acts as multiplication by i.",
                   "Its square is -I and it preserves lengths; W commutes with it, while the source reflection reverses it.")
        center=Dot(radius=.03,color=FG)
        x=Arrow([0,0,0],[1.2,0,0],buff=0,color=RESID)
        guide=VGroup(Circle(radius=1.2,color=FAINT),
                     Line([-1.4,0,0],[1.4,0,0],color=MUTED),
                     Line([0,-1.4,0],[0,1.4,0],color=MUTED),center,x)
        self.put(guide,"left")
        self.put(column(r"\mathcal I_g^2=-I",
                        r"(a+ib)x=ax+b\mathcal I_gx",
                        r"W\mathcal I_g=\mathcal I_gW",
                        r"J\mathcal I_g=-\mathcal I_gJ",size=31),"right")
        self.play(Rotate(x,np.pi/2,about_point=center.get_center()),run_time=1.)
        self.play(Rotate(x,np.pi/2,about_point=center.get_center()),run_time=1.)


class M16TwoPhases(MatchingSlide):
    kicker = "Step 3(b): a scalar equation limits the possible phases"
    def body(self):
        self.start("A positive gradient level has at most two eigenphases of W.",
                   "The derivative f prime rises then falls once, so a positive horizontal level meets it at most twice.")
        ax=Axes(x_range=[0,np.pi,1],y_range=[0,1.5,.5],x_length=5,y_length=2.5,
                axis_config={"color":MUTED,"include_tip":False})
        roots=phase_level_roots(1.5,.8)
        diagram=VGroup(ax,ax.plot(lambda t:float(phase_derivative(t,1.5)),color=RESID),
                       DashedLine(ax.c2p(0,.8),ax.c2p(np.pi,.8),color=GAP),
                       math("t",size=23).next_to(ax.x_axis,RIGHT,buff=.1),
                       math(r"f'_p(t)",size=23,color=RESID).next_to(ax.y_axis,UP,buff=.1),
                       math("g",size=23,color=GAP).next_to(ax.c2p(0,.8),LEFT,buff=.12))
        for t in roots:
            diagram.add(Dot(ax.c2p(t,.8),color=SINE))
        self.put(column(diagram,math(r"p=3/2,\quad f'_p(t)=g",size=26)),"left")
        self.put(column(r"f'_p(t)=p(2\sin(t/2))^{p-1}\cos(t/2)",
                        r"f''_p(t)=0\ \Longleftrightarrow\ \tan^2(t/2)=p-1",
                        r"W=e^{i\varphi_1}E+e^{i\varphi_2}(I-E)",
                        tex("Multiplicity still requires a block argument",size=24),size=29),"right")


class M17ProjectionBlocks(MatchingSlide):
    kicker = "Step 3(c): preserve the phase projection and conjugation together"
    def body(self):
        self.start("Real and imaginary parts of E split coordinate space into invariant lines or planes.",
                   "Y pairs an X-eigenvector at lambda with one at 1-lambda; normalize Yu, then repeat on the orthogonal complement.")
        nodes=VGroup(card(r"Xu=\lambda u"),card(r"Xv=(1-\lambda)v")).arrange(RIGHT,buff=1.1)
        arrow=Arrow(nodes[0].get_right(),nodes[1].get_left(),buff=.1,color=RESID)
        diagram=column(VGroup(nodes,arrow),r"Yu=\eta v,\quad Yv=-\eta u",
                       r"\eta=\sqrt{\lambda(1-\lambda)}",size=29)
        self.put(diagram,"left")
        self.put(column(r"E=X+iY,\quad X^T=X,\quad Y^T=-Y",
                        r"X^2-Y^2=X,\qquad XY+YX=Y",
                        r"0<\lambda<1:\ \operatorname{span}_{\mathbb R}(u,v)",
                        r"\lambda=0,1:\ Yu=0",size=29),"right")


class M18RealBlocks(MatchingSlide):
    kicker = "Step 3(c): convert complex-coordinate dimensions back to real dimensions"
    def body(self):
        self.start("The simultaneous real blocks carry one or two angle entries.",
                   "Complexifying a real coordinate line or plane gives real dimension two or four; J fixes half the dimensions.")
        line=VGroup(card(r"\mathbb C",RESID),math(r"\longrightarrow"),
                    card(r"\mathbb R^2",WANTED),math(r"\longrightarrow"),
                    card(r"\theta_i",SINE)).arrange(RIGHT,buff=.4)
        plane=VGroup(card(r"\mathbb C^2",RESID),math(r"\longrightarrow"),
                     card(r"\mathbb R^4",WANTED),math(r"\longrightarrow"),
                     card(r"\theta_i,\theta_j",SINE)).arrange(RIGHT,buff=.4)
        self.put(column(line,plane,r"E,J\ \Longrightarrow\ W,P,Q\ \text{preserve each block}",buff=.42))


class M19ZeroGradient(MatchingSlide):
    kicker = "Step 3(d): do not divide by the zero level"
    def body(self):
        self.start("The kernel of G contributes fixed lines and one-angle planes.",
                   "There W is a reflection. Two-projection geometry gives small blocks; a needless -1 line contradicts global minimality.")
        self.put(column(r"G=0\ \Longrightarrow\ W=I-2N",
                        r"N:\text{ projection onto the }-1\text{ eigenspace}",
                        r"\text{Common blocks for }P,N\text{ also preserve }W,Q",size=29),"left")
        self.put(column(card(r"W|_\ell=-1\quad\text{cost }2^p",TRIAL),
                        math(r"\Downarrow"),
                        card(r"W|_\ell=+1\quad\text{cost }0",WANTED),
                        tex("Same source and target on this invariant line",size=23)),"right")


class M20PairCoordinates(MatchingSlide):
    kicker = "Step 4(b): source-adapted coordinates parametrize all pair competitors"
    def body(self):
        self.start(r"Every transporter on a two-angle block is $D\operatorname{diag}(U_0,U_1)$.",
                   "Multiplying by D transpose preserves the source, hence its complement. The free factors may mix principal planes.")
        self.put(column(block_matrix([["C","-S"],["S","C"]],color=SINE),
                        r"D,\quad C=\operatorname{diag}(\cos\theta_i,\cos\theta_j)",
                        r"S=\operatorname{diag}(\sin\theta_i,\sin\theta_j)",size=27),"left")
        self.put(column(r"W=D\begin{pmatrix}U_0&0\\0&U_1\end{pmatrix}",
                        r"U_0,U_1\in O(2)",
                        tex(r"Coordinates: $K$ then $K^\perp$",size=26),
                        r"\det W=(\det U_0)(\det U_1)",size=31),"right")


class M20PhaseParameters(MatchingSlide):
    kicker = "Step 4(b): use half-sums of the free-factor angles"
    def body(self):
        self.start("Both positive-determinant cases have explicit cosine parameters x and y.",
                   "The two free factors have the same determinant: both rotations, or both rotations composed with a reflection.")
        self.put(column(r"h=(\theta_i+\theta_j)/2,\quad d=|\theta_i-\theta_j|/2",
                        r"\theta_i\ge\theta_j,\quad u=\cos x,\quad v=\cos y",
                        r"U_0=R_{r+s},\quad U_1=R_{r-s}",
                        card(r"u=\cos h\cos s,\quad v=\cos d\cos r",SINE,size=27),
                        tex("Both factors are rotations",size=25),size=27),"left")
        self.put(column(r"J_2=\operatorname{diag}(1,-1)",
                        r"U_0=R_{r+s}J_2,\quad U_1=R_{r-s}J_2",
                        card(r"u=-\sin d\cos r,\quad v=\sin h\cos s",SINE,size=27),
                        tex("Both factors are reflections",size=25),size=27),"right")


class M20PhasePolynomial(MatchingSlide):
    kicker = "Step 4(b): traces identify the eigenphases without choosing eigenvectors"
    def body(self):
        self.start(r"The four eigenvalues are $e^{\pm i(x+y)}$ and $e^{\pm i(x-y)}$.",
                   "Block multiplication gives the two traces; orthogonality and determinant one fix the reciprocal polynomial. Factor it.")
        self.put(column(r"\operatorname{tr}W=4uv,\quad\operatorname{tr}(W^2)=16u^2v^2-8(u^2+v^2)+4",
                        r"c_2=\frac{(\operatorname{tr}W)^2-\operatorname{tr}(W^2)}2=4(u^2+v^2)-2",
                        r"\chi_W(z)=z^4-4uvz^3+\bigl(4(u^2+v^2)-2\bigr)z^2-4uvz+1",
                        r"\phantom{\chi_W(z)}=\prod_{\varepsilon=\pm1}\left(z^2-2\cos(x+\varepsilon y)z+1\right)",
                        tex(r"Here $u=\cos x$ and $v=\cos y$",size=24),size=28,buff=.2))


class M20RectangleBounds(MatchingSlide):
    kicker = "Step 4(b): cosine bounds place both determinant-one cases in one rectangle"
    def body(self):
        self.start(r"Both cases satisfy $h\le x\le\pi-h$ and $d\le y\le\pi-d$.",
                   r"Cosine decreases on $[0,\pi]$. The reflection intervals fit inside the rotation rectangle because $h+d\le\pi/2$.")
        h,d=np.pi/4,np.pi/12
        ax=Axes(x_range=[0,3.2,1],y_range=[0,3.2,1],x_length=3.8,y_length=2.65,
                axis_config={"color":MUTED,"include_tip":False})
        def rectangle(x0,x1,y0,y1,color):
            pts=[ax.c2p(x0,y0),ax.c2p(x1,y0),ax.c2p(x1,y1),ax.c2p(x0,y1)]
            return VGroup(*(Line(pts[i],pts[(i+1)%4],color=color) for i in range(4)))
        self.put(VGroup(ax,rectangle(h,np.pi-h,d,np.pi-d,SINE),
                        rectangle(np.pi/2-d,np.pi/2+d,np.pi/2-h,np.pi/2+h,RESID),
                        math("x",size=23).next_to(ax.x_axis,RIGHT,buff=.1),
                        math("y",size=23).next_to(ax.y_axis,UP,buff=.1)),"left")
        self.put(column(tex("Both rotations",size=27,color=SINE),
                        r"|\cos x|\le\cos h,\quad|\cos y|\le\cos d",
                        tex("Both reflections",size=27,color=RESID),
                        r"\pi/2-d\le x\le\pi/2+d",
                        r"\pi/2-h\le y\le\pi/2+h",size=28,buff=.22),"right")


class M21PhaseRectangle(MatchingSlide):
    kicker = "Step 4(b): compare both phases with an attainable edge point"
    def body(self):
        self.start(r"Every positive-determinant phase point is no cheaper than a point $(h,\tau)$.",
                   r"Choose $\tau=\max(d,h-|x-y|)$. Both new folded phases are no larger; $f_p$ is increasing on $[0,\pi]$.")
        h,d=np.pi/4,np.pi/12
        x,y,tau=phase_rectangle_edge(1.2,.9,h,d)
        ax=Axes(x_range=[0,3.2,1],y_range=[0,3.2,1],x_length=3.8,y_length=2.65,
                axis_config={"color":MUTED,"include_tip":False})
        corners=[ax.c2p(h,d),ax.c2p(np.pi-h,d),ax.c2p(np.pi-h,np.pi-d),ax.c2p(h,np.pi-d)]
        rect=VGroup(*(Line(corners[i],corners[(i+1)%4],color=FAINT) for i in range(4)))
        edge=Line(ax.c2p(h,d),ax.c2p(h,h),color=CURRENT,stroke_width=6)
        start=Dot(ax.c2p(x,y),color=SINE)
        end=Dot(ax.c2p(h,tau),color=CURRENT)
        picture=VGroup(ax,rect,edge,start,end,DashedLine(start.get_center(),end.get_center(),color=MUTED),
                       math("x",size=23).next_to(ax.x_axis,RIGHT,buff=.1),
                       math("y",size=23).next_to(ax.y_axis,UP,buff=.1),
                       math("(x,y)",size=23,color=SINE).next_to(start,RIGHT,buff=.15),
                       math(r"(h,\tau)",size=23,color=CURRENT).next_to(end,LEFT,buff=.15))
        self.put(picture,"left")
        self.put(column(r"h\le x\le\pi-h,\quad d\le y\le\pi-d",
                        r"d\le\tau\le h",
                        r"h+\tau\le x+y",
                        r"h-\tau\le|x-y|",size=31),"right")
        self.play(start.animate.move_to(end.get_center()),run_time=1.4)


class M22PairMinimum(MatchingSlide):
    kicker = "Step 4(b): the edge bound is attained by an explicit transporter"
    def body(self):
        self.start("The paired power cost is a minimum over one closed scalar interval.",
                   r"Set $U_0=U_1=R_\gamma$ with $\cos\gamma=\cos\tau/\cos d$; this realizes $x=h$, $y=\tau$ for every $\tau\in[d,h]$.")
        theta,psi=np.radians([80.,65.]); h,d=pair_parameters(theta,psi)
        ts=np.linspace(d,h,201); values=paired_power_cost(theta,psi,ts,1.5)
        low,high=float(min(values))-.15,float(max(values))+.15
        ax=Axes(x_range=[0,h,.4],y_range=[low,high,.2],x_length=5,y_length=2.5,
                axis_config={"color":MUTED,"include_tip":False},tips=False)
        curve=ax.plot(lambda t:float(paired_power_cost(theta,psi,t,1.5)),x_range=[d,h],color=CURRENT)
        diagram=VGroup(ax,curve,
                       math(r"\tau",size=23).next_to(ax.x_axis,RIGHT,buff=.1),
                       tex("paired cost",size=22,color=CURRENT).next_to(ax.y_axis,UP,buff=.1))
        self.put(column(diagram,math(r"p=3/2,\quad(\theta_i,\theta_j)=(80^\circ,65^\circ)",size=25)),"left")
        self.put(column(r"b_{ij}(p)=\min_{d\le\tau\le h}",
                        r"2\bigl(f_p(h+\tau)+f_p(h-\tau)\bigr)",
                        r"\gamma=\arccos(\cos\tau/\cos d)",
                        tex("Continuity + a compact interval = attainment",size=23),size=30),"right")


class M23Determinants(MatchingSlide):
    kicker = "Step 4(c): account for both determinant classes"
    def body(self):
        self.start("An unrestricted pair block chooses a paired cost or two singletons.",
                   "The negative class is minimized by a reflection on the larger-angle plane and rotation on the smaller-angle plane.")
        self.put(column(r"\det W=-1:\quad 1,-1,e^{it},e^{-it}",
                        r"|\operatorname{tr}W|\le2\cos\theta_j",
                        r"t\ge\theta_j\quad(\theta_i\ge\theta_j)",
                        r"\text{cost}\ge2^p+2f_p(\theta_j)",size=29),"left")
        self.put(column(tex("Compare all local choices",size=29),
                        r"\text{paired positive class}:\ b_{ij}(p)",
                        r"\text{independent choices}:\ a_i(p)+a_j(p)",
                        card(r"\min\{b_{ij}(p),a_i(p)+a_j(p)\}",CURRENT,size=29),size=29),"right")


class M24BlockOptimality(MatchingSlide):
    kicker = "Step 5(b): global minimality is stronger than stationarity"
    def body(self):
        self.start("Every simultaneous invariant block of a global minimizer has minimum local cost.",
                   "Replacing one block by a cheaper transporter preserves feasibility and strictly lowers the sum of costs.")
        before=VGroup(card(r"W_1",WANTED),card(r"W_2",TRIAL),card(r"W_3",WANTED)).arrange(RIGHT,buff=.6)
        self.put(column(before,r"\Phi_p(W)=\Phi_p(W_1)+\Phi_p(W_2)+\Phi_p(W_3)",
                        r"\Phi_p(\widetilde W_2)<\Phi_p(W_2)\quad\Longrightarrow\quad\text{contradiction}",size=31))
        cheaper=card(r"\widetilde W_2",CURRENT).move_to(before[1])
        self.play(Transform(before[1],cheaper),run_time=1.2)


class M25MatchingEquality(MatchingSlide):
    kicker = "Step 5: close both inequalities for $1<p<2$"
    def body(self):
        self.start("The unrestricted smooth minimum equals the finite matching minimum.",
                   "Construct from each matching; extract a matching from the blocks of a global minimizer. Costs agree in both directions.")
        self.put(column(tex("Construction",size=28,color=WANTED),
                        r"M\longmapsto W_M",
                        r"\min_{W\in\mathcal F}\Phi_p(W)\le\min_M C_p(M)",
                        tex("Orthogonal blocks have additive costs",size=24)),"left")
        self.put(column(tex("Minimizer decomposition",size=28,color=TRIAL),
                        r"W_*\longmapsto M_*",
                        r"\min_{W\in\mathcal F}\Phi_p(W)\ge\min_M C_p(M)",
                        tex("Angle lists combine with multiplicity",size=24)),"right")


class M26ZeroAngles(MatchingSlide):
    kicker = "Step 5: justify using only positive angle labels"
    def body(self):
        self.start("Zero-angle directions cannot provide cheaper extra partners.",
                   "A zero singleton costs zero. Removing a zero pairing cannot increase cost, and strict improvement contradicts minimality.")
        self.put(column(r"a_0(p)=0",
                        r"(\theta,0):\quad h=d=\theta/2",
                        r"b_{\theta,0}(p)=2f_p(\theta)\ge a_\theta(p)",
                        card(r"\text{Keep common directions fixed}",WANTED,size=29)))


class M27UniformLimit(MatchingSlide):
    kicker = "Step 6(a): let p approach one from above"
    def body(self):
        self.start("Uniform convergence carries the minimum values to the trace norm.",
                   "All displacement singular values lie in [0,2]. A uniform error bound also bounds the difference of minimum values.")
        ax=Axes(x_range=[0,2,.5],y_range=[0,3,1],x_length=4.8,y_length=2.7,
                axis_config={"color":MUTED,"include_tip":False})
        curves=VGroup(ax,ax.plot(lambda s:s,color=FG),
                      math("s",size=23).next_to(ax.x_axis,RIGHT,buff=.1),
                      math(r"s^p",size=23,color=CURRENT).next_to(ax.y_axis,UP,buff=.1))
        for p,color in [(1.8,FAINT),(1.4,MUTED),(1.1,CURRENT)]:
            curves.add(ax.plot(lambda s,p=p:s**p,color=color))
        self.put(column(curves,math(r"s^p\longrightarrow s\quad\text{on }[0,2]",size=27)),"left")
        self.put(column(r"\sup_W|\Phi_p(W)-\|I-W\|_1|",
                        r"\le n\sup_{0\le s\le2}|s^p-s|\longrightarrow0",
                        r"|\min f-\min g|\le\sup|f-g|",
                        tex("Compact pair interval; finitely many matchings",size=23),size=29),"right")


class M28EndpointWeights(MatchingSlide):
    kicker = "Step 6(b): evaluate the scalar minimum at p=1"
    def body(self):
        self.start(r"The paired trace cost is $4\sin h$, attained at $\tau=h$.",
                   "The sum-to-product identity gives 8 sin(h/2) cos(tau/2), which is nonincreasing as tau runs from d to h.")
        self.put(column(r"2\bigl(f_1(h+\tau)+f_1(h-\tau)\bigr)",
                        r"=8\sin(h/2)\cos(\tau/2)",
                        r"\min_{d\le\tau\le h}=4\sin h",size=32),"left")
        self.put(column(card(r"h+\tau=2h=\theta_i+\theta_j",WANTED,size=29),
                        card(r"h-\tau=0",MUTED,size=29),
                        tex("One moving plane; one fixed plane",size=26),
                        r"e_{ij}=4\sin((\theta_i+\theta_j)/2)",size=29),"right")


class M29MatchingAlgorithm(MatchingSlide):
    kicker = "Recover both the minimum cost and an attaining transporter"
    def body(self):
        self.start("Maximum total edge weight gives minimum trace displacement.",
                   r"Each edge subtracts $s_i+s_j-e_{ij}$ from the all-singleton baseline. Realize the chosen blocks by an orthogonal sum.")
        self.put(graph_example()[0],"left")
        self.put(column(r"C_0=\sum_i s_i,\qquad g_{ij}=s_i+s_j-e_{ij}",
                        r"\mathrm{OPT}=C_0-\max_M\sum_{\{i,j\}\in M}g_{ij}",
                        r"M_*\longmapsto W_{M_*}",
                        tex("Total weight, not number of edges",size=25),size=30),"right")


class M30WorkedExample(MatchingSlide):
    kicker = "Three positive angles: 30, 45, and 75 degrees in real dimension six"
    def body(self):
        self.start("Pair labels 1 and 2; reflect on the remaining principal plane.",
                   "The paired four-dimensional block costs 4 sin(37.5 degrees); the unmatched 75-degree singleton costs 2.")
        ex=nuclear_matching_graph_example()
        choices=[(r"\varnothing",ex['all_singletons'])]+[
            (rf"\{{\{{{i+1},{j+1}\}}\}}",ex['all_singletons']-gain)
            for (i,j),gain in ex['savings'].items()]
        self.put(column(*(math(rf"M={label}:\quad C(M)={cost:.4f}",size=30,
                               color=CURRENT if label==choices[1][0] else FG)
                          for label,cost in choices),buff=.24),"left")
        self.put(column(r"W=W_{12}\oplus W_3",
                        r"\mathbb R^6=\mathbb R^4\oplus\mathbb R^2",
                        r"\|I-W\|_1=4\sin(37.5^\circ)+2",
                        card(r"\mathrm{OPT}\approx4.4350",CURRENT),size=31),"right")


class M31Rehearsal(MatchingSlide):
    kicker = "Reconstruct each inference before reading its justification"
    def body(self):
        self.start("Explain the construction, the structural lower bound, and the trace-norm limit.",
                   "The study note expands each step, including differentiability and the four-dimensional characteristic polynomial.")
        questions=["Why does construction give the upper bound?",
                   "Why does sign averaging handle mixing directions?",
                   "Why do two phases still need the projection argument?",
                   "Why may minimum values pass through the limit?"]
        self.put(column(*(para(f"{i}. {q}",width=11.8,size=30)
                          for i,q in enumerate(questions,1)),buff=.32))
