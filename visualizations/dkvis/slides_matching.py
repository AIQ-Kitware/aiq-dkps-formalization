"""Theorem 5 as a sequence of inferences, with separately authored narration."""
from __future__ import annotations

import numpy as np
from manim import (
    Arc, Arrow, Axes, Circle, Create, DashedLine, Dot, DOWN, LEFT, Line,
    Rectangle, RIGHT, Rotate, Transform, UP, VGroup, Polygon,
    ValueTracker, always_redraw, FadeOut, Indicate, TransformFromCopy, ArcBetweenPoints,
)

from dkvis.matching_math import (
    paired_power_cost, pair_parameters, phase_derivative,
    phase_level_roots, phase_rectangle_edge,
    source_plane_wiggle,
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
        script = SCRIPTS[type(self).__name__]
        self.title, self.kicker = script.title, script.motivation
        chrome = super().make_chrome()
        kick = self._head[1]
        if kick.width > 12.1:
            kick.scale_to_fit_width(12.1).next_to(self._head[0],DOWN,aligned_edge=LEFT,buff=.18)
        from dkvis.decks.matching import SCENES
        at = SCENES.index(type(self).__name__)
        stage = sum(at >= SCENES.index(name) for name in
                    ["M06SmoothCost", "M20PairCoordinates", "M27UniformLimit"])
        labels = ["Build candidates", "Find independent pieces", "Compute their costs", "Return to trace norm"]
        items = VGroup(*(tex(label,size=17,color=CURRENT if i==stage else MUTED)
                         for i,label in enumerate(labels))).arrange(RIGHT,buff=.5)
        items.move_to([0,-3.16,0])
        chrome.add(items,Line(items[stage].get_left()+DOWN*.13,
                              items[stage].get_right()+DOWN*.13,color=CURRENT,stroke_width=2))
        return chrome

    def footer_text(self):
        return "Goal: the cheapest map carrying K onto L"

    def construct(self):
        super().construct()
        if self._beat_index+1 != len(SCRIPTS[type(self).__name__].beats):
            raise ValueError(f"narration builds do not match animations: {type(self).__name__}")

    def beat(self):
        self.wait(self.wait_time_between_slides)
        self._beat_index += 1
        self.say(SCRIPTS[type(self).__name__].beats[self._beat_index])

    def start(self, inference, justification):
        script = SCRIPTS[type(self).__name__]
        self._beat_index = 0
        self.say(script.beats[0])
        key = type(self).__name__ in {
            "M08CommutingConstruction", "M13InvariantBlocks", "M17ProjectionBlocks", "M27UniformLimit"}
        label = "Key idea" if key else "Takeaway"
        top = para(r"\textbf{"+label+r".} "+inference,width=12.2,size=26)
        top.move_to([0,self.content_top-.35,0])
        if top.height > .8:
            raise ValueError(f"inference is too long: {type(self).__name__}")
        if key:
            self.add(Rectangle(width=12.4,height=max(.56,top.height+.16),
                               color=CURRENT,stroke_width=2).move_to(top))
        reason = para(r"\textbf{What this gives us.} "+justification,width=12.2,size=23)
        if reason.height > .7:
            raise ValueError(f"justification is too long: {type(self).__name__}")
        reason.move_to([0,-2.65,0])
        reminder = tex(script.reminder,size=20,color=MUTED)
        if reminder.width > 12.1:
            reminder.scale_to_fit_width(12.1)
        reminder.move_to([0,-2.06,0])
        self.add(top,reason,reminder)

    def put(self,mob,side="full"):
        width = 12.2 if side=="full" else 5.7
        factor = min(1,width/mob.width,3.1/mob.height)
        if factor < .56:
            raise ValueError(f"content too dense in {type(self).__name__}: {factor:.2f}")
        mob.scale(factor).move_to([{"full":0,"left":-3.23,"right":3.23}[side],-.13,0])
        self.add(mob)
        return mob


class M00Problem(MatchingSlide):
    def body(self):
        self.start("Find the smallest full trace displacement of an orthogonal transporter.",
                   "Only the image subspace is prescribed; all ambient orthogonal competitors are allowed.")
        self.put(principal_plane(label="source and target"),"left")
        self.put(column(r"K,L\subseteq\mathbb R^n,\quad\dim K=\dim L",
                        r"W^TW=I,\qquad W(K)=L",
                        r"\mathrm{OPT}=\min_W\|I-W\|_1",
                        tex("Trace norm = sum of singular values",size=25)),"right")


class M01PrincipalPlanes(MatchingSlide):
    def body(self):
        self.start("Positive principal angles give mutually orthogonal real planes.",
                   "The SVD diagonalizes source--target overlaps. This does not yet constrain the minimizing W.")
        planes=VGroup(principal_plane(.45,"first principal plane"),
                      principal_plane(.9,"second principal plane")).arrange(RIGHT,buff=.65)
        self.put(planes,"left")
        self.put(column(r"\langle u_i,v_i\rangle=\cos\theta_i",
                        r"\langle u_i,v_j\rangle=0\quad(i\ne j)",
                        r"q_i=\frac{v_i-\cos\theta_i\,u_i}{\sin\theta_i}",
                        r"\Pi_i=\operatorname{span}(u_i,q_i)",
                        r"\Pi_i\perp\Pi_j\quad(i\ne j)",size=30),"right")


class M02Singleton(MatchingSlide):
    def body(self):
        self.start("A singleton chooses the cheaper of a rotation and a reflection.",
                   "A rotation has two equal displacement singular values; a reflection has values 0 and 2.")
        self.put(principal_plane(.9,label="unoriented source and target lines"),"left")
        self.put(column(tex("Rotation",size=29,color=WANTED),r"4\sin(\theta_i/2)",
                        tex("Reflection",size=29,color=TRIAL),r"2",
                        card(r"s_i=\min\{4\sin(\theta_i/2),2\}",CURRENT,size=29),buff=.12),"right")


class M03PairedBlock(MatchingSlide):
    def body(self):
        self.start("Two principal planes can interact within one four-dimensional block.",
                   "The paired construction rotates a different invariant plane and fixes its orthogonal complement.")
        left=column(card(r"\Pi_i\oplus\Pi_j\cong\mathbb R^4",SINE),
                    math(r"\Downarrow"),
                    VGroup(card(r"R_{\theta_i+\theta_j}",WANTED),card(r"I_2",MUTED)).arrange(RIGHT,buff=.3),
                    tex("Moving plane + fixed plane",size=26))
        self.put(left,"left")
        self.put(column(tex("Displacement singular values",size=27),
                        r"\bigl(2\sin h,2\sin h,0,0\bigr)",
                        r"h=(\theta_i+\theta_j)/2",
                        card(r"e_{ij}=4\sin h",CURRENT)),"right")


class M04Graph(MatchingSlide):
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
    def body(self):
        self.start("We have candidates. We still need to rule out profitable many-way mixing.",
                   "Legal wiggles will reveal why a global minimizer can be split into small pieces.")
        self.put(column(tex("Already available",size=29,color=WANTED),
                        r"M\longmapsto W_M",card(r"\mathrm{OPT}\le\min_M C(M)",WANTED)),"left")
        self.put(column(tex("The geometric work ahead",size=29,color=TRIAL),
                        tex("Construct legal wiggles",size=29),math(r"\Downarrow"),
                        tex("Get equations at a minimizer",size=29),math(r"\Downarrow"),
                        tex("Find independent small pieces",size=29),buff=.12),"right")


class M06SmoothCost(MatchingSlide):
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
    def body(self):
        self.start("The smooth cost attains a global minimum on the feasible set.",
                   "Extend orthonormal bases for nonemptiness; use closedness, boundedness, and continuity for attainment.")
        self.put(column(r"\mathcal F=\{W:W^TW=I,\ W(K)=L\}",
                        VGroup(card(r"\mathcal F\ne\varnothing",WANTED),
                               card(r"\mathcal F\ \text{compact}",TRIAL),
                               card(r"\Phi_p\ \text{continuous}",CURRENT)).arrange(RIGHT,buff=.5),
                        math(r"\Downarrow"),r"\exists W_*\in\mathcal F:\ \Phi_p(W_*)=\min_{\mathcal F}\Phi_p"))


class M08FeasibleCurves(MatchingSlide):
    def body(self):
        self.start("Pre-rotate inside K; the whole image remains L.",
                   "This constructs actual competitors for the unknown minimizer.")
        tracker=ValueTracker(0)
        screen=np.array([[.9,.15,-.3],[.1,.7,.65]])
        w,_=source_plane_wiggle(0)
        centers=[np.array([-3.,0.,0.]),np.array([3.,0.,0.])]
        def point(vector,center):
            return center+np.r_[1.15*(screen@vector),0.]
        for basis,center,label,color in [(np.eye(3)[:,:2],centers[0],"same source K",TRIAL),
                                         (w[:,:2],centers[1],"same target L",WANTED)]:
            corners=[point(basis@np.array([a,b]),center) for a,b in [(-1,-1),(1,-1),(1,1),(-1,1)]]
            self.add(Polygon(*corners,color=color,fill_color=color,fill_opacity=.09),
                     tex(label,size=27,color=color).move_to(center+UP*1.35))
        def vectors():
            fixed,variation=source_plane_wiggle(tracker.get_value())
            return VGroup(*(Arrow(center,point(matrix[:,j],center),buff=0,color=color,stroke_width=5)
                            for matrix,center,color in [(variation,centers[0],TRIAL),(fixed@variation,centers[1],WANTED)]
                            for j in range(2)))
        arrows=always_redraw(vectors)
        self.add(arrows,Arrow([-1.2,0,0],[1.2,0,0],buff=.1,color=FG),
                 math("W",size=31).move_to([0,.45,0]))
        self.beat()
        self.play(tracker.animate.set_value(1.1),run_time=2.8)
        self.add(math(r"V_t(K)=K\quad\Longrightarrow\quad WV_t(K)=L",size=30).move_to([0,-1.48,0]))
        self.beat()
        self.play(tracker.animate.set_value(.35),run_time=1.8)
        self.add(tex("Vectors move",size=23,color=MUTED).move_to([0,-.65,0]))


class M09RotationCost(MatchingSlide):
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
    def body(self):
        self.start("Compare equal cost-change rates; averaging cancels the mixing terms.",
                   "This extends the rotation-plane derivative calculation to directions that mix the planes.")
        labels=[[[r"B_{00}",r"B_{01}"],[r"B_{10}",r"B_{11}"]],
                [[r"B_{00}",r"-B_{01}"],[r"-B_{10}",r"B_{11}"]],
                [[r"B_{00}","0"],["0",r"B_{11}"]]]
        matrices=[block_matrix(entries).scale(.78).move_to([x,0,0]) for entries,x in zip(labels,[-4.,0.,4.])]
        self.add(*matrices[:2],math("B",size=28).move_to([-4,1.15,0]),
                 math("SBS",size=28).move_to([0,1.15,0]))
        definition=math(r"\mathrm{rate}(B):=\left.\frac{d}{dt}\Phi_p(We^{tB})\right|_{t=0}",size=28)
        definition.move_to([0,-1.5,0]); self.add(definition)
        self.beat()
        self.add(math(r"\tfrac12(B+SBS)",size=27).move_to([4,1.15,0]))
        self.play(TransformFromCopy(matrices[0],matrices[2]),run_time=1.5)
        equal=math(r"\mathrm{rate}(B)=\mathrm{rate}(SBS)=\mathrm{rate}\bigl(\tfrac12(B+SBS)\bigr)",size=26).move_to([0,-.98,0])
        self.play(Create(equal),run_time=1.2)
        self.add(tex("S keeps one block and flips the other",size=22,color=MUTED).move_to([0,1.48,0]))


class M11TracePairing(MatchingSlide):
    def body(self):
        self.start(r"The cost-change rate is $-\operatorname{tr}(GB)$.",
                   "Add the rotation-plane responses; sign cancellation has already dealt with mixing.")
        self.put(column(r"J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}",
                        r"B_{aa}=bJ_0,\qquad G_{aa}=f'_p(\varphi)J_0",
                        r"J_0^2=-I_2",size=31),"left")
        self.put(column(r"\frac{d}{dt}\,2f_p(\varphi+tb)\Big|_{t=0}=2bf'_p(\varphi)",
                        r"-\operatorname{tr}(G_{aa}B_{aa})=2bf'_p(\varphi)",
                        card(r"\frac{d}{dt}\Phi_p(We^{tB})\Big|_0=-\operatorname{tr}(GB)",RESID,size=29),size=29),"right")


class M12Stationarity(MatchingSlide):
    def body(self):
        self.start("A surviving internal response would give a legal test that detects it.",
                   "Both diagonal source blocks of G must vanish; only cross terms remain.")
        grid=block_matrix([[r"G_{00}",r"G_{01}"],[r"-G_{01}^T",r"G_{11}"]])
        self.put(grid,"left")
        self.add(tex(r"Coordinates: $K\oplus K^\perp$",size=24,color=MUTED).move_to([-3.23,-1.55,0]))
        right=self.put(column(r"B=PGP=\begin{pmatrix}G_{00}&0\\0&0\end{pmatrix}",
                              tex("Choose this available internal velocity",size=24),size=29),"right")
        self.play(Indicate(grid[0:2],color=TRIAL),run_time=.8)
        self.beat()
        calculation=column(r"0=-\operatorname{tr}(GB)",r"=-\operatorname{tr}(B^2)=\|B\|_F^2",r"=\sum_{i,j}B_{ij}^2",r"\Longrightarrow\quad G_{00}=0",size=29).move_to(right)
        self.play(Transform(right,calculation),run_time=1.3)
        partial=block_matrix([["0",r"G_{01}"],[r"-G_{01}^T",r"G_{11}"]]).move_to(grid)
        self.play(Transform(grid,partial),run_time=1.)
        self.beat()
        zero=block_matrix([["0",r"G_{01}"],[r"-G_{01}^T","0"]]).move_to(grid)
        final=column(tex("Repeat inside the complement",size=25),r"G_{00}=G_{11}=0",
                     r"J=2P-I=\begin{pmatrix}I&0\\0&-I\end{pmatrix}",r"JGJ=-G",size=29).move_to(right)
        self.play(Transform(grid,zero),Transform(right,final),run_time=1.3)


class M13TwoDecompositions(MatchingSlide):
    def body(self):
        self.start("W's rotation planes and the source decomposition need not coincide.",
                   "The equations GW=WG and JGJ=-G connect them; neither equation assumes W preserves the original principal planes.")
        self.put(column(tex("Rotation-plane coordinates of W",size=28,color=WANTED),
                        block_matrix([[r"R_{\varphi_a}","0"],["0",r"R_{\varphi_b}"]],color=WANTED),
                        r"G_{aa}=f'_p(\varphi_a)J_0,\quad GW=WG",size=29),"left")
        self.put(column(tex("Source coordinates",size=28,color=TRIAL),
                        block_matrix([["0",r"G_{01}"],[r"-G_{01}^T","0"]]),
                        r"K\oplus K^\perp",size=29),"right")


class M14GradientLevels(MatchingSlide):
    def body(self):
        self.start("Squaring removes the sign reversal and reveals common invariant pieces.",
                   "We can split by response strength. These pieces may still have many dimensions.")
        k=card("K",TRIAL).move_to([-4.6,0,0]); comp=card(r"K^\perp",FG).move_to([-1.9,0,0])
        diagram=VGroup(k,comp,Arrow(k.get_right()+UP*.2,comp.get_left()+UP*.2,buff=.1,color=RESID),
                 Arrow(comp.get_left()+DOWN*.2,k.get_right()+DOWN*.2,buff=.1,color=RESID),
                 math("G",size=27,color=RESID).move_to([-3.3,.55,0]),
                 tex("Twice returns to the same side",size=24).move_to([-3.3,-.8,0]))
        self.add(diagram)
        right=self.put(column(r"JGJ=-G\quad\Longrightarrow\quad JG^2J=G^2",
                              r"A:=-G^2,\quad\langle Ax,x\rangle=\|Gx\|^2",size=28),"right")
        self.beat()
        groups=column(card(r"V_{g_1}:\ A=g_1^2I",RESID,size=27),
                      card(r"V_{g_2}:\ A=g_2^2I",RESID,size=27),
                      card(r"\ker G",MUTED,size=27),buff=.24)
        groups.move_to([-3.23,-.13,0])
        final=column(r"A=-G^2",r"Ax=g^2x,\quad AW=WA",r"A(Wx)=W(Ax)=g^2Wx",
                     tex("So W x stays in the same group",size=24),
                     tex("The same holds for P and Q",size=24),size=29).move_to(right)
        self.play(Transform(diagram,groups),Transform(right,final),run_time=1.4)


class M15ComplexCoordinates(MatchingSlide):
    def body(self):
        self.start("A normalized response pairs real directions exactly like multiplication by i.",
                   "Complex coordinates let us use phases while conjugation still remembers the source.")
        center=np.array([-3.3,-.1,0.]); arrow=Arrow(center,center+[1.2,0,0],buff=0,color=RESID)
        self.add(Circle(radius=1.2,color=FAINT).move_to(center),
                 Line(center+[-1.4,0,0],center+[1.4,0,0],color=TRIAL),
                 Line(center+[0,-1.4,0],center+[0,1.4,0],color=MUTED),arrow,
                 math("u",size=28,color=TRIAL).move_to(center+[1.5,-.2,0]))
        right=self.put(column(r"\mathcal I_g:=G/g",r"\mathcal I_g^2=-I",r"\|\mathcal I_gx\|=\|x\|",size=31),"right")
        self.beat()
        self.play(Rotate(arrow,np.pi/2,about_point=center),run_time=1.3)
        self.add(math(r"\mathcal I_gu=iu",size=27,color=RESID).move_to(center+[-.7,1.45,0]))
        self.play(Rotate(arrow,np.pi/2,about_point=center),run_time=1.3)
        next_content=column(r"u,\ \mathcal I_gu\quad\longleftrightarrow\quad1,\ i",
                            r"(a+ib)x=ax+b\mathcal I_gx",
                            tex("Same real space, paired coordinates",size=24),size=29).move_to(right)
        self.play(Transform(right,next_content),run_time=1.)
        self.beat()
        final=column(r"W\mathcal I_g=\mathcal I_gW",tex("W is complex-linear",size=25),
                     r"J(a+ib)=a-ib",tex("J remembers the source half",size=25),size=29).move_to(right)
        self.play(Transform(right,final),run_time=1.2)
        self.add(tex("J fixes u; it reverses i u",size=23,color=MUTED).move_to([-3.3,-1.62,0]))


class M16TwoPhases(MatchingSlide):
    def body(self):
        self.start("A fixed positive response strength allows at most two rotation phases.",
                   "We still need to split repeated phase spaces while preserving the source structure.")
        ax=Axes(x_range=[0,np.pi,1],y_range=[0,1.5,.5],x_length=4.7,y_length=2.35,
                axis_config={"color":MUTED,"include_tip":False})
        curve=ax.plot(lambda t:float(phase_derivative(t,1.5)),color=RESID)
        line=DashedLine(ax.c2p(0,.8),ax.c2p(np.pi,.8),color=GAP)
        picture=VGroup(ax,curve,line,math("t",size=23).next_to(ax.x_axis,RIGHT,buff=.1),
                       math("g",size=25,color=GAP).next_to(ax.c2p(0,.8),LEFT,buff=.1),
                       math(r"f'_p(t)",size=24,color=RESID).next_to(ax.y_axis,UP,buff=.1))
        self.put(picture,"left")
        roots=phase_level_roots(1.5,.8)
        markers=VGroup(*(Dot(ax.c2p(t,.8),color=SINE) for t in roots))
        self.play(Create(markers),run_time=1.)
        right=self.put(column(r"f'_p(t)=p(2\sin(t/2))^{p-1}\cos(t/2)",
                              r"f''_p(t)=0\ \Longleftrightarrow\ \tan^2(t/2)=p-1",
                              tex(r"One peak on $0<t<\pi$",size=25),
                              r"f'_p(t)=g:\quad\varphi_1,\ \varphi_2",size=26),"right")
        self.beat()
        next_content=column(r"W=e^{i\varphi_1}E+e^{i\varphi_2}(I-E)",
                            tex("E selects the first phase space",size=25),
                            tex("Each phase may repeat many times",size=25,color=SINE),size=29).move_to(right)
        self.play(Transform(right,next_content),run_time=1.3)


class M17ProjectionBlocks(MatchingSlide):
    def body(self):
        self.start("Starting from an X-eigenvector, one partner closes a line or plane.",
                   "That closed line or plane is the small invariant piece we were looking for.")
        right=self.put(column(r"E=X+iY,\quad X^T=X,\quad Y^T=-Y",
                              r"X^2-Y^2=X,\quad XY+YX=Y",
                              tex("Expand the projection equation E squared = E",size=23),size=28),"right")
        u=card("u",size=35).move_to([-4.8,0,0]); v=card("v",size=35).move_to([-1.8,0,0])
        self.add(u,tex("Start with one X-eigenvector",size=24).move_to([-3.3,1.15,0]),
                 math(r"Xu=\lambda u",size=28).move_to([-4.8,-1.15,0]))
        self.beat()
        self.add(v,math(r"Xv=(1-\lambda)v",size=27).move_to([-1.8,-1.15,0]))
        arrow=Arrow(u.get_right()+UP*.18,v.get_left()+UP*.18,buff=.1,color=RESID)
        partner=column(r"Xu=\lambda u",
                       r"Y^2u=(X^2-X)u=-\lambda(1-\lambda)u",
                       r"X(Yu)=(1-\lambda)Yu",
                       r"\eta=\|Yu\|=\sqrt{\lambda(1-\lambda)}",size=27).move_to(right)
        self.play(Create(arrow),Transform(right,partner),run_time=1.2)
        self.add(math(r"Yu=\eta v",size=27,color=RESID).move_to([-3.3,.6,0]))
        self.beat()
        back=Arrow(v.get_left()+DOWN*.18,u.get_right()+DOWN*.18,buff=.1,color=RESID)
        self.play(Create(back),run_time=1.2)
        self.add(math(r"Yv=-\eta u",size=27,color=RESID).move_to([-3.3,-.55,0]))
        self.play(Create(Rectangle(width=4.45,height=1.65,color=CURRENT).move_to([-3.3,0,0])),run_time=.8)
        final=column(r"\eta=\sqrt{\lambda(1-\lambda)}",
                     r"Yv=Y^2u/\eta=-\eta u",r"0<\lambda<1:\quad\operatorname{span}(u,v)",
                     r"\lambda=0,1:\quad Yu=0\quad\text{(one line)}",
                     tex("No third independent direction is needed",size=24),size=28).move_to(right)
        self.play(Transform(right,final),run_time=1.2)


class M18RealBlocks(MatchingSlide):
    def body(self):
        self.start("One or two complex coordinates give one or two source angle entries.",
                   "We have recovered singles and pairs from the structure of an unrestricted minimizer.")
        line=VGroup(card("u",TRIAL,size=32),card("iu",FG,size=32)).arrange(RIGHT,buff=.35)
        pair=VGroup(card("u",TRIAL,size=32),card("v",TRIAL,size=32),
                    card("iu",FG,size=32),card("iv",FG,size=32)).arrange(RIGHT,buff=.35)
        self.put(column(line,tex("One complex coordinate = two real directions",size=25),
                        pair,tex("Two complex coordinates = four real directions",size=25),buff=.3),"left")
        right=self.put(column(tex("These are real direction counts",size=27),
                              tex("Not a picture of a four-dimensional solid",size=23)),"right")
        self.beat()
        final=column(r"J(u)=u,\quad J(iu)=-iu",tex("Amber tiles: the source half",size=25,color=TRIAL),
                     r"\mathbb R^2:\ \text{one source direction}\ \longrightarrow\ \theta_i",
                     r"\mathbb R^4:\ \text{two source directions}\ \longrightarrow\ \theta_i,\theta_j",size=28).move_to(right)
        self.play(Transform(right,final),run_time=1.5)


class M19ZeroGradient(MatchingSlide):
    def body(self):
        self.start("On the zero group, reflection geometry supplies the remaining small pieces.",
                   "A needless negative-one action on an invariant line can be replaced by identity.")
        origin=np.array([-3.3,-.1,0.]); angle=.65
        self.add(Line(origin+[-1.5,0,0],origin+[1.5,0,0],color=TRIAL),
                 Line(origin-1.5*np.array([np.cos(angle),np.sin(angle),0]),
                      origin+1.5*np.array([np.cos(angle),np.sin(angle),0]),color=WANTED),
                 DashedLine(origin-1.5*np.array([np.cos(angle/2),np.sin(angle/2),0]),
                            origin+1.5*np.array([np.cos(angle/2),np.sin(angle/2),0]),color=MUTED),
                 tex("Reflection carries K onto L",size=25).move_to([-3.3,-1.3,0]))
        right=self.put(column(r"G=0\quad\Longrightarrow\quad W=I-2N",
                              tex("Two projections: P and N",size=27),
                              tex("Their principal lines and planes give pieces",size=23),size=29),"right")
        self.beat()
        final=column(r"W|_\ell=-1\quad\text{cost }2^p",math(r"\Downarrow"),
                     r"W|_\ell=+1\quad\text{cost }0",
                     tex("Same source and target on this invariant line",size=23),size=29).move_to(right)
        self.play(Transform(right,final),run_time=1.3)


class M20PairCoordinates(MatchingSlide):
    def body(self):
        self.start("Every local transporter is a fixed direct rotation after internal orthogonal changes.",
                   "The same pre-change geometry now parametrizes every competitor on one pair.")
        left=self.put(column(card("K",TRIAL),math(r"\xrightarrow{\ D\ }"),card("L",WANTED),
                             tex("One known reference transporter",size=24)),"left")
        right=self.put(column(r"D=\begin{pmatrix}C&-S\\S&C\end{pmatrix}",
                              r"C=\operatorname{diag}(\cos\theta_i,\cos\theta_j)",
                              r"S=\operatorname{diag}(\sin\theta_i,\sin\theta_j)",size=28),"right")
        self.beat()
        next_content=column(r"D^TW(K)=K",r"D^TW=\begin{pmatrix}U_0&0\\0&U_1\end{pmatrix}",
                            card(r"W=D\operatorname{diag}(U_0,U_1)",CURRENT,size=28),
                            tex(r"$U_0,U_1$: orthogonal $2\times2$ matrices",size=25),size=29).move_to(right)
        self.play(Transform(right,next_content),run_time=1.5)
        reminder=column(card(r"K\xrightarrow{\ U_0\ }K",TRIAL,size=27),
                        card(r"K^\perp\xrightarrow{\ U_1\ }K^\perp",FG,size=27),
                        math(r"\xrightarrow{\ D\ }"),card("L",WANTED),buff=.2).move_to(left)
        self.play(Transform(left,reminder),run_time=1.2)


class M20PhaseParameters(MatchingSlide):
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
    def body(self):
        self.start(r"The four eigenvalues are $e^{\pm i(x+y)}$ and $e^{\pm i(x-y)}$.",
                   "Block multiplication gives the two traces; orthogonality and determinant one fix the reciprocal polynomial. Factor it.")
        self.put(column(r"\operatorname{tr}W=4uv,\quad\operatorname{tr}(W^2)=16u^2v^2-8(u^2+v^2)+4",
                        r"c_2=\frac{(\operatorname{tr}W)^2-\operatorname{tr}(W^2)}2=4(u^2+v^2)-2",
                        r"\chi_W(z)=z^4-4uvz^3+\bigl(4(u^2+v^2)-2\bigr)z^2-4uvz+1",
                        r"\phantom{\chi_W(z)}=\prod_{\varepsilon=\pm1}\left(z^2-2\cos(x+\varepsilon y)z+1\right)",
                        tex(r"Here $u=\cos x$ and $v=\cos y$",size=24),size=28,buff=.2))


class M20RectangleBounds(MatchingSlide):
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
    def body(self):
        self.start("An independent piece of a globally cheapest map must itself be cheapest.",
                   "Replacing just that piece preserves transport and changes only its contribution to the total cost.")
        blocks=VGroup(card("W_1",FG),card("W_2",TRIAL),card("W_3",FG)).arrange(RIGHT,buff=.65)
        self.put(column(blocks,r"\Phi_p(W)=\Phi_p(W_1)+\Phi_p(W_2)+\Phi_p(W_3)",
                        tex("Source and target split along these same pieces",size=26),size=31))
        self.beat()
        cheaper=card(r"\widetilde W_2",CURRENT).move_to(blocks[1])
        self.play(Transform(blocks[1],cheaper),run_time=1.5)
        self.add(math(r"\Phi_p(\widetilde W_2)<\Phi_p(W_2)\quad\Longrightarrow\quad\text{a cheaper global map}",size=28).move_to([0,-1.6,0]))


class M25MatchingEquality(MatchingSlide):
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
    def body(self):
        self.start("Zero-angle directions cannot provide cheaper extra partners.",
                   "A zero singleton costs zero. Removing a zero pairing cannot increase cost, and strict improvement contradicts minimality.")
        self.put(column(r"a_0(p)=0",
                        r"(\theta,0):\quad h=d=\theta/2",
                        r"b_{\theta,0}(p)=2f_p(\theta)\ge a_\theta(p)",
                        card(r"\text{Keep common directions fixed}",WANTED,size=29)))


class M27UniformLimit(MatchingSlide):
    def body(self):
        self.start("Pass minimum values to the limit; the minimizing maps need not converge.",
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
    def body(self):
        self.start("Maximum total edge weight gives minimum trace displacement.",
                   r"Each edge subtracts $s_i+s_j-e_{ij}$ from the all-singleton baseline. Realize the chosen blocks by an orthogonal sum.")
        self.put(graph_example()[0],"left")
        self.put(column(r"C_0=\sum_i s_i,\qquad g_{ij}=s_i+s_j-e_{ij}",
                        r"\mathrm{OPT}=C_0-\max_M\sum_{\{i,j\}\in M}g_{ij}",
                        r"M_*\longmapsto W_{M_*}",
                        tex("Total weight, not number of edges",size=25),size=30),"right")


class M30WorkedExample(MatchingSlide):
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
    def body(self):
        self.start("Explain the construction, the structural lower bound, and the trace-norm limit.",
                   "The study note expands each step, including differentiability and the four-dimensional characteristic polynomial.")
        questions=["Why does construction give the upper bound?",
                   "Why does sign averaging handle mixing directions?",
                   "Why do two phases still need the projection argument?",
                   "Why may minimum values pass through the limit?"]
        self.put(column(*(para(f"{i}. {q}",width=11.8,size=30)
                          for i,q in enumerate(questions,1)),buff=.32))


class M00BlockMeaning(MatchingSlide):
    def body(self):
        self.start("Zero cross blocks mean each piece keeps its own vectors.",
                   "Then a large map is an orthogonal sum of independent smaller maps.")
        rooms=VGroup()
        for x,label in [(-1.2,"piece 0"),(1.2,"piece 1")]:
            center=Dot([x,0,0],radius=.035,color=FG)
            border=Rectangle(width=1.9,height=2.1,color=MUTED).move_to(center)
            arrow=Arrow(center.get_center(),center.get_center()+[.65,0,0],buff=0,color=FG)
            rooms.add(VGroup(border,center,arrow,tex(label,size=25).next_to(border,DOWN,buff=.12)))
        self.put(rooms,"left")
        coupling=Arrow(rooms[0][0].get_right()+UP*.4,rooms[1][0].get_left()+UP*.4,buff=.02,color=RESID)
        self.add(coupling)
        matrix=block_matrix([["A_{00}","A_{01}"],["A_{10}","A_{11}"]],color=FG)
        self.put(matrix,"right")
        self.beat()
        zero=block_matrix([["A_{00}","0"],["0","A_{11}"]],color=FG).move_to(matrix)
        self.play(FadeOut(coupling),Transform(matrix,zero),
                  Rotate(rooms[0][2],np.pi/3,about_point=rooms[0][1].get_center()),run_time=2.)
        self.add(tex("Motion inside a piece is still allowed",size=23,color=MUTED).next_to(rooms,DOWN,buff=.13))




class M08ProjectionMeaning(MatchingSlide):
    def body(self):
        self.start("P keeps the source component and removes the perpendicular one.",
                   "A change preserving both parts commutes with this keep-or-discard operation.")
        origin=np.array([-3.5,-.5,0.]); tip=origin+[1.6,1.1,0]
        self.add(Line(origin+[-1.2,0,0],origin+[2.2,0,0],color=TRIAL),
                 Line(origin+[0,-.5,0],origin+[0,2.1,0],color=MUTED),
                 Arrow(origin,tip,buff=0,color=FG),math("x",size=28).next_to(tip,UP,buff=.08),
                 math("K",size=29,color=TRIAL).move_to(origin+[2.35,0,0]))
        right=self.put(column(r"x=Px+(I-P)x",tex("Two perpendicular components",size=26)),"right")
        self.beat()
        self.play(Create(Arrow(origin,origin+[1.6,0,0],buff=0,color=TRIAL)),
                  Create(DashedLine(tip,origin+[1.6,0,0],color=MUTED)),run_time=1.2)
        self.add(math("Px",size=27,color=TRIAL).move_to(origin+[1.6,-.32,0]),
                 math(r"(I-P)x",size=26,color=MUTED).move_to(origin+[-.55,1.15,0]))
        new=column(r"x=Px+(I-P)x",r"P=\begin{pmatrix}I_K&0\\0&0\end{pmatrix}",r"Q=P_L,\quad WPW^T=Q",
                   tex(r"Coordinates: $K\oplus K^\perp$",size=25))
        new.move_to(right)
        self.play(Transform(right,new),run_time=1.)




class M08CommutingConstruction(MatchingSlide):
    def body(self):
        self.start("Choose internal rotation velocities; BP=PB follows from the construction.",
                   "A minimizer must resist every such available test; we do not assume a new optimizer property.")
        left=self.put(column(block_matrix([["B_{00}","0"],["0","B_{11}"]],color=TRIAL),
                             tex(r"No component crosses $K\leftrightarrow K^\perp$",size=24)),"left")
        right=self.put(column(r"J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}",
                              r"B_{00}=aJ_0,\quad B_{11}=bJ_0",
                              tex(r"Skew means $B^T=-B$",size=25),
                              tex(r"Choose any real speeds $a,b$",size=26),size=30),"right")
        self.beat()
        next_content=column(r"P=\begin{pmatrix}I&0\\0&0\end{pmatrix}",
                            r"BP=PB=\begin{pmatrix}B_{00}&0\\0&0\end{pmatrix}",size=30).move_to(right)
        self.play(Transform(right,next_content),Indicate(left[0],color=TRIAL),run_time=1.7)
        self.beat()
        last=column(r"e^{tB}=\begin{pmatrix}R_{at}&0\\0&R_{bt}\end{pmatrix}",
                    r"e^{tB}K=K",card(r"We^{tB}K=L",WANTED),size=30).move_to(right)
        self.play(Transform(right,last),run_time=1.4)




class M08StationaryTests(MatchingSlide):
    def body(self):
        self.start("Along every constructed feasible path, the cost has a minimum at zero.",
                   "Its first derivative must vanish. These necessary equations will reveal structure.")
        ax=Axes(x_range=[-1.4,1.4,1],y_range=[0,2,1],x_length=4.6,y_length=2.3,
                axis_config={"color":MUTED,"include_tip":False})
        curve=ax.plot(lambda t:.65*t*t+.3,color=CURRENT)
        picture=column(VGroup(ax,curve,math("t",size=24).next_to(ax.x_axis,RIGHT,buff=.1)),
                       tex("Schematic cost along a legal wiggle",size=23,color=MUTED))
        self.put(picture,"left")
        right=self.put(column(r"W_*:\ \text{a global minimizer}",
                              r"W_*e^{tB}\ \text{is feasible for all }t",size=29),"right")
        self.beat()
        tangent=Line(ax.c2p(-.6,.3),ax.c2p(.6,.3),color=RESID,stroke_width=5)
        self.play(Create(tangent),run_time=1.2)
        self.add(Dot(ax.c2p(0,.3),color=RESID))
        final=column(r"\left.\frac{d}{dt}\Phi_p(W_*e^{tB})\right|_{t=0}=0",
                     tex("For every internal skew direction B",size=24),
                     tex("Stationary: zero first derivative",size=25,color=RESID),size=29).move_to(right)
        self.play(Transform(right,final),run_time=1.2)




class M13InvariantBlocks(MatchingSlide):
    def body(self):
        self.start("Useful independent pieces are preserved by W, P, and Q together.",
                   "Then the source, target, and cost split into the same smaller problems.")
        nodes=VGroup(*(card(rf"e_{i+1}",size=25) for i in range(4)))
        for node,x in zip(nodes,[-5.4,-4.1,-2.8,-1.5]): node.move_to([x,.25,0])
        links=always_redraw(lambda:VGroup(ArcBetweenPoints(nodes[0].get_center(),nodes[2].get_center(),angle=-.8,color=RESID),
                                          ArcBetweenPoints(nodes[1].get_center(),nodes[3].get_center(),angle=.8,color=RESID)))
        self.add(links,nodes)
        matrix=self.put(column(r"\begin{pmatrix}c_1&0&-s_1&0\\0&c_2&0&-s_2\\s_1&0&c_1&0\\0&s_2&0&c_2\end{pmatrix}",
                               tex(r"Order: $e_1,e_2,e_3,e_4$",size=24),
                               math(r"c_i=\cos\theta_i,\quad s_i=\sin\theta_i",size=23),size=30),"right")
        self.add(tex("A concrete example: which directions interact?",size=23,color=MUTED).move_to([-3.3,1.2,0]))
        self.beat()
        points=[[-4.6,.55,0],[-2.1,.55,0],[-4.6,-.75,0],[-2.1,-.75,0]]
        final=column(r"\begin{pmatrix}c_1&-s_1&0&0\\s_1&c_1&0&0\\0&0&c_2&-s_2\\0&0&s_2&c_2\end{pmatrix}",
                     tex(r"Order: $e_1,e_3\;|\;e_2,e_4$",size=24),
                     math(r"c_i=\cos\theta_i,\quad s_i=\sin\theta_i",size=23),size=30).move_to(matrix)
        self.play(*(node.animate.move_to(point) for node,point in zip(nodes,points)),Transform(matrix,final),run_time=2.)
        for x in [-4.6,-2.1]: self.add(Rectangle(width=1.6,height=2.,color=MUTED).move_to([x,-.1,0]))
        self.add(tex("Same pieces work for P and Q in this example",size=22,color=MUTED).move_to([-3.3,-1.5,0]))
