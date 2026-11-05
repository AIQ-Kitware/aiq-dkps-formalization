"""A compact presentation of the real matching proof, with synchronized notes."""
from __future__ import annotations

import numpy as np
from manim import (
    Arrow, Axes, DashedLine, Dot, DOWN, LEFT, Line, Rectangle, RIGHT,
    Transform, UP, VGroup, Create, Indicate,
)

from dkvis.learning.matching.model import (
    paired_power_cost, phase_derivative, phase_level_roots, phase_rectangle_edge,
)
from dkvis.presentation.narration import read_deck_narration
from dkvis.novelty_math import nuclear_matching_graph_example
from dkvis.slide_style import (
    CURRENT, FAINT, FG, GAP, MUTED, RESID, SINE, TRIAL, WANTED,
    DeckSlide, boxed, math, para, tex,
)

SCRIPTS = read_deck_narration('matching-proof-talk')


def stack(*items, size=30, buff=.25):
    return VGroup(*(math(item, size=size) if isinstance(item, str) else item
                    for item in items)).arrange(DOWN, buff=buff)


def tile(label, *, color=FG, width=2.1, height=.85):
    box = Rectangle(width=width, height=height, color=color,
                    fill_color=color, fill_opacity=.08)
    label = math(label, size=29)
    if label.width > width-.22:
        label.scale_to_fit_width(width-.22)
    return VGroup(box, label.move_to(box))


class MatchingTalkSlide(DeckSlide):
    stage = 0
    wait_time_between_slides = .3

    def make_chrome(self):
        script = SCRIPTS[type(self).__name__]
        self.title, self.kicker = script.title, script.motivation
        chrome = super().make_chrome()
        if self._head[1].width > 12.5:
            self._head[1].scale_to_fit_width(12.5)
            self._head[1].next_to(self._head[0], DOWN, aligned_edge=LEFT, buff=.18)
        steps = VGroup(*(tex(label, size=17, color=CURRENT if i == self.stage else MUTED)
                         for i, label in enumerate([
                             'Setup', 'Stationarity', 'Common blocks',
                             'Local costs', 'Matching', 'Trace endpoint',
                         ]))).arrange(RIGHT, buff=.55)
        steps.move_to([0, -3.10, 0])
        active = steps[self.stage]
        chrome.add(steps, Line(active.get_left()+DOWN*.15,
                               active.get_right()+DOWN*.15,
                               color=CURRENT, stroke_width=2))
        return chrome

    def construct(self):
        self._beat = 0
        super().construct()
        if self._beat+1 != len(SCRIPTS[type(self).__name__].beats):
            raise ValueError(f'Animation/narration build mismatch: {type(self).__name__}')

    def begin(self):
        self.say(SCRIPTS[type(self).__name__].beats[0])

    def beat(self):
        self.wait(.3)
        self._beat += 1
        self.say(SCRIPTS[type(self).__name__].beats[self._beat])

    def put(self, mob, side='full', *, y=-.15, height=4.55):
        width = 12.1 if side == 'full' else 5.75
        factor = min(1, width/mob.width, height/mob.height)
        if factor < .70:
            raise ValueError(f'Content too dense: {type(self).__name__} ({factor:.2f})')
        mob.scale(factor).move_to([{'full': 0, 'left': -3.2, 'right': 3.2}[side], y, 0])
        self.add(mob)
        return mob

    def conclusion(self, text):
        label = para(text, width=12.0, size=24, color=CURRENT)
        if label.height > .6:
            raise ValueError(f'Conclusion too long: {type(self).__name__}')
        self.add(label.move_to([0, -2.62, 0]))


class T00Statement(MatchingTalkSlide):
    def body(self):
        self.begin()
        self.put(stack(
            r'K,L\subseteq\mathbb R^n,\quad\dim K=\dim L,\quad'
            r'0<\theta_1,\ldots,\theta_m\le\pi/2',
            r'\operatorname{OPT}_1=\min_{W\in O(n),\ W(K)=L}\|I-W\|_1',
            boxed(math(r'\operatorname{OPT}_1=\min_M\left['
                       r'\sum_{\{i,j\}\in M}b_{ij}+\sum_{i\notin V(M)}a_i\right]',
                       size=34), color=CURRENT),
            r'a_i=\min\{4\sin(\theta_i/2),2\},\qquad '
            r'b_{ij}=4\sin((\theta_i+\theta_j)/2)',
            tex(r'$M$: a matching of positive angle labels; multiplicities retained.',
                size=26, color=MUTED), buff=.33), y=.0)
        self.conclusion('The minimum is attained over all ambient orthogonal transporters.')


class T01ProofStrategy(MatchingTalkSlide):
    def body(self):
        self.begin()
        self.put(stack(
            r'\mathcal F=\{W\in O(n):W(K)=L\}\quad\text{compact, nonempty}',
            r'\sym{PowerCost}(W)=\sum_k s_k(I-W)^p,\qquad 1<p<2',
            tex(r'Fix a global minimizer $W_p$.', size=30),
            tex(r'Principal planes need not be invariant under $W_p$.',
                size=28, color=GAP), buff=.35), y=.65, height=2.3)
        self.beat()
        labels = [r'\text{stationarity}', r'\text{common blocks}',
                  r'\text{block minima}', r'\text{matching}']
        boxes = VGroup(*(tile(label, color=CURRENT, width=2.7) for label in labels))
        boxes.arrange(RIGHT, buff=.38).move_to([0, -1.38, 0])
        self.add(boxes)
        for a, b in zip(boxes, boxes[1:]):
            self.play(Create(Arrow(a.get_right(), b.get_left(), buff=.03,
                                   color=CURRENT, stroke_width=2)), run_time=.35)
        self.conclusion('Prove the reduction for the smooth cost, then pass minimum values to p = 1.')


class T02Stationarity(MatchingTalkSlide):
    stage = 1

    def body(self):
        self.begin()
        left = stack(
            r'P=P_K,\quad Q=P_L,\quad \sym{Jreflect}=2P-I',
            r'B^T=-B,\ [B,P]=0\ \Longrightarrow\ W e^{tB}\in\mathcal F',
            r'\left.\frac{d}{dt}\sym{PowerCost}(We^{tB})\right|_0'
            r'=-\operatorname{tr}(\sym{SpectralGradient}B)',
            r'\sym{SpectralGradient}|_{\Pi_\varphi}'
            r'=\sym{MatchingPhaseCost}\prime(\varphi)\sym{Jturn},\quad'
            r'[\sym{SpectralGradient},W]=0',
            r'\sym{MatchingPhaseCost}(t)=(2\sin(t/2))^p', size=28, buff=.33)
        self.put(left, 'left', y=.0)
        self.beat()
        result = stack(
            r'B=P\sym{SpectralGradient}P',
            r'0=-\operatorname{tr}((P\sym{SpectralGradient}P)^2)'
            r'=\|P\sym{SpectralGradient}P\|_F^2',
            r'P\sym{SpectralGradient}P=P^\perp\sym{SpectralGradient}P^\perp=0',
            r'\sym{SpectralGradient}=\begin{pmatrix}0&G_{01}\\-G_{01}^T&0\end{pmatrix}',
            boxed(math(r'\sym{Jreflect}\sym{SpectralGradient}\sym{Jreflect}'
                       r'=-\sym{SpectralGradient}', size=32), color=RESID),
            size=28, buff=.28)
        self.put(result, 'right', y=.0)
        self.conclusion('The gradient is off diagonal in source coordinates; W may still mix principal planes.')


class T03TwoPhases(MatchingTalkSlide):
    stage = 2

    def body(self):
        self.begin()
        self.put(stack(
            r'V_g=\ker(-G^2-g^2I),\quad g>0',
            r'\sym{GradientComplexStructure}=G/g,\quad'
            r'\sym{GradientComplexStructure}^2=-I',
            r'[W,\sym{GradientComplexStructure}]=0,\quad'
            r'\sym{Jreflect}\sym{GradientComplexStructure}'
            r'=-\sym{GradientComplexStructure}\sym{Jreflect}',
            tex(r'$W$ is complex unitary; $J_{\mathrm{src}}$ is a conjugation.', size=27),
            r'f_p\prime(\varphi)=g', size=31, buff=.34), 'left', y=.1)
        p = 1.5
        critical = 2*np.arctan(np.sqrt(p-1))
        g = .72*float(phase_derivative(critical, p))
        axes = Axes(x_range=[0, np.pi, 1], y_range=[0, 1.5, .5],
                    x_length=4.7, y_length=2.5, tips=False,
                    axis_config={'color': MUTED, 'include_ticks': False})
        curve = axes.plot(lambda t: float(phase_derivative(t, p)),
                          x_range=[0, np.pi, .025], color=SINE)
        level = DashedLine(axes.c2p(0, g), axes.c2p(np.pi, g), color=RESID)
        roots = phase_level_roots(p, g)
        points = VGroup(*(Dot(axes.c2p(t, g), color=SINE, radius=.065) for t in roots))
        labels = VGroup(*(math(rf'\varphi_{i+1}', size=25, color=SINE).next_to(
            points[i], DOWN, buff=.18) for i in range(len(roots))))
        plot = VGroup(axes, curve, level, points, labels,
                      math(r'f_p\prime(\varphi)', size=27).next_to(axes, UP),
                      math(r'g', size=27, color=RESID).next_to(level, RIGHT),
                      tex(r'$p=1.5$ (illustration)', size=21, color=MUTED).next_to(axes, DOWN, buff=.35))
        self.beat()
        self.put(plot, 'right', y=.15)
        self.conclusion(r'$f_p\prime$ increases then decreases: every positive level has at most two phases.')


class T04CommonBlocks(MatchingTalkSlide):
    stage = 2

    def body(self):
        self.begin()
        self.put(stack(
            r'W=e^{i\varphi_1}E+e^{i\varphi_2}(I-E),\quad E=X+iY',
            r'X^T=X,\quad Y^T=-Y,\quad X^2-Y^2=X,\quad XY+YX=Y',
            r'Xu=\lambda u\ \Longrightarrow\ '
            r'X(Yu)=(1-\lambda)Yu,\quad Y^2u=-\lambda(1-\lambda)u',
            size=29, buff=.32), y=1.17, height=1.8)
        u, v = tile(r'u', color=TRIAL), tile(r'v=Yu/\eta', color=TRIAL)
        u.move_to([-2.3, -.60, 0]); v.move_to([2.3, -.60, 0])
        forward = Arrow(u.get_right()+UP*.13, v.get_left()+UP*.13,
                        color=RESID, buff=.1)
        back = Arrow(v.get_left()+DOWN*.13, u.get_right()+DOWN*.13,
                     color=RESID, buff=.1)
        self.add(u, math(r'\eta=\sqrt{\lambda(1-\lambda)}', size=27).move_to([0, .12, 0]))
        self.beat()
        self.add(v)
        self.play(Create(forward), Create(back), run_time=.8)
        self.add(math(r'Yu=\eta v', size=25, color=RESID).move_to([0, -.23, 0]),
                 math(r'Yv=-\eta u', size=25, color=RESID).move_to([0, -1.00, 0]))
        self.add(math(r'\operatorname{span}_{\mathbb C}\{u,v\}'
                      r'=\operatorname{span}_{\mathbb R}\{u,v,\mathcal I_g u,\mathcal I_g v\}',
                      size=29).move_to([0, -1.65, 0]))
        self.conclusion(r'$J_{\mathrm{src}}$ fixes $u,v$ and negates $\mathcal I_g u,\mathcal I_g v$: two source directions in four dimensions.')


class T05BlockAccounting(MatchingTalkSlide):
    stage = 2

    def body(self):
        self.begin()
        self.put(stack(
            r'0<\lambda<1:\quad \dim_{\mathbb R}V_a=4,\quad\dim(K\cap V_a)=2',
            r'\lambda\in\{0,1\}:\quad Yu=0,\quad (\dim V_a,\dim(K\cap V_a))=(2,1)',
            r'g=0:\quad W^2=I\quad\Longrightarrow\quad'
            r'\text{two-projection lines and planes}', size=29, buff=.30), y=1.05, height=1.8)
        blocks = VGroup(tile(r'\theta_1', color=SINE, width=2.0),
                        tile(r'\theta_2,\theta_3', color=SINE, width=3.5),
                        tile(r'\theta_4', color=SINE, width=2.0)).arrange(RIGHT, buff=.45)
        self.put(blocks, y=-.5, height=1)
        self.beat()
        self.add(math(r'W=\bigoplus_a W_a,\quad P=\bigoplus_a P_a,\quad'
                      r' Q=WPW^T=\bigoplus_a Q_a', size=30).move_to([0, -1.35, 0]),
                 math(r'\Phi_p(W)=\sum_a\Phi_p(W_a),\qquad'
                      r'\{\theta_i\}=\bigsqcup_a\{\text{angles of }(P_a,Q_a)\}',
                      size=29).move_to([0, -2.02, 0]))
        self.conclusion('Each block preserves the constraints, the angle labels, and additivity of cost.')


class T06LocalFibers(MatchingTalkSlide):
    stage = 3

    def body(self):
        self.begin()
        self.put(stack(
            tex('One principal angle', size=29, color=SINE),
            r'R_{\theta_i}:\ 2f_p(\theta_i),\qquad'
            r'\text{reflection}:\ 2^p',
            boxed(math(r'a_i(p)=\min\{2f_p(\theta_i),2^p\}', size=31), color=CURRENT),
            tex('Common directions can be fixed.', size=25, color=MUTED),
            size=29, buff=.38), 'left', y=.1)
        self.beat()
        self.put(stack(
            tex('Two principal angles', size=29, color=SINE),
            r'D=\begin{pmatrix}C&-S\\S&C\end{pmatrix},\quad'
            r' W=D\operatorname{diag}(U_0,U_1)',
            r'C=\operatorname{diag}(\cos\theta_i,\cos\theta_j)',
            r'S=\operatorname{diag}(\sin\theta_i,\sin\theta_j)',
            r'U_0,U_1\in O(2)',
            r'h=(\theta_i+\theta_j)/2,\quad d=(\theta_i-\theta_j)/2\ge0',
            size=28, buff=.26), 'right', y=.1)
        self.conclusion(r'The local calculation ranges over the entire $O(2)\times O(2)$ fiber.')


class T07PhaseRectangle(MatchingTalkSlide):
    stage = 3

    def body(self):
        self.begin()
        self.put(stack(
            r'\det W=1:\quad U_0,U_1\text{ both rotations or both reflections}',
            r'U_0=R_{r+s}\sigma,\quad U_1=R_{r-s}\sigma,\quad'
            r'\sigma=I\text{ or }\operatorname{diag}(1,-1)',
            r'\begin{array}{c|cc}&\cos x&\cos y\\\hline'
            r'\sigma=I&\cos h\cos s&\cos d\cos r\\'
            r'\sigma\ne I&-\sin d\cos r&\sin h\cos s\end{array}',
            size=28, buff=.35), y=.95, height=2.1)
        self.beat()
        self.add(math(r'h\le x\le\pi-h,\quad d\le y\le\pi-d',
                      size=31, color=SINE).move_to([0, -.64, 0]),
                 math(r'a=\cos x,\ b=\cos y:\quad\operatorname{tr}W=4ab,\quad'
                      r'\operatorname{tr}(W^2)=16a^2b^2-8(a^2+b^2)+4',
                      size=26).move_to([0, -1.28, 0]),
                 math(r'\det(zI-W)=\prod_{\epsilon=\pm1}'
                      r'\bigl(z^2-2\cos(x+\epsilon y)z+1\bigr)',
                      size=30).move_to([0, -1.94, 0]))
        self.conclusion(r'The eigenvalues are $e^{\pm i(x+y)}$ and $e^{\pm i(x-y)}$.')


class T08EdgeReduction(MatchingTalkSlide):
    stage = 3

    def body(self):
        self.begin()
        h, d = np.pi/3, np.pi/6
        x, y, tau = phase_rectangle_edge(1.7, 2.0, h, d)
        axes = Axes(x_range=[0, np.pi, 1], y_range=[0, np.pi, 1],
                    x_length=4.5, y_length=2.8, tips=False,
                    axis_config={'color': MUTED, 'include_ticks': False})
        corners = [axes.c2p(a, b) for a, b in
                   [(h, d), (np.pi-h, d), (np.pi-h, np.pi-d), (h, np.pi-d)]]
        frame = VGroup(*(Line(corners[i], corners[(i+1) % 4], color=FAINT)
                         for i in range(4)))
        edge = Line(axes.c2p(h, d), axes.c2p(h, h), color=CURRENT, stroke_width=5)
        point = Dot(axes.c2p(x, y), color=SINE, radius=.07)
        target = Dot(axes.c2p(h, tau), color=CURRENT, radius=.07)
        plot = VGroup(axes, frame, edge, point,
                      math(r'x', size=24).next_to(axes, RIGHT),
                      math(r'y', size=24).next_to(axes, UP),
                      math(r'(x,y)', size=24, color=SINE).next_to(point, RIGHT, buff=.12),
                      math(r'x=h,\ d\le\tau\le h', size=24, color=CURRENT).next_to(axes, DOWN, buff=.2))
        self.put(plot, 'left', y=.3, height=3.4)
        # Match the target to the translation/scaling applied to the plot.
        target.move_to(axes.c2p(h, tau))
        self.put(stack(
            r'x+y>\pi:\ (x,y)\mapsto(\pi-x,\pi-y)',
            r'\tau=\max\{d,h-|x-y|\}',
            r'h+\tau\le x+y,\qquad h-\tau\le|x-y|',
            r'f_p\text{ increasing on }[0,\pi]',
            size=28, buff=.35), 'right', y=.6, height=2.5)
        self.beat()
        self.add(Dot(point.get_center(), color=FAINT, radius=.045))
        self.play(Create(Arrow(point.get_center(), target.get_center(),
                               buff=.09, color=CURRENT)), Transform(point, target), run_time=1.4)
        self.add(math(r'U_0=U_1=R_\gamma,\quad\cos\gamma=\cos\tau/\cos d',
                      size=27).move_to([0, -1.66, 0]),
                 boxed(math(r'b_{ij}(p)=\min_{d\le\tau\le h}'
                            r'2\bigl[f_p(h+\tau)+f_p(h-\tau)\bigr]', size=30),
                       color=CURRENT).move_to([0, -2.32, 0]))


class T09OtherComponents(MatchingTalkSlide):
    stage = 3

    def body(self):
        self.begin()
        self.put(stack(
            tex('Negative determinant', size=30, color=GAP),
            r'\sigma(W)=\{1,-1,e^{it},e^{-it}\}',
            r'|\operatorname{tr}W|=|2\cos t|\le2\cos\theta_j',
            r't\ge\theta_j\quad(\theta_i\ge\theta_j)',
            r'\Phi_p(W)\ge2^p+2f_p(\theta_j)\ge a_i(p)+a_j(p)',
            size=27, buff=.30), 'left', y=.40, height=3.3)
        self.beat()
        self.put(stack(
            tex('Zero-angle partners', size=30, color=GAP),
            r'\theta_j=0:\quad h=d=\theta_i/2',
            r'a_j(p)=0,\qquad b_{ij}(p)=2f_p(\theta_i)\ge a_i(p)',
            tex('Zero-angle directions can remain fixed.', size=25),
            size=28, buff=.37), 'right', y=.40, height=3.3)
        self.add(boxed(math(r'\min_{W\text{ on the two-angle block}}\Phi_p(W)'
                            r'=\min\{b_{ij}(p),a_i(p)+a_j(p)\}', size=29),
                       color=CURRENT).move_to([0, -1.82, 0]))
        self.conclusion('Both determinant components and common directions are accounted for.')


class T10MatchingEquality(MatchingTalkSlide):
    stage = 4

    def body(self):
        self.begin()
        self.put(stack(
            r'C_p(M)=\sum_{\{i,j\}\in M}b_{ij}(p)'
            r'+\sum_{i\notin V(M)}a_i(p)',
            tex('Matching to transporter', size=30, color=WANTED),
            tex('Orthogonal sum of attaining blocks and identity on common directions.',
                size=25),
            r'\min_{W\in\mathcal F}\Phi_p(W)\le\min_M C_p(M)',
            size=31, buff=.34), y=.92, height=2.45)
        self.beat()
        self.add(tex('Minimizer to matching', size=30, color=TRIAL).move_to([0, -.83, 0]),
                 para('Each restriction minimizes its local problem. Replace a cheaper block to contradict global minimality.',
                      width=11.6, size=26).move_to([0, -1.38, 0]),
                 boxed(math(r'\min_{W\in\mathcal F}\Phi_p(W)=\min_M C_p(M),'
                            r'\qquad 1<p<2', size=33),
                       color=CURRENT).move_to([0, -2.20, 0]))


class T11TraceEndpoint(MatchingTalkSlide):
    stage = 5

    def body(self):
        self.begin()
        top = stack(
            r'\sup_{W\in\mathcal F}\bigl|\Phi_p(W)-\|I-W\|_1\bigr|'
            r'\le n\max_{0\le s\le2}|s^p-s|\ \longrightarrow\ 0',
            tex(r'Compact scalar intervals and finitely many matchings give the other limit.', size=26),
            size=29, buff=.25)
        self.put(top, y=1.50, height=1.1)
        self.beat()
        h, d = 1.2, .2
        axes = Axes(x_range=[d, h, .5], y_range=[3.5, 4.7, .5],
                    x_length=4.5, y_length=2.1, tips=False,
                    axis_config={'color': MUTED, 'include_ticks': False})
        cost = lambda tau: float(paired_power_cost(h+d, h-d, tau, 1))
        curve = axes.plot(cost, x_range=[d, h, .015], color=CURRENT)
        plot = VGroup(axes, curve,
                      Dot(axes.c2p(h, cost(h)), color=CURRENT, radius=.07),
                      math(r'\tau=d', size=24).next_to(axes.c2p(d, 3.5), DOWN),
                      math(r'\tau=h', size=24).next_to(axes.c2p(h, 3.5), DOWN),
                      tex('Trace-norm pair cost', size=25).next_to(axes, UP))
        self.put(plot, 'left', y=-.62, height=2.9)
        self.put(stack(
            r'a_i(1)=\min\{4\sin(\theta_i/2),2\}',
            r'2[f_1(h+\tau)+f_1(h-\tau)]',
            r'=8\sin(h/2)\cos(\tau/2)',
            r'b_{ij}(1)=4\sin h\quad(\tau=h)',
            r'(h+\tau,h-\tau)=(\theta_i+\theta_j,0)',
            size=28, buff=.24), 'right', y=-.59, height=3.0)
        self.conclusion('Uniform convergence passes both minimum values to the trace norm.')


class T12Attainment(MatchingTalkSlide):
    stage = 5

    def body(self):
        self.begin()
        ex = nuclear_matching_graph_example()
        points = np.array([[-1.8, .7, 0], [1.8, .7, 0], [0, -1.05, 0]])
        graph = VGroup()
        positions = {(0, 1): [0, 1., 0], (0, 2): [-1.3, -.35, 0],
                     (1, 2): [1.3, -.35, 0]}
        selected_line = None
        for (i, j), weight in ex['savings'].items():
            line = DashedLine(points[i], points[j], color=FAINT)
            graph.add(line,
                      math(f'{weight:+.4f}', size=25, color=CURRENT).move_to(positions[i, j]))
            if (i, j) in ex['pairs']:
                selected_line = line
        for i, (point, angle) in enumerate(zip(points, ex['angles_deg'])):
            dot = Dot(point, color=SINE, radius=.065)
            graph.add(dot, math(rf'\theta_{i+1}={angle:.0f}^\circ', size=26,
                               color=SINE).next_to(dot, UP if i < 2 else DOWN, buff=.24))
        self.put(graph, 'left', y=.12, height=3.4)
        self.put(stack(
            r'g_{ij}=a_i+a_j-b_{ij}',
            r'\operatorname{OPT}_1=\sum_i a_i-\max_M\sum_{\{i,j\}\in M}g_{ij}',
            math(rf'M=\{{\{{1,2\}}\}},\quad\operatorname{{OPT}}_1={ex["all_singletons"]-ex["savings"][0,1]:.4f}',
                 size=30, color=CURRENT),
            r'W_\star=W_{12}\oplus W_3',
            tex('Paired block + singleton reflection', size=24),
            size=28, buff=.42), 'right', y=.10, height=3.4)
        self.beat()
        # The graph group was translated by put(); preserve that same transform.
        edge = Line(selected_line.get_start(), selected_line.get_end(),
                    color=CURRENT, stroke_width=6)
        self.play(Create(edge), run_time=.8)
        self.conclusion('A maximum-weight matching gives the unrestricted minimum and an actual orthogonal attainer.')
