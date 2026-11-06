"""A learner's proof of the population-gap theorem with explicit block geometry."""
import numpy as np
from manim import (
    Arc, Arrow, DashedLine, Dot, DOWN, Indicate, LEFT, Line, Rectangle,
    RIGHT, ValueTracker, VGroup, always_redraw, linear,
)
from dkvis.components.lesson import LessonSlide, LessonTitle, LessonLean, plane, stack, vector
from dkvis.learning.yws.model import mixed_gap_example, rotated_example
from dkvis.slide_style import CURRENT, FG, GAP, MUTED, RESID, SINE, TRIAL, WANTED, boxed, math, para, tex


def note(text, width=5.4, size=26):
    return para(text,width=width,size=size)


def formula(text, size=32):
    return boxed(math(text,size=size),color=CURRENT)


class YwsSlide(LessonSlide):
    lesson_deck='yws-population-gap'
    phase=None

    def make_chrome(self):
        chrome=super().make_chrome()
        if self.phase is not None:
            labels=VGroup(*(tex(label,size=19,color=CURRENT if i==self.phase else MUTED)
                            for i,label in enumerate(['Build R','Bound R','Use population g','Align frames'])))
            labels.arrange(RIGHT,buff=.5).move_to([0,-2.15,0]);chrome.add(labels)
        return chrome


class YsTitle(LessonTitle):
    lesson_deck='yws-population-gap'
    title_lines=('Yu–Wang–Samworth', 'A population-gap theorem')
    subtitle='From matrix error to subspace error and aligned frames.'
    series_title='Spectral perturbation · A learner’s proof'


class YsMotivation(YwsSlide):
    def body(self):
        self.start()
        self.put(stack(tex('Model information',size=32,color=WANTED),
                       math(r'\lambda_1\ge\cdots\ge\lambda_p',size=31),
                       note('Population eigenvalues describe the underlying matrix.'),buff=.4),'left',y=.75,height=2.7)
        self.put(stack(tex('Estimation error',size=32,color=TRIAL),
                       math(r'H=\widehat A-A',size=34),
                       note('An estimate may be random; its error is measured by a matrix norm.'),buff=.4),'right',y=.75,height=2.7)
        self.beat()
        self.put(formula(r'\text{matrix error} \quad\longrightarrow\quad \text{subspace error}',32),y=-1.25,height=.8)
        self.takeaway('A deterministic conversion theorem can be combined with a separate probability bound.')


class YsMixedExample(YwsSlide):
    example=True
    def body(self):
        self.start();population,sample,g,mixed=mixed_gap_example()
        def x(value): return -5.7+(value-10)/45*11.2
        for values,y,label,color in [(population,1.4,'Population',WANTED),(sample,-.2,'Sample',TRIAL)]:
            self.add(Line([x(10),y,0],[x(55),y,0],color=MUTED),
                     tex(label,size=25,color=color).move_to([-5.6,y+.58,0]))
            for value in values:
                self.add(Dot([x(value),y,0],color=color),math(f'{value:g}',size=25).move_to([x(value),y-.35,0]))
        self.add(Rectangle(width=x(40)-x(20)+.5,height=1.15,color=WANTED).move_to([(x(40)+x(20))/2,1.25,0]))
        self.beat()
        self.add(DashedLine([x(21),-.2,0],[x(21),1.4,0],color=SINE),
                 formula(r'g=10,\qquad\delta_{\rm mixed}=0',31).move_to([0,-1.4,0]))
        self.takeaway('A zero mixed-gap certificate is compatible with a positive population boundary gap.')


class YsGap(YwsSlide):
    def body(self):
        self.start()
        self.put(stack(r'\lambda_1\ge\cdots\ge\lambda_{r-1}>\underbrace{\lambda_r\ge\cdots\ge\lambda_s}_{\text{selected}} >\lambda_{s+1}\ge\cdots\ge\lambda_p',
                       formula(r'g=\min(\lambda_{r-1}-\lambda_r,\ \lambda_s-\lambda_{s+1})>0',31),
                       tex('Only the exterior boundaries enter g.',size=30,color=GAP),size=30,buff=.45),y=1,height=2.4)
        self.beat()
        self.put(stack(note('Missing endpoint: omit that side. Full-space block: zero subspace error.',width=11,size=27),
                       note('Internal population multiplicities and sample ties are allowed.',width=11,size=27),buff=.25),y=-1.15,height=1.3)
        self.takeaway('A cluster needs separation from the outside, not from itself.')


class YsGeometry(YwsSlide):
    def body(self):
        self.start();axes=plane(extent=1.5);self.put(axes,'left',y=.45,height=2.9)
        theta=ValueTracker(.12)
        self.add(vector(axes,[1.2,0],WANTED))
        def picture():
            t=theta.get_value();p=np.array([np.cos(t),np.sin(t)])
            return VGroup(vector(axes,p,TRIAL),
                          DashedLine(axes.c2p(p[0],0),axes.c2p(*p),color=SINE),
                          Arc(radius=.4,start_angle=0,angle=t,color=SINE).shift(axes.c2p(0,0)))
        self.add(always_redraw(picture),tex('One-angle illustration',size=23,color=MUTED).move_to([-3.25,2,0]))
        self.put(stack(r'\sigma_j(V^T\widehat V)=\cos\theta_j',
                       r'\|\sin\Theta\|_F^2=\sum_{j=1}^d\sin^2\theta_j',
                       formula(r'X=V_\perp^T\widehat V,\quad\|X\|_F=\|\sin\Theta\|_F',27),
                       note('X is the estimated frame in unwanted population coordinates.'),size=30,buff=.35),'right',y=.45,height=3.6)
        self.beat();self.play(theta.animate.set_value(.65),run_time=3,rate_func=linear)
        self.takeaway('Sine error measures what lies outside the population space, independently of basis choices.')


class YsTheorem(YwsSlide):
    def body(self):
        self.start()
        self.put(stack(r'N:=\min\{\sqrt d\,\|H\|_{\rm op},\ \|H\|_F\}',
                       formula(r'\|\sin\Theta(\widehat V,V)\|_F\le\frac{2N}{g}',35),
                       tex('Real symmetric matrices; matched ordered blocks; population g > 0.',size=26),buff=.36),y=1.25,height=2.2)
        self.beat()
        self.put(stack(formula(r'\exists O\in O(d):\quad\|\widehat VO-V\|_F\le\frac{2\sqrt2 N}{g}',33),
                       tex('No sample eigengap or additional small-perturbation assumption.',size=26),buff=.3),y=-1.1,height=1.65)
        self.takeaway('Two conclusions: a basis-free space bound, then an aligned-frame bound.')


class YsRoadmap(YwsSlide):
    phase=0;stage=1
    def body(self):
        self.start()
        self.put(stack(tex('1. Bound one residual from above',size=31,color=RESID),
                       r'\|R\|_F\le 2N',
                       tex('2. Use the population gap from below',size=31,color=GAP),
                       r'g\|\sin\Theta\|_F\le\|R\|_F',buff=.25),y=.85,height=2.8)
        self.beat()
        self.put(stack(tex('3. Convert space error to aligned-frame error',size=28,color=SINE),
                       r'\|\widehat VO-V\|_F\le\sqrt2\|\sin\Theta\|_F',buff=.2),y=-1.2,height=1.1)
        self.takeaway('Choose R so that the upper estimate sees H and the lower estimate sees population gaps.')


class YsResidual(YwsSlide):
    phase=0;stage=1
    def body(self):
        self.start()
        self.put(stack(r'\Lambda=\operatorname{diag}(\lambda_r,\ldots,\lambda_s),\quad\widehat\Lambda=\operatorname{diag}(\widehat\lambda_r,\ldots,\widehat\lambda_s)',
                       formula(r'R:=\widehat V\Lambda-A\widehat V',35),
                       note('Estimated frame, population eigenvalues, population matrix.',width=11,size=27),size=29,buff=.35),y=1.15,height=2.2)
        self.beat()
        self.put(stack(r'\widehat A\widehat V=\widehat V\widehat\Lambda,\qquad\widehat A=A+H',
                       formula(r'R=H\widehat V-\widehat V(\widehat\Lambda-\Lambda)',33),buff=.26),y=-1.15,height=1.6)
        self.takeaway('This deliberate residual compares the estimated frame with population eigenvalues.')


class YsOperatorUpper(YwsSlide):
    phase=1;stage=1
    def body(self):
        self.start()
        self.put(stack(r'\|R\|_F\le\|H\widehat V\|_F+\|\widehat V(\widehat\Lambda-\Lambda)\|_F',
                       r'\|H\widehat V\|_F^2=\sum_{j=1}^d\|H\widehat v_j\|^2\le d\|H\|_{\rm op}^2',
                       tex('Each estimated column has unit length.',size=25),size=30,buff=.30),y=1.1,height=2.25)
        self.beat()
        self.put(stack(r'|\widehat\lambda_j-\lambda_j|\le\|H\|_{\rm op}\quad\text{(Weyl)}',
                       r'\|\widehat V(\widehat\Lambda-\Lambda)\|_F=\|\widehat\Lambda-\Lambda\|_F\le\sqrt d\|H\|_{\rm op}',
                       formula(r'\|R\|_F\le 2\sqrt d\|H\|_{\rm op}',30),size=28,buff=.22),y=-1,height=1.95)
        self.takeaway('The factor two adds the frame-perturbation term and the ordered-eigenvalue-shift term.')


class YsFrobeniusUpper(YwsSlide):
    phase=1;stage=1
    def body(self):
        self.start()
        self.put(stack(r'\|H\widehat V\|_F\le\|H\|_F\quad\text{(orthonormal compression)}',
                       r'\sum_{j=1}^{p}|\widehat\lambda_j-\lambda_j|^2\le\|H\|_F^2',
                       tex('Hoffman–Wielandt; restricting the sum to the block only decreases it.',size=26),size=29,buff=.35),y=1.15,height=2.2)
        self.beat()
        self.put(stack(r'\|R\|_F\le\|H\|_F+\|H\|_F',
                       formula(r'\|R\|_F\le 2\min\{\sqrt d\|H\|_{\rm op},\|H\|_F\}=2N',30),buff=.25),y=-1.1,height=1.65)
        self.takeaway('Both residual estimates hold simultaneously, so their minimum is available.')


class YsBlocks(YwsSlide):
    phase=2;stage=1
    def body(self):
        self.start()
        self.put(stack(tex('Choose a full population eigenbasis',size=29,color=WANTED),
                       r'Q_{\rm pop}=[V\ V_\perp],\quad Q_{\rm pop}^TQ_{\rm pop}=I',
                       formula(r'Q_{\rm pop}^TAQ_{\rm pop}=\begin{pmatrix}\Lambda&0\\0&\Lambda_1\end{pmatrix}',32),buff=.32),'left',y=.4,height=3.5)
        self.beat()
        self.put(stack(tex('Express the estimated frame in that basis',size=26,color=TRIAL),
                       r'Q_{\rm pop}^T\widehat V=\begin{pmatrix}V^T\widehat V\\V_\perp^T\widehat V\end{pmatrix}',
                       formula(r'X=V_\perp^T\widehat V',33),
                       note('Bottom coordinates = the unwanted part.'),buff=.32),'right',y=.4,height=3.5)
        self.takeaway('The population eigenbasis supplies these blocks; the estimated matrix need not share them.')


class YsLowerIdentity(YwsSlide):
    phase=2;stage=1
    def body(self):
        self.start()
        self.put(stack(r'R=\widehat V\Lambda-A\widehat V',
                       r'V_\perp^TA=\Lambda_1V_\perp^T',
                       tex('Reason: the complementary columns are population eigenvectors.',size=26),buff=.32),y=1.15,height=2.1)
        self.beat()
        self.put(stack(formula(r'V_\perp^TR=X\Lambda-\Lambda_1X',33),
                       r'\|R\|_F\ge\|V_\perp^TR\|_F=\|X\Lambda-\Lambda_1X\|_F',size=29,buff=.32),y=-1,height=1.7)
        self.takeaway('Projecting onto the unwanted coordinates removes irrelevant residual energy.')


class YsEntrywise(YwsSlide):
    phase=2;stage=1
    def body(self):
        self.start()
        self.put(stack(r'(X\Lambda-\Lambda_1X)_{ij}=(\lambda_j-\mu_i)x_{ij}',
                       tex('Selected population value',size=27,color=WANTED),
                       math(r'\lambda_j',size=33,color=WANTED),
                       tex('Exterior population value',size=27,color=MUTED),
                       math(r'\mu_i',size=33),buff=.17),'left',y=.45,height=3.5)
        self.put(stack(r'|\lambda_j-\mu_i|\ge g',
                       note('Exterior values may lie above or below the selected block.'),
                       note('Frobenius norm squares entries, so signs do not cancel.'),buff=.4),'right',y=.85,height=2.8)
        self.beat()
        self.put(formula(r'\|R\|_F^2\ge\sum_{ij}(\lambda_j-\mu_i)^2|x_{ij}|^2\ge g^2\|X\|_F^2',28),y=-1.4,height=.85)
        self.takeaway('Every unwanted coefficient is multiplied by a population eigenvalue difference of size at least g.')


class YsCombine(YwsSlide):
    phase=2;stage=1
    def body(self):
        self.start()
        self.put(stack(r'g\|\sin\Theta\|_F=g\|X\|_F\le\|R\|_F\le 2N',
                       formula(r'\|\sin\Theta\|_F\le\frac{2\min\{\sqrt d\|H\|_{\rm op},\|H\|_F\}}{g}',32),buff=.48),y=.95,height=2.6)
        self.beat()
        self.put(note('Sample eigenvalue shifts entered only the upper bound. The lower bound uses population differences.',width=11,size=28),y=-1.25,height=1.0)
        self.takeaway('The residual sandwich proves the first conclusion with a population-only denominator.')


class YsAlignment(YwsSlide):
    phase=3;stage=1
    def body(self):
        self.start()
        self.put(stack(tex('A sign flip leaves a line unchanged',size=28),
                       r'\widehat v=-v,\quad\|\widehat v-v\|=2,\quad\sin\theta=0',
                       tex('Illustration: same line, different frame.',size=24,color=MUTED),buff=.4),y=1.05,height=2.2)
        self.beat()
        self.put(stack(formula(r'\min_{O\in O(d)}\|\widehat VO-V\|_F',34),
                       note('Right multiplication changes the estimated basis while preserving its space.',width=11,size=27),buff=.3),y=-1.1,height=1.6)
        self.takeaway('Choose the sample coordinates; keep the supplied population frame fixed.')


class YsAlignmentProof(YwsSlide):
    phase=3;stage=1
    def body(self):
        self.start()
        self.put(stack(r'\widehat V^TV=L\operatorname{diag}(\cos\theta_j)Q^T,\qquad O=LQ^T',
                       r'\|\widehat VO-V\|_F^2=2d-2\sum_j\cos\theta_j',
                       math(r'0\le\cos\theta_j\le1\quad\Longrightarrow\quad\cos\theta_j\ge\cos^2\theta_j',size=28),size=29,buff=.35),y=1.1,height=2.2)
        self.beat()
        self.put(stack(r'\|\widehat VO-V\|_F^2\le 2\sum_j\sin^2\theta_j',
                       formula(r'\|\widehat VO-V\|_F\le\sqrt2\|\sin\Theta\|_F\le\frac{2\sqrt2N}{g}',29),size=28,buff=.22),y=-1.05,height=1.9)
        self.takeaway('Residual estimation supplies 2; converting spaces to aligned frames supplies the extra square root two.')


class YsRotationExample(YwsSlide):
    example=True;stage=2
    def body(self):
        self.start();axes=plane(extent=1.6);self.put(axes,'left',y=.45,height=3)
        angle=ValueTracker(.1)
        self.add(vector(axes,[1,0],WANTED))
        def picture():
            a,b,vhat,r=rotated_example(angle.get_value());v=vhat[:,0]
            return VGroup(vector(axes,v,TRIAL),
                          Arrow(axes.c2p(0,0),axes.c2p(*r[:,0]),buff=0,color=RESID),
                          DashedLine(axes.c2p(v[0],0),axes.c2p(*v),color=SINE))
        self.add(always_redraw(picture))
        self.put(stack(r'A=\operatorname{diag}(3,1),\quad\widehat A=Q_\theta A Q_\theta^T',
                       r'\widehat v=(\cos\theta,\sin\theta)^T,\quad g=2',
                       r'R=(0,2\sin\theta)^T,\quad\|H\|_{\rm op}=2\sin\theta',
                       r'\text{actual sine error}=\sin\theta',
                       r'\text{YWS upper bound}=2\sin\theta',size=27,buff=.35),'right',y=.5,height=3.6)
        self.beat();self.play(angle.animate.set_value(.6),run_time=4,rate_func=linear)
        self.takeaway('The lower residual estimate is exact here; the general upper estimate loses a factor two.')


class YsRectangular(YwsSlide):
    stage=2
    def body(self):
        self.start()
        self.put(stack(r'B,\widehat B\in\mathbb R^{m\times n},\quad D=\widehat B-B',
                       formula(r'B^TB:\ \text{right singular vectors},\quad\lambda_j=\sigma_j^2',29),
                       r'\widehat B^T\widehat B-B^TB=B^TD+D^TB+D^TD',size=29,buff=.35),y=1.1,height=2.2)
        self.beat()
        self.put(stack(r'C=2\sigma_1(B)+\|D\|_{\rm op}',
                       r'\|\widehat B^T\widehat B-B^TB\|_{\rm op}\le C\|D\|_{\rm op}',
                       r'\|\widehat B^T\widehat B-B^TB\|_F\le C\|D\|_F',size=29,buff=.22),y=-1,height=1.8)
        self.takeaway('Apply the symmetric theorem to a Gram matrix; left subspaces use BB transpose.')


class YsRectangularGap(YwsSlide):
    stage=2
    def body(self):
        self.start()
        self.put(stack(r'g_{\rm sv}=\min(\sigma_{r-1}^2-\sigma_r^2,\ \sigma_s^2-\sigma_{s+1}^2)>0',
                       tex('Use the full Gram spectrum, including zeros after the rank.',size=28,color=GAP),
                       r'1\le r\le s\le k=\operatorname{rank}B;\quad k<n\Rightarrow\sigma_{k+1}=0',size=28,buff=.35),y=1.15,height=2.25)
        self.beat()
        self.put(stack(formula(r'\|\sin\Theta\|_F\le\frac{2(2\sigma_1+\|D\|_{\rm op})\min\{\sqrt d\|D\|_{\rm op},\|D\|_F\}}{g_{\rm sv}}',27),
                       note('Corrected ambient-spectrum version of Theorem 3; the printed rank-based infinity convention is refuted.',width=11,size=25),buff=.28),y=-1.1,height=1.75)
        self.takeaway('Infinity belongs beyond the ambient spectrum, not just beyond the last positive singular value.')


class YsSummary(YwsSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Choose the residual with population eigenvalues.',size=29),
                       tex('Bound it above in two ways using H.',size=29),
                       tex('Population eigenvalue differences bound it below.',size=29),
                       tex('Align frames using the principal-angle geometry.',size=29),buff=.4),y=.85,height=2.8)
        self.beat()
        self.put(note('Statistics supplies a perturbation estimate; YWS converts it into geometric control.',width=11,size=28),y=-1.2,height=1)
        self.takeaway('The proof explains both the population-only gap and the two constants.')


class YsFacts(YwsSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(r'N=\min\{\sqrt d\|H\|_{\rm op},\|H\|_F\}',
                       formula(r'\|\sin\Theta(\widehat V,V)\|_F\le2N/g',35),
                       formula(r'\exists O\in O(d):\ \|\widehat VO-V\|_F\le2\sqrt2 N/g',33),
                       note('Real symmetric matrices; ordered blocks; positive population boundary gap.',width=11,size=27),buff=.4),y=.4,height=3.8)
        self.takeaway('These two statements correspond to the source-facing Lean applications on the next cards.')


class YsLean(LessonLean):
    lesson_deck='yws-population-gap';lecture_id='yws'
    assumptions='Real symmetric A, A-hat; ordered eigenframes V, V-hat; source population gap $g>0$. Full context and aliases: facts.lean.'
    symbolic_facts=(('Sine error',r'\|\sin\Theta\|_F\le2N/g'),
                    ('Aligned frame',r'\exists O\in O(d):\ \|\widehat VO-V\|_F\le2\sqrt2N/g'))
    ownership='YWS paper-facing package: Symmetric/Theorem2.lean. Lean uses zero-based block indices.'
    notation=r'\texttt{noise} is N; \texttt{sinError} is the sine norm; Lean $\Delta$ is the displayed gap g.'


class YsLeanAligned(YsLean):
    fact_index=1
    notation=r'\texttt{alignedError O} is $\|\widehat VO-V\|_F$; \texttt{hV, hVhat, hgap} carry the stated hypotheses.'


class YsComputation(YwsSlide):
    bonus=True;stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Use a symmetric eigensolver; sort in decreasing order.',size=29),
                       r'\cos\theta_j=\sigma_j(V^T\widehat V)',
                       r'\widehat V^TV=L C Q^T\quad\Longrightarrow\quad O=LQ^T',
                       tex('Near zero angles, avoid relying only on 1 minus a nearly unit squared cosine.',size=26),
                       r'\|\sin\Theta\|_F=\|V_\perp^T\widehat V\|_F',
                       note('A sample-only experiment does not certify an unknown population gap.',width=11,size=27),size=29,buff=.30),y=.35,height=3.8)
        self.takeaway('Numerics can check a known example; population-gap certification needs additional information.')
