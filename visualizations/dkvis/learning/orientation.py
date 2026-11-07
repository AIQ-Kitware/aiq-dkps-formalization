"""Local notation refreshers: no earlier video is required to decode a lesson."""
from manim import DOWN, LEFT, VGroup
from dkvis.components.lesson import LessonSlide, stack
from dkvis.slide_style import CURRENT, boxed, math, para, tex


class OrientationSlide(LessonSlide):
    setting = ''
    symbols = ()
    goal = ''

    def body(self):
        self.start()
        self.put(para(self.setting,width=12,size=28), y=1.85,height=.85)
        rows=VGroup()
        for symbol,meaning in self.symbols:
            left=math(symbol,size=31)
            if left.width>3.0:
                left.scale_to_fit_width(3.0)
            left.move_to([-4.35,0,0])
            right=para(meaning,width=8.2,size=27).move_to([-2.35,0,0],aligned_edge=LEFT)
            rows.add(VGroup(left,right))
        rows.arrange(DOWN,buff=.30,center=False)
        self.put(rows,y=.1,height=2.8)
        self.takeaway(self.goal)


class PrSetup(OrientationSlide):
    lesson_deck='prereq-projections'
    setting='Work with real vectors and the usual inner product: perpendicular means zero inner product.'
    symbols=((r'K,\ K^\perp','A subspace and all directions perpendicular to it.'),
             (r'P_Kx','The component of x lying in K; the orthogonal projection.'),
             (r'Q^TQ=I','The columns of Q are an orthonormal frame for K.'),
             (r'PT=TP','Commutation: applying P then T equals applying T then P.'))
    goal='Goal: translate between subspaces, projections, frames, and invariant blocks.'


class SnSetup(OrientationSlide):
    lesson_deck='prereq-singular-norms'
    setting='A real matrix acts on vectors; orthogonal coordinates preserve lengths.'
    symbols=((r'T^T T','Map followed by its transpose: the resulting eigenvalues are nonnegative.'),
             (r's_j(T)\ge0','Singular values: square roots of the eigenvalues of T transpose T.'),
             (r'\|T\|_{\rm op},\ \|T\|_*','Largest singular value, or sum of all singular values.'),
             (r'I-W','Displacement map: original vector minus its image under W.'))
    goal='Goal: understand what different norms measure and when block costs add.'


class ExSetup(OrientationSlide):
    lesson_deck='prereq-matrix-exponential'
    setting='A is a fixed real square matrix. The scalar t is time; x is a column vector.'
    symbols=((r'A^0=I,\ A^2=AA','Powers mean repeated matrix multiplication; I is the identity.'),
             (r'e^{tA}=\sum_{k\ge0}\frac{t^kA^k}{k!}','The matrix exponential is defined by a convergent power series.'),
             (r'x(t)=e^{tA}x_0','Applying that matrix to one initial vector gives a trajectory.'),
             (r'B^T=-B','Skew-symmetry is the infinitesimal condition for preserving lengths.'))
    goal='Goal: connect the series, the differential equation, and exact legal motions.'


class VaSetup(OrientationSlide):
    lesson_deck='prereq-variations'
    setting='Work in finite real Euclidean space. K and L have the same dimension.'
    symbols=((r'W(K)=L,\ W^TW=I','A legal transporter sends the source onto the target and preserves lengths.'),
             (r'P=P_K','The orthogonal projection onto the source subspace.'),
             (r'W(t)=We^{tB}','A curve through W, made by composing with a small source motion.'),
             (r'\phi(t)=F(W(t))','The objective restricted to this curve is an ordinary scalar function.'))
    goal='Goal: derive necessary conditions at a minimizer without shrinking the feasible set.'


class MmSetup(OrientationSlide):
    lesson_deck='operators-minmax'
    setting='Real symmetric n by n matrices have orthonormal eigenbases and real eigenvalues.'
    symbols=((r'\lambda_0\ge\cdots\ge\lambda_{n-1}','Eigenvalues are listed in decreasing order, starting at index zero.'),
             (r'\rho_A(x)=x^TAx,\ \|x\|=1','The Rayleigh quotient measures A along a unit direction.'),
             (r'\|H\|_{\rm op}','The largest possible output length of H on unit vectors.'),
             (r'V,\ \dim V=k+1','A candidate subspace over which we optimize the worst direction.'))
    goal='Goal: reconstruct each eigenvalue variationally, then bound its perturbation.'


class PoSetup(OrientationSlide):
    lesson_deck='operators-polar'
    setting='A is a real or complex linear map between finite inner product spaces; singular maps are allowed.'
    symbols=((r'A^*','The adjoint: transpose in real coordinates, conjugate transpose in complex coordinates.'),
             (r'|A|=(A^*A)^{1/2}','Operator modulus: the unique positive square root, not entrywise absolute value.'),
             (r'\ker A,\ (\ker A)^\perp','The collapsed input directions and their perpendicular complement.'),
             (r'A=U|A|','The canonical factor U is isometric on the support and zero on the kernel.'))
    goal='Goal: construct the polar factor from the equality of output lengths.'


class SySetup(OrientationSlide):
    lesson_deck='operators-sylvester'
    setting='Begin with real self-adjoint matrices. The ordered-gap argument also applies to bounded Hilbert-space operators.'
    symbols=((r'AX-XB=R','A and B are given; X maps the B-space to the A-space; R is the residual.'),
             (r'A\ge(c+\delta)I,\ B\le cI','Quadratic-form inequalities place A above B with a gap of width delta.'),
             (r'\|X\|=\sup_{\|v\|=1}\|Xv\|','The norm here is the operator norm.'),
             (r'e^{tA}=\sum_{k\ge0}\frac{t^kA^k}{k!}','The exponential flow lets us integrate the equation.'))
    goal='Goal: explain exactly why this ordered gap bounds solution size by residual size.'


class MatchingSetup(OrientationSlide):
    setting='K and L are equal-dimensional subspaces of a finite real Euclidean space.'
    symbols=((r'W\in O(n),\ W(K)=L','Search over all length-preserving transporters, including reflections.'),
             (r'\|I-W\|_*','Sum the singular values of the full displacement, on the whole ambient space.'),
             (r'\theta_i\in(0,\pi/2]','Positive principal angles: canonical paired-plane angles between K and L.'),
             (r'M,\ \{i,j\}\in M','A matching chooses disjoint pairs of angle labels; unpaired labels are allowed.'))
    goal='Goal: prove an attained minimum over all transporters by a finite matching reduction.'


class M00Setup(MatchingSetup):
    lesson_deck='matching-proof'


class T00Setup(MatchingSetup):
    lesson_deck='matching-proof-talk'


class CpSetup(OrientationSlide):
    lesson_deck='prereq-complementary-projection'
    setting='Work in real Euclidean space. P is the orthogonal projection onto a subspace K.'
    symbols=((r'P^2=P,\ P^T=P','Projecting twice changes nothing; the projection is orthogonal.'),
             (r'Ix=x','The identity leaves the vector unchanged.'),
             (r'(I-P)x=x-Px','Subtract the projected component from the original vector.'),
             (r'K^\perp','All directions perpendicular to every vector in K.'))
    goal='Goal: see the complementary component, then distinguish projection error from motion displacement.'


class BaSetup(OrientationSlide):
    lesson_deck='prereq-basics'
    setting='A refresher and a readiness check: recognize the ideas, then decide what to revisit.'
    symbols=((r'x,\ A','A vector and a matrix: inputs and the rules that transform them.'),
             (r'\langle x,y\rangle,\ \theta','Inner products and angles: measuring alignment and perpendicularity.'),
             (r'Av=\lambda v','Eigenvectors: directions a matrix only scales.'),
             (r'f^\prime(t),\ \int_a^b f(t)\,dt','Derivatives and integrals: rates of change and accumulation.'))
    goal='Recognize the basic language; the later lectures develop the specialized tools.'


class YsSetup(OrientationSlide):
    lesson_deck='yws-population-gap'
    setting='Real symmetric p by p matrices; eigenvalues listed in decreasing order. The theorem is deterministic.'
    symbols=((r'\widehat A=A+H','Population matrix A, estimated matrix A-hat, perturbation H.'),
             (r'V,\widehat V\in\mathbb R^{p\times d}','Orthonormal eigenframes at the same ordered positions r through s.'),
             (r'd=s-r+1','Number of selected eigenvectors; paper indices start at one.'),
             (r'g>0','Population separation at the exterior boundaries of the selected block.'))
    goal='Goal: prove a population-gap sine bound, then an orthogonally aligned frame bound.'


class PvSetup(OrientationSlide):
    lesson_deck='operators-pvm'
    stage_labels=('Why select?', 'Build the PVM', 'Use the selection', 'Recap')
    setting='Begin with a self-adjoint matrix; then extend the selection picture to Hilbert spaces.'
    symbols=((r'A','The operator whose spectral components we want to select.'),
             (r'B\subseteq\mathbb R','A region of spectral values: begin with an interval.'),
             (r'E(B)','The orthogonal projection that keeps the components selected by B.'),
             (r'\text{select}\ \to\ \text{measure}\ \to\ \text{weight}','Which components? How much of a vector? What operator do the weights build?'))
    goal='Can we keep a spectral region without relying on an eigenvector list?'


class RrSetup(LessonSlide):
    lesson_deck='operators-rayleigh-ritz'
    stage_labels=('Search space', 'Small model', 'Full residual', 'Recap')

    def body(self):
        from manim import Create, Transform, Indicate, SurroundingRectangle
        from dkvis.learning.rayleigh_ritz.visuals import TrialPlane, matrix_tiles, formula
        from dkvis.slide_style import TRIAL, MUTED
        self.start()
        self.put(tex('A smaller problem must still be checked in the original space.',size=27),y=1.95,height=.6)
        rows=VGroup()
        for expression,description,y,color in [
            ('A=A^T','Original operator: the full eigenproblem.',1.0,CURRENT),
            (r'\mathcal T\subseteq\mathbb R^n','Trial space: the candidate vectors.',-.2,TRIAL),
            ('Q^TQ=I','Frame: length-preserving trial coordinates.',-1.4,TRIAL)]:
            rows.add(self.put(stack(formula((expression,color),size=33),
                                    tex(description,size=24),buff=.18),'left',y=y,height=.95))
        tiles=matrix_tiles(4,CURRENT,cell=.24).move_to([3.35,1.1,0])
        view=TrialPlane(origin=(3.35,-.55,0),scale=.47)
        basis=view.basis()
        self.add(tiles,view,basis,tex('A',size=26,color=CURRENT).next_to(tiles,LEFT))
        self.takeaway('Search space, small model, full residual: three parts of one approximation.')
        focus=SurroundingRectangle(rows[0],color=CURRENT,buff=.16)
        self.play(Create(focus),Indicate(tiles,color=CURRENT),run_time=1)
        self.play(Transform(focus,SurroundingRectangle(rows[1],color=TRIAL,buff=.16)),Indicate(view.plane,color=TRIAL),run_time=1)
        self.play(Transform(focus,SurroundingRectangle(rows[2],color=TRIAL,buff=.16)),Indicate(basis,color=TRIAL),run_time=1)
