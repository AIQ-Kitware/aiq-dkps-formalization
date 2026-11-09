# Proof of the real trace-norm matching formula

Independent compact presentation with thirteen proof scenes, a short cover,
local setup, numerical bonus, and study questions. The audience is
assumed to know principal angles, singular-value norms, orthogonal spectral
decompositions, and compact variational arguments. The talk introduces its own
gradient and phase constructions but does not teach those prerequisites.

The `Why:` and `Recall:` fields supply slide metadata and reference notation;
they are excluded from speech. Each `<!-- beat -->` starts the narration for
the next animated build. Exported `presentation.txt` and individual `.txt`
files contain only the spoken script, with slide titles in the combined file.

Mathematical source: the matching theorem and proof in
`papers/dk_formalization_journal/formalization_enabled_extension.tex`.
Lean endpoint: `exists_minimizing_real_nuclear_transport_matching` in
`DavisKahan/FiniteDimensional/DirectRotation/RealNuclearMatching.lean`.

Numerical reference: https://networkx.org/documentation/stable/reference/algorithms/generated/networkx.algorithms.matching.max_weight_matching.html

## TTitle: The real trace-norm matching proof

Why: Follow an unrestricted geometric minimum through its matching reduction.
Recall: The main proof concerns finite real orthogonal transport.

The real trace-norm matching proof.

## LectureOutcomes: The ideas to carry away

Why: See the conclusions before the details.
Recall: The local setup follows this overview.

The unrestricted real trace-norm minimum equals a matching value. A smooth auxiliary minimum supplies the invariant-block reduction. A uniform limit and explicit transporters establish the trace endpoint. This is a specialist proof presentation. Its destination is an equality with attainment, over all orthogonal transporters of the two equal-dimensional spaces. The lower bound must cover arbitrary mixing; the upper bound must construct an actual map.

## T00Setup: Local notation for the matching argument

Why: Read the proof independently of the longer study deck.
Recall: $W\in O(n)$, $W(K)=L$; $\theta_i$: positive principal angles; $M$: matching.

K and L are equal-dimensional real subspaces, and W ranges over the full orthogonal group, including both determinant signs. The full displacement cost is the sum of the singular values of identity minus W on the ambient space. Positive principal angles are the canonical paired-plane angles between K and L; equivalently, their cosines come from singular values of frame overlap. Repeated angles retain separate labels. A matching is a set of disjoint pairs of these labels, with unmatched vertices allowed. We will use stationarity at a chosen minimizer to derive blocks; we do not assume every feasible map already has that structure. This talk supplies its proof-specific notation locally and assumes the usual spectral and variational background.

## T00Statement: Exact real trace-norm transport

Why: The unrestricted orthogonal minimum is a finite matching problem.
Recall: $K,L\subset\mathbb R^n$ have equal dimension; $\theta_i>0$ are principal-angle labels.

Fix two equal-dimensional real subspaces. We minimize the full trace norm of
identity minus W over every ambient orthogonal transporter. The theorem expresses
this minimum as a matching of the positive principal-angle labels. An unmatched
angle has the cheaper rotation-or-reflection cost, a sub i. A selected pair has
cost b sub i j, four times the sine of half their angle sum. Repeated angle values
retain distinct labels. Zero angles can be fixed, and right angles are allowed.
The assertion includes attainment. The main proof question is why arbitrary
mixing of many principal planes cannot improve this matching value.

## T01ProofStrategy: Find the decomposition at a minimizer

Why: The lower bound must allow arbitrary mixing of principal planes.
Recall: $\mathcal F=\{W\in O(n):W(K)=L\}$; $\Phi_p(W)=\sum_k s_k(I-W)^p$.

We first work with a power p strictly between one and two. The power cost is
differentiable even at zero displacement singular values. The transport fiber
is nonempty and compact, so choose a global minimizer. Principal-angle geometry
describes the constraints, but it does not make this minimizer block diagonal.

<!-- beat -->

Stationarity will provide the missing structure. We derive a spectral gradient
whose interaction with the source reflection forces common invariant blocks
with one or two source directions. We then solve those local problems, recover
a matching, and pass the minimum values to the trace-norm endpoint.

## T02Stationarity: The gradient has zero diagonal blocks

Why: Feasible variations relate the minimizer to the source decomposition.
Recall: $P=P_K$, $Q=P_L$, $J_{\mathrm{src}}=2P-I$; $G$ is the right-variation gradient.

Let P and Q be the source and target projections. For a skew-symmetric B
commuting with P, right multiplication by the exponential of t B stays in the
transport fiber. The first variation is minus the trace of G B. On a rotation
plane, G is the phase-cost derivative times the oriented quarter-turn; on the
scalar plus-one and minus-one eigenspaces it is zero. This definition also gives
commutation of G with W.

<!-- beat -->

Now test stationarity with B equal to P G P. This is an admissible skew direction.
The vanishing derivative is exactly the squared Frobenius norm of P G P.
The complementary compression vanishes by the same argument. Thus G is off
diagonal in source coordinates, or equivalently, the source reflection
anticommutes with G. These conditions constrain the gradient while retaining
the original unrestricted minimizer.

## T03TwoPhases: A gradient level has at most two phases

Why: A scalar derivative equation limits the spectral complexity of each level.
Recall: $V_g=\ker(-G^2-g^2I)$, $g>0$; multiplication by $i$ is $\mathcal I_g=G/g$.

Decompose by the eigenspaces of minus G squared. Both W and the source reflection
preserve them. On a positive level g, dividing G by g defines a complex structure
on the original real space. W becomes complex unitary, and the source reflection
acts as conjugation because it reverses that complex structure.

<!-- beat -->

Every eigenphase of W on this level solves f prime of the phase equals g.
For p between one and two, this derivative increases once and then decreases.
The horizontal level therefore meets its graph at most twice. W is consequently
a linear combination of one orthogonal phase projection and its complement.
It remains to split this projection simultaneously with the conjugation.

## T04CommonBlocks: The projection closes a coordinate plane

Why: The phase projection and conjugation yield real blocks of dimension at most four.
Recall: $E=X+iY$, $X^T=X$, $Y^T=-Y$; the coordinates make $J_{\mathrm{src}}$ conjugation.

Write the phase projection as X plus i Y in conjugation-adapted coordinates.
Self-adjointness and idempotence give the displayed real matrix identities.
Choose a unit eigenvector u of X with eigenvalue lambda. The vector Y u has
eigenvalue one minus lambda, and applying Y again returns minus lambda times
one minus lambda times u.

<!-- beat -->

For an interior lambda, normalize Y u to obtain v. Skew-symmetry gives an
orthonormal pair, and its real coordinate span is invariant under both X and Y.
Its complex span is therefore invariant under the phase projection, W, and
conjugation. In the original real space this has basis u, v, i u, i v.
Conjugation fixes the first two and negates the other two, so exactly two
directions belong to the source. Orthogonal complements remain invariant,
allowing the construction to be iterated, including repeated eigenvalues.

## T05BlockAccounting: The blocks preserve the whole problem

Why: Constraints, principal-angle labels, and displacement cost split together.
Recall: Each block is invariant under $W$, $P$, and $Q=WPW^T$.

At lambda zero or one, Y u vanishes and a real coordinate line gives a
two-dimensional real block with one source direction. On the zero-gradient
space, W has only eigenvalues plus one and minus one. Apply the standard
two-projection decomposition to P and the minus-one spectral projection.
This supplies invariant lines and planes. A minus-one line can be replaced by
identity at smaller cost, so a minimizer fixes its one-dimensional pieces.

<!-- beat -->

The resulting two- and four-dimensional blocks preserve P and W, hence also Q.
Both the displacement singular-value list and the principal-angle list split
over them. The power cost adds, and each nontrivial block contains at most two
angle occurrences. This is a decomposition of the chosen smooth minimizer,
with exactly the constraint and cost information required for matching.

## T06LocalFibers: Solve the one- and two-angle fibers

Why: The block calculation must include every local orthogonal competitor.
Recall: $h=(\theta_i+\theta_j)/2$, $d=(\theta_i-\theta_j)/2\ge0$; $D$ is the displayed direct rotation.

On a one-angle block, the optimal rotation contributes twice f p of theta,
and a reflection contributes two to the power p. Their minimum is a sub i of p.

<!-- beat -->

For two angles, use source and complementary principal coordinates. Let D be
the direct rotation displayed here. Every transporter is D times a block
diagonal pair of arbitrary two-dimensional orthogonal matrices. Indeed,
multiplying by D transpose preserves the source and its complement. This
parametrization retains mixing between the original principal planes.
We now minimize on this entire local fiber, keeping both determinant components.

## T07PhaseRectangle: Locate the two-angle phases

Why: Trace identities turn the local matrix problem into a rectangle of phase parameters.
Recall: $0\le d\le h$, $h+d\le\pi/2$; the two eigenphase pairs are $x+y$ and $x-y$.

First take determinant plus one. The two free factors are either both rotations
or both reflections. Parametrize their rotation angles by r plus s and r minus s.
The cosine formulas shown define x and y. For both kinds of factors, these
parameters lie in the displayed rectangle; the reflection bounds use h plus d
at most pi over two.

<!-- beat -->

The traces of W and W squared identify its eigenphases. Put a equal to cosine x
and b equal to cosine y. Block multiplication gives the two displayed traces.
Since an orthogonal four-by-four matrix of determinant one has a reciprocal
characteristic polynomial, these traces determine the polynomial. Its quadratic
factorization yields phases x plus y and x minus y. Thus the rectangle describes
the actual spectrum used to evaluate the displacement cost.

## T08EdgeReduction: Compare the rectangle with an attainable edge

Why: Both folded phases can be decreased to an edge realized by actual transporters.
Recall: $b_{ij}(p)$ is the positive-determinant pair minimum; $f_p$ increases on $[0,\pi]$.

Fold the phase point across pi if its coordinate sum exceeds pi; the cost is
unchanged. We may then assume x plus y is at most pi. Set tau to the maximum
of d and h minus the absolute difference of x and y. The rectangle bounds give
tau between d and h. They also give the two displayed comparisons: h plus tau
is no larger than x plus y, and h minus tau is no larger than their absolute
difference.

<!-- beat -->

Monotonicity of the phase cost now bounds this competitor below by the edge cost
at x equal to h and y equal to tau. The animation compares phase values.
Every point of that edge is realized by choosing both free factors to be the
same rotation, with the displayed cosine for gamma. Consequently the edge
minimum is exactly the positive-determinant block minimum, not merely a bound.

## T09OtherComponents: Include reflections and zero angles

Why: Reflections and common directions must not lower the proposed local costs.
Recall: For determinant $-1$, the spectrum is $1,-1,e^{it},e^{-it}$ with $0\le t\le\pi$.

For determinant minus one, one free factor is a rotation and the other a
reflection. Their trace is bounded in absolute value by twice the cosine of
the smaller principal angle. The rotational phase is therefore at least that
angle. The displacement cost is at least a reflection cost plus the smaller
angle's rotation cost, hence at least the sum of the singleton minima.
The positive-determinant minimum already compares with the two-rotation and
two-reflection choices. Together these give the unrestricted local minimum:
the smaller of the paired cost and two singleton costs.

<!-- beat -->

A zero angle cannot be a cheaper extra partner. Pairing it with theta collapses
the scalar interval to its single endpoint and gives twice f p of theta,
which is at least the positive angle's singleton cost. Thus zero-angle
directions can be fixed, and only the original positive labels are needed.

## T10MatchingEquality: Recover the two global inequalities

Why: Local block minima give exactly the matching minimum for $1<p<2$.
Recall: $C_p(M)$ adds pair costs on selected edges and singleton costs on unmatched labels.

The local estimates are ready. We now assemble them into the lower inequality for an arbitrary minimizing transporter and compare with the explicit matching constructions. For any matching, choose an attaining local transporter for each selected pair
and each unmatched angle, and use identity on the common directions. The
orthogonal sum is feasible and has exactly the matching cost. This proves
that the unrestricted minimum is at most the matching minimum.

<!-- beat -->

Conversely, take the smooth global minimizer and its common-block decomposition.
Every restriction must minimize its local transport problem: replacing a
nonminimal restriction would lower the global cost. A plane contributes a
singleton, and a four-dimensional block contributes a pair or two singletons.
Each angle occurrence belongs to exactly one block. These choices form a
matching with the same cost as the minimizer, proving the reverse inequality.

## T11TraceEndpoint: Pass the minimum values to the trace norm

Why: Uniform convergence removes the auxiliary exponent and gives explicit block weights.
Recall: All displacement singular values lie in $[0,2]$; pair intervals $[d,h]$ are fixed and compact.

Let p approach one from above. The scalar power function converges uniformly
to the identity on the interval from zero to two. This gives uniform convergence
of the ambient costs, with the dimension factor shown. The scalar pair costs
converge uniformly on their fixed compact intervals, and there are only finitely
many matchings. Both minimum values therefore converge. No choice of a
convergent sequence of minimizers is required.

<!-- beat -->

The singleton weight has the stated rotation-or-reflection form. At p equal to
one, the pair expression is eight times sine of half h times cosine of half tau.
It is nonincreasing in tau, so its minimum is at tau equal to h, with value
four sine h. One rotational phase is now twice h, the sum of the principal
angles, while the other is zero. The attaining paired block has a moving
plane and a fixed plane. These are precisely the theorem's trace-norm weights.

## T12Attainment: Solve the matching and assemble an attainer

Why: The structural proof becomes an explicit finite optimization and construction.
Recall: The edge weight is $g_{ij}=a_i+a_j-b_{ij}$; unmatched labels remain allowed.

The unrestricted real trace-norm minimum equals a matching value. A smooth auxiliary minimum supplies the invariant-block reduction. A uniform limit and explicit transporters establish the trace endpoint. Here is how the preceding argument fits those conclusions. Subtract each paired cost from its two singleton costs to obtain the edge weight.
The trace minimum is the all-singleton baseline minus the maximum total weight
of a matching. For principal angles thirty, forty-five, and seventy-five
degrees, the maximum-weight edge pairs the first two labels and leaves the
third unmatched.

<!-- beat -->

The paired block rotates one plane by seventy-five degrees and fixes another;
the remaining principal plane uses its cheaper reflection. Their orthogonal sum
has trace displacement about four point four three five zero and is globally
minimal over every ambient orthogonal transporter. The proof rests on
stationarity, common invariant blocks, unrestricted local minima, and uniform
continuation to the trace norm. A finite matching supplies both the value and
an actual attainer.

## MatchingComputation: Bonus: implementing the matching reduction

Why: Separate a numerical graph solver from the proof of the reduction.
Recall: $a_i$: singleton cost; $b_{ij}$: pair cost; $g_{ij}=a_i+a_j-b_{ij}$.

As an optional numerical bonus, turn the exact reduction into code. On this card, a sub i denotes a singleton cost, and b sub i j denotes the paired cost. The edge saving g sub i j is the sum of the two singleton costs minus the pair cost. Build one vertex per angle label and weight each edge by its pair savings. A general-graph maximum-weight matching algorithm selects disjoint pairs; a bipartite assignment solver would impose an extra restriction. NetworkX exposes a blossom-based implementation. Keep maxcardinality false, because we maximize savings rather than the number of paired labels. Recover the actual orthogonal transporter from the selected local blocks, then verify its constraint and displacement cost. Floating-point weights can select a slightly suboptimal matching near a tie, so precision is part of the numerical implementation, separate from the exact reduction proved in the lecture.
