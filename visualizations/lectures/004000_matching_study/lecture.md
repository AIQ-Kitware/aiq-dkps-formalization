# The matching proof: a learner's narrated walkthrough

Each section names one Manim scene. `Why:` is the motivation shown beneath its
title; `Recall:` is a local notation reminder. Neither metadata line is sent to
TTS. A `<!-- beat -->` marker starts a new narrated build: the next animation
plays when that part of the explanation begins. Complete slide scripts and
individual build scripts are both exported for offline study and speech.

Numerical reference: https://networkx.org/documentation/stable/reference/algorithms/generated/networkx.algorithms.matching.max_weight_matching.html

## MTitle: Real trace-norm matching

Why: Follow an unrestricted geometric minimum through its matching reduction.
Recall: The main proof concerns finite real orthogonal transport.

Real trace-norm matching.

## LectureOutcomes: The ideas to carry away

Why: See the conclusions before the details.
Recall: The local setup follows this overview.

An optimal orthogonal transporter attains a finite matching value. Stationarity derives the small blocks rather than assuming them. Local block bounds and attaining constructions prove opposite inequalities. The cost is the trace norm of the displacement on the entire real ambient space. We will first see the paired-plane savings, then explain why arbitrary mixing cannot do better. Zero angles can be fixed and right angles are allowed.

## M00Setup: The objects in this proof

Why: Keep the admissible maps distinct from the finite matching.
Recall: $K,L$: subspaces; $W$: transporter; $\theta_i$: principal angles; $M$: matching.

Here is a local dictionary for the proof. K and L are subspaces of the same dimension in real Euclidean space. O of n is the group of all length-preserving linear maps, including reflections. The constraint W of K equals L specifies a whole target subspace, not the image of each selected basis vector. The trace norm of identity minus W adds the singular values of the displacement on the entire ambient space. Principal angles are canonical angles between paired source and target directions; their cosines are the singular values of the overlap of orthonormal frames. We use the positive angle labels, including right angles. A matching selects disjoint pairs of labels. Unmatched labels stay single. A matching will encode an attaining construction, not a unique representation of every admissible W.

## M00Problem: The optimization problem

Why: What freedom do we have when only a whole subspace must reach its destination?
Recall: $K$: source; $L$: target; $W$: orthogonal map with $W(K)=L$.

The geometric freedom in this problem is what will eventually make matching possible.

We have two subspaces, K and L, of the same dimension inside a finite-dimensional real
Euclidean space. Orthogonal means that W preserves lengths and angles; it may rotate or
reflect. We want an orthogonal transformation W that carries K onto L. We are not
prescribing where each individual source vector must go. The constraint concerns the
whole subspace.

Among all these transformations, we minimize the trace norm of identity minus W.
Identity, written I, is the do-nothing map. I minus W sends a vector to the difference
between its original and moved positions. The singular values are the stretch factors of
this displacement map along its principal axes. The trace norm adds those stretch
factors over the whole space, including directions outside K. Theorem five says that we
can obtain this minimum by solving a finite maximum-weight matching problem. Our task is
to understand why a search over arbitrary orthogonal matrices can reduce to choosing
pairs of angle labels.

## M00BlockMeaning: A block means vectors stay in their own piece

Why: What does a block say geometrically about where vectors can go?
Recall: $A_{ij}$: input piece $j$ to output piece $i$; each cell can itself be a whole matrix.

Before using blocks in a proof, let's give the word a geometric meaning. Split a space
into two perpendicular pieces. The two panels represent those pieces; they are not the
same plane drawn twice. A vector in the first piece may rotate around inside it. That is
still staying in the piece. But if its image acquires a component in the other piece,
the map couples the pieces. The off-diagonal matrix blocks record exactly that coupling.
The block row tells us where the output lands; the block column tells us which piece
contains the input. A one-zero block, for example, carries inputs from piece zero into
an output component in piece one.

<!-- beat -->

When the off-diagonal blocks are zero, an input in the first piece has no output in the
second, and conversely. Each piece is invariant: vectors that start there stay there.
The map becomes two smaller maps that can be considered independently. A diagonal block
may itself be a large matrix. We have not made the map diagonal on individual vectors.
Our eventual goal is to find small pieces preserved by the transporter and by both
subspace projections.

## M01PrincipalPlanes: Geometry gives principal planes

Why: How can we describe the relative position of two large subspaces?
Recall: $u_i$: source unit vector; $v_i$: matched target vector; $q_i$: perpendicular partner; $\Pi_i$: their plane.

We first need a manageable description of the two subspaces, before making any claim
about an optimal map.

Principal angles lie between zero and ninety degrees because the subspaces have no
prescribed orientation. They describe the best-aligned directions of the source and
target, then their next independent directions, and so on. Choosing corresponding unit
vectors makes each source vector overlap only with its matched target vector. The
singular value decomposition, abbreviated SVD, of the matrix of basis overlaps gives
these vectors and angles. Call a matched source unit vector u sub i and its target unit
vector v sub i. For a positive angle, remove v sub i's component along u sub i, then
divide by sine of the angle to make the remaining perpendicular vector unit length. Call
it q sub i. The span of u sub i and q sub i means all their linear combinations. Each
positive angle has a source direction and a target direction lying in a two-dimensional
principal plane. Principal planes belonging to different angle labels are orthogonal.

In the picture, each little plane shows one source line in amber and its target line in
blue. The panels represent mutually orthogonal coordinate planes, rather than planes
physically lying on the screen. Common zero-angle directions can be fixed. This
describes the two subspaces. It does not say that an optimal W must preserve the
individual principal planes. That is the distinction we will need to keep in mind when
proving the lower bound.

## M02Singleton: Transport one principal plane

Why: What are the cheapest ways to carry just one line onto another?
Recall: $s_i$: the best trace cost for one angle; rotations and reflections are allowed.

These are the small constructions whose costs our eventual structural argument must
recover.

Start with one principal angle, theta. A planar rotation through theta carries the
source line onto its target. Its displacement has two equal singular values, each equal
to two times sine of half theta. Adding them gives a trace cost of four times sine of
half theta.

There is another choice. A reflection across an angle-bisecting line also carries the
source line onto the target. Its eigenvalues are positive one and negative one, so its
displacement singular values are zero and two. Its trace cost is therefore two. The best
singleton cost is the smaller of the rotation cost and two. The source and target are
unoriented lines, which is why reflection is an admissible competitor.

## M03PairedBlock: Let two principal planes interact

Why: Could letting two principal planes interact lower the cost?
Recall: $\oplus$: combine perpendicular pieces; $R_t$: planar rotation through $t$; $e_{ij}$: paired trace cost.

A singleton construction does not use all the freedom in mapping a whole subspace. Let
us try sharing that freedom between two angle labels.

We can also group two principal planes into a four-dimensional block. Inside that block,
we allow an orthogonal transporter to mix the two source directions and their
complementary directions. This is more freedom than transporting each principal plane
independently.

At the trace-norm endpoint, there is a paired construction whose cost is four times sine
of half the sum of the two principal angles. In a suitable invariant basis, it rotates
one real plane through the sum of the angles and fixes another real plane. These moving
and fixed planes are generally different from the two original principal planes. The
diagram shows the dimensions and grouping; it is not a literal drawing of
four-dimensional geometry. We will justify both the construction and the comparison with
other transporters later. Here R with an angle subscript means rotation through that
angle, and I sub two means the identity map on a plane. The direct-sum symbol means
combining the perpendicular pieces as independent coordinates.

## M04Graph: Encode pair choices in a general graph

Why: How do we record pair choices without using an angle twice?
Recall: $M$: disjoint pairs; $g_{ij}=s_i+s_j-e_{ij}$: savings from one pair.

We can already record our constructions in a finite graph. This organizes the
candidates; proving that they are enough remains our main task.

Now put one vertex at each positive principal-angle label. Every edge is a possible
pair. A matching chooses edges so that each label is used at most once. For example,
pairing labels one and two leaves label three unmatched. Taking both edge one-two and
edge two-three is disallowed because label two would belong to two blocks.

Each vertex has its singleton cost. The weight of an edge is the cost of its two
singletons minus their paired cost. Starting from all singletons, selecting an edge
subtracts that weight. Therefore we maximize total edge weight. The empty matching is
allowed, and negative edges need not be selected. In our thirty, forty-five, and
seventy-five degree example, the best edge pairs thirty and forty-five. The seventy-five
degree label uses its singleton reflection.

## M05TwoBounds: The question now: could many-way mixing win?

Why: What still prevents the construction from being a proof of optimality?
Recall: Known: a matching builds a map. Needed: unrestricted mixing cannot do better.

You already know the two-inequality proof pattern. We have the easy construction: select
singles and pairs, build their maps, and add the costs. The question that remains is
geometric. Could an unrestricted map, mixing many principal planes, beat all those
constructions?

Here is our route through the difficult part. Choose a globally best map for a smooth
cost. Construct changes that keep the same source and target. Use the fact that none can
lower the cost to obtain equations. Those equations will reveal common invariant pieces
containing only one or two angle entries. Then we can price each piece. Keep this
destination in mind: the next several slides are trying to explain why many-way mixing
cannot improve the minimum.

## M06SmoothCost: Use a differentiable cost first

Why: How can the cost of a small wiggle reveal the structure of a minimizer?
Recall: $\Phi_p$: sum of displacement singular values to power $p$, with $1<p<2$.

Our plan is to learn structure from the cost of small legal changes. For that we want a
cost with a derivative, even when some displacement vanishes.

The trace norm is a sum of singular values. At zero singular values it need not be
differentiable. This makes a direct first-derivative argument difficult. Instead, choose
an exponent p strictly between one and two and sum the p-th powers of the displacement
singular values. Call this cost phi p.

The graph shows why the exponent helps: absolute t has a corner at zero, whereas
absolute t to a power greater than one has derivative zero there. The corresponding
finite-dimensional matrix cost is differentiable too, including at zero displacement
singular values. The study note derives this using a symmetric matrix dilation. We will
prove the matching equality for these smooth costs, then let p approach one from above.
We pass minimum values to that limit; we do not assume one transporter minimizes every
exponent.

## M07Existence: Choose a best map before knowing how to find it

Why: Can we reason about a best map even before we know how to find it?
Recall: $\mathcal F$: all valid candidate maps; compact here means closed and bounded.

To learn structure from optimality, first choose a genuinely best map. This is an
existence argument; we do not yet know how to find it. Call a map feasible when it
preserves lengths and carries the whole source K onto L. Write script F for the
collection of all these valid candidates.

There is at least one: map an orthonormal basis of K to one of L and extend the map to
the perpendicular complements. This set is bounded because the columns of an orthogonal
matrix have length one. It is closed because limits preserve orthogonality, and the
images of a fixed source basis stay inside the closed target subspace. Equal dimensions
then ensure that these images span L. In a finite-dimensional space, closed and bounded
means compact. A continuous cost reaches its minimum on such a nonempty set. So we may
choose a best W for our fixed exponent p. We have established its existence, without
assuming any special structure for it.

## M08FeasibleCurves: Move the vectors; keep their destination plane

Why: Can we construct a new map that still sends the same source onto the same target?
Recall: $V_t$: pre-rotation inside the source; $W_t=WV_t$: a new feasible map.

We need to learn something about a best map, but we can only test changes that obey the
transport condition. Start with any orthogonal W that sends K onto L. Watch the two
marked basis vectors in K and their images in L. The planes themselves are fixed. The
task prescribes where the whole source goes, not which target vector each marked source
vector must reach.

<!-- beat -->

Now construct a rotation V at time t inside K. Follow it by the original W. The marked
vectors move around inside K, so their images move around inside L. Yet the image of the
whole plane stays exactly L. This gives an actual new feasible map, W times V at time t.
The animation is a three-dimensional example of this construction. We can write down
these rotations; their existence is not an extra assumption about an algorithm.

<!-- beat -->

In a larger space we can also rotate independently inside the perpendicular complement
of K. Combine the two rotations and neither part leaks into the other. These are changes
of the input before applying W. Our minimizer is still allowed to mix its own principal
planes. We have only constructed a family of legal tests. Next we will express the same
geometric construction in the projection notation used by the proof.

## M08ProjectionMeaning: The projection P records which part lies in K

Why: How do we write the difference between staying inside K and leaving it?
Recall: $P$: keeps the source component; $Q$: keeps the target component.

Why introduce P? We need a short way to check whether a change carries source vectors
out of the source. P is the orthogonal projection onto K. Given a vector x, P x keeps
its source component and discards the perpendicular component. Identity minus P keeps
the other component. The drawing uses a line as the source so both components can be
shown on screen.

<!-- beat -->

In coordinates adapted to K and its perpendicular complement, P therefore has identity
in the source block and zero in the complement block. The symbols zero and identity here
stand for whole blocks, whose sizes depend on the dimensions. If a change acts
independently in these two spaces, it commutes with P: choosing the source component
before or after that change gives the same result. The next slide constructs exactly
such a change, so this notation will describe something we already know exists. Q
performs the same keep-or-discard operation for the target L. For an orthogonal W, the
projection onto its image of K is W P W transpose: first go back by W transpose, keep
the source component, and go forward by W. Thus saying W carries K onto L is equivalent
to saying W P W transpose equals Q. This equation records the whole-subspace constraint.

## M08CommutingConstruction: Construct B first; commutation follows

Why: Why are commuting directions available rather than merely wished for?
Recall: $a,b$: chosen speeds; $B$: rotation velocity; $e^{tB}$: rotation after time $t$.

Here is a key idea: construct the legal test first, and read the algebraic condition
from the construction. We have already built finite rotations within the source and its
complement. B records their instantaneous velocity at time zero. For a rotating matrix
V, differentiate V transpose times V equals identity at time zero. Its velocity obeys B
transpose plus B equals zero. A matrix with this property is called skew-symmetric. To
construct B, choose any skew-symmetric matrix on K and any skew-symmetric matrix on its
complement. Put them in the two diagonal blocks and put zeros in the cross blocks. For
example, on two-dimensional pieces choose any real speeds a and b times the planar
quarter-turn matrix. This is an explicit family, with arbitrary speeds.

<!-- beat -->

Now multiply this B by P on either side. Since P keeps the source block and discards the
other block, both products keep the same upper-left block. Thus B P equals P B. We did
not assume this difficult condition and hope to find a matrix satisfying it. We built B
from independent rotations, and this equation is the algebraic record of their staying
inside the source and its complement.

<!-- beat -->

The matrix exponential is defined by the familiar power series for e to the x, now using
powers of B. For a skew rotation velocity, the exponential of time t times B is the
resulting orthogonal rotation. Transposing this series changes B to its transpose, which
is negative B, and therefore gives the inverse. That is why this finite change preserves
lengths. In the two-plane example it is just the block diagonal matrix of rotations
through a t and b t. Compose it on the right of W and the whole source still reaches L.
This family need not contain every imaginable perturbation of W. A globally best map
must resist every member of this family, and that will already force the equations we
need.

## M08StationaryTests: Every legal wiggle gives a test at the minimum

Why: What must the best map do along every legal wiggle?
Recall: $\Phi_p$: power cost; stationary means zero first derivative along every legal path.

We can now ask a concrete question about the unknown global minimizer. Pick any one of
the skew directions we just constructed, move along its feasible curve, and plot the
resulting cost against time. Since time zero is our global minimizer, this one-variable
function has a minimum there. The curve drawn here is a schematic smooth minimum, not a
numerical trace-cost computation.

<!-- beat -->

The derivative at zero must be zero. This is what stationarity means in this proof. The
statement holds for every choice of the within-source and within-complement rotation
velocities. We have not found the best W by setting a derivative to zero, and
stationarity by itself will not prove global optimality. We are using the existence of a
global minimizer to obtain necessary equations. The next job is to calculate the cost
change of one of these wiggles.

## M09RotationCost: Read displacement from a rotation chord

Why: How do we turn a small rotation into a change in the displacement cost?
Recall: $f_p(t)=(2\sin(t/2))^p$: one scalar chord cost; a real plane contributes $2f_p(t)$.

The legal changes are available. Now we need to calculate their cost-change rates,
starting with one rotation plane.

Every real orthogonal map has coordinates in which it acts by rotations on perpendicular
planes and by keeping or reversing the remaining lines. This standard decomposition
describes W itself. Its rotation planes need not be the principal planes describing K
and L. Start with the cost on one such rotation plane of W. A vector and its image under
rotation by angle t lie on the same unit circle. The displacement is the chord between
them. Its length is two times sine of half t. Every unit vector in that plane has the
same displacement length.

Algebraically, identity minus the rotation, transpose times itself, is four times sine
squared of half t times identity. There are therefore two equal displacement singular
values. Define the scalar rotation cost f p of t as the p-th power of this chord length.
The full real plane contributes twice f p of t. The factor two comes from the two real
dimensions. We must retain it when computing the cost-change rate.

## M10SignAverage: Mixing directions: compare equal cost-change rates

Why: What if our wiggle mixes the rotation planes used to calculate the derivative?
Recall: $B_{ij}$ here uses W rotation-plane coordinates; $\mathrm{rate}(B)$ is the cost-change derivative.

The chord calculation works in W's rotation planes. But a legal wiggle need not preserve
those planes. We must account for that mixing before using the derivative formula. On
this slide, rate of B means one number: the derivative at zero of the cost along W times
the exponential of t B. The formula is written beside the name. Because the smooth cost
is differentiable, averaging directions averages these numbers.

<!-- beat -->

Use a sign change that is positive identity on one W block and negative identity on
another. It commutes with W. Conjugating by it leaves all displacement singular values
unchanged, so B and its sign-conjugated version have the same cost-change rate. Look at
their cross blocks: each appears with opposite signs. Average the two directions and
those cross blocks cancel. Thus their common rate can be computed using the diagonal
blocks alone. Repeat independent sign choices for all blocks. These are auxiliary
directions for calculating a derivative; they do not all have to preserve K.

## M11TracePairing: G stores the response to each small rotation

Why: Can one matrix collect the cost response to all small rotations?
Recall: $\varphi$: a W rotation angle; $G$: response matrix; $\operatorname{tr}$: sum of diagonal entries.

We now want to collect the cost-change calculation in one matrix. In one rotation plane,
a skew direction is a speed b times the quarter-turn matrix J zero. So the rotation
angle changes at speed b. Differentiating the plane cost, twice f p of varphi, gives
twice b times f p prime of varphi.

Put f p prime of varphi times J zero into the same block of a new matrix G. Trace means
the sum of a matrix's diagonal entries. Multiplying by b J zero and taking minus the
trace gives precisely that derivative, because the square of J zero is negative identity
on a two-dimensional plane. The displayed calculation checks the sign and the factor
two. On a line, a skew-symmetric velocity has to be zero, so the kept or reversed scalar
lines contribute zero to the first derivative. Adding the blocks, with the
sign-averaging argument from the last slide, gives rate of B equals minus trace of G B
for every skew direction. G is a compact record of all these rotation responses. Now we
can apply the legal-wiggle tests without recalculating every derivative.

## M12Stationarity: If an internal response survived, we could test it

Why: What does the inability to improve within K tell us about G?
Recall: $PGP$: the part of $G$ acting within $K$; $J=2P-I$: source reflection.

Remember our explicit family of legal velocities: any skew matrix inside K,
independently of one inside its complement. G is also skew-symmetric. Its upper-left
source block is therefore one of the allowed velocities. Choose B to equal that block
and zero elsewhere. In projection notation this is P G P: keep the input component in K,
apply G, and keep the output component in K. This choice exists for the same reason the
earlier constructed examples did.

<!-- beat -->

Stationarity says its cost-change rate is zero. The trace formula turns that into minus
trace of G B equals zero. With this choice of B, cyclically move the projections in the
trace to get minus trace of B squared. For a real skew matrix this is the squared
Frobenius norm, the sum of squares of all entries. Therefore the entire upper-left block
must vanish. We have forced a property of G by testing an actual available direction.

<!-- beat -->

Repeat inside the complement. The lower-right block vanishes too. Only cross terms
remain: G sends source vectors into the complement and complementary vectors into the
source. The reflection J keeps source vectors and reverses complementary ones. This
cross-only structure is exactly why J G J equals negative G. We will square G to remove
that sign reversal and discover invariant spaces. Notice that we have simplified G; we
have not claimed that W itself preserves K.

## M13TwoDecompositions: Two coordinate choices answer different questions

Why: Which matrix have we simplified, and in which choice of coordinates?
Recall: $W$: the actual transporter; $G$: its cost response. They are different matrices.

The derivative tests have produced structural equations at a minimizer. Their purpose is to find pieces that the relevant maps preserve, so that a global cost can be bounded one piece at a time. Before continuing, keep track of what each matrix is doing. W is the transporter whose
minimum cost we are studying. G is the cost-response matrix we built from its rotation
planes. In W's rotation coordinates, G is easy to calculate. In source and complement
coordinates, legal wiggles force G's diagonal blocks to be zero.

Those are two different coordinate choices on the same space. Do not transfer the block
picture of one directly to the other. Inside each rotation plane, G is a scaled
quarter-turn. Applying W then G therefore gives the same result as applying G then W.
This explains their commutation. What survives independently of coordinates are the two
equations: W commutes with G, and source reflection reverses G. Our purpose now is to
use them to find a third decomposition: pieces preserved simultaneously by W and by the
source and target projections. Such pieces will finally let us solve independent smaller
transport problems.

## M13InvariantBlocks: Independent pieces must work for W, P, and Q

Why: What kind of independent pieces would let us replace part of a transporter?
Recall: Invariant under $A$ means $x\in V$ implies $Ax\in V$.

Here is the second key idea: independent pieces must work for the transporter and for
the source and target together. What would a useful block decomposition actually
accomplish? If a piece is invariant under W, a vector starting there stays there after
transport. But for our constraint to split too, source and target must each split along
the same pieces. That is what invariance under the projections P and Q supplies. We need
all three maps to preserve each piece, not just W.

<!-- beat -->

The coordinate example joins directions one and three, and directions two and four.
Reorder the basis to put each pair together. The same map now appears in two diagonal
blocks. This illustrates why an off-diagonal entry in one ordering does not rule out a
useful block decomposition in another. In this example the same pieces also work for P
and Q. For our unknown global minimizer, the next slides must prove that suitable common
pieces exist. Once they do, source and target restrict to each piece and the
displacement costs add.

## M14GradientLevels: Group directions that have the same response strength

Why: How do the equations from legal wiggles produce common invariant spaces?
Recall: $V_g$: the space where $-G^2$ acts as $g^2I$; it can still be large.

We know that G crosses between the source and its complement. Applying it twice returns
to the original side. This suggests squaring it: the sign reversal under the source
reflection disappears. More precisely, negative G squared is symmetric and nonnegative.
The minus sign makes its eigenvalues nonnegative: its quadratic form at x is the squared
length of G x. These eigenvalues are squared response strengths. Collect all vectors on
which this matrix acts by multiplication by g squared. That collection is its eigenspace
at g squared; it contains every direction with that same response strength, and it can
still have many dimensions.

<!-- beat -->

Both W and the source reflection commute with negative G squared. Here is the reason
this gives an invariant piece: if the square acts on x by g squared, then applying it to
W x gives W applied to g squared x, which is g squared times W x. So W x stays in the
same eigenspace. The same reasoning works for the source projection, and then for the
target projection W P W transpose. We have obtained the common pieces we wanted. They
may still be large, so the next question is why they can be split further into
single-angle or two-angle problems.

## M15ComplexCoordinates: A quarter-turn lets us describe each pair by one coordinate

Why: Why introduce complex numbers into a real optimization problem?
Recall: $\mathcal I_g=G/g$: a quarter-turn; $J$: fixes source vectors and flips the complement.

Take a positive response-strength piece. Here negative G squared is g squared times
identity, with g positive. Divide G by g. This normalized map preserves lengths and
sends each vector through a quarter-turn: doing it twice gives negative the original
vector. Choose a unit vector u in the source part of this group. We can use its
quarter-turn partner to describe a real plane.

<!-- beat -->

Watch u move to I sub g u, then to negative u. This is exactly the real-plane action of
multiplication by the imaginary unit. We can therefore describe u and its quarter-turn
partner as the real and imaginary directions of one complex coordinate. We are not
enlarging the space or allowing a complex transporter in a different optimization
problem. We are describing pairs of real directions more economically. The source
reflection keeps the real direction and flips the imaginary one, so it becomes
conjugation in coordinates chosen from its fixed space.

<!-- beat -->

Why is that useful? W commutes with this quarter-turn. It therefore respects our new
complex coordinates, meaning it is complex-linear, and still preserves lengths, which is
called unitary. Its complex eigenvalues lie on the unit circle. Write one as e to the i
t: t is the rotation angle, also called its phase. A phase eigenspace consists of the
vectors multiplied by that same unit-circle number. At the same time, conjugation still
remembers which directions belong to the source. We must preserve both structures when
making smaller pieces. That is why the next argument involves a phase projection
together with conjugation, rather than just diagonalizing W and forgetting K.

## M16TwoPhases: One response strength allows at most two rotation angles

Why: How many different rotation angles can have the same positive cost response?
Recall: $g$: fixed response strength; $\varphi_1,\varphi_2$: phases of $W$, not principal angles.

We grouped directions by response strength g. Recall that on a rotation plane, G's
strength was f p prime of the rotation angle. So which rotation phases can occur in this
group? Look for intersections of the derivative curve with the horizontal line at g. The
curve rises and then falls, so there are at most two intersections. These phases are
rotation angles of W, not the principal angles between K and L. Differentiating f p
gives the formula on the slide. Its derivative changes sign just once in the open
interval: tangent squared of half t equals p minus one. This verifies the single peak
throughout our exponent range, rather than just for the plotted example.

<!-- beat -->

Therefore W has at most two phase values on this group. But each phase can have many
independent directions. Two phase values do not mean two dimensions. Introduce E, the
orthogonal projection selecting the first phase; identity minus E selects the other.
This is the same keep-one-component operation as P earlier, now applied to a phase space
instead of the source. This packages W using one projection. The remaining problem is to
split that projection in a way that also respects the conjugation remembering the
source.

## M17ProjectionBlocks: Follow one direction: its partner sends us back

Why: Why does following one direction lead to at most one extra partner?
Recall: $E$: keeps the first-phase component; $X,Y$: its real and imaginary matrix parts.

We need small pieces preserved by the phase projection E and by conjugation. Choose
coordinates where conjugation is ordinary complex conjugation, and separate E into its
real matrix X and imaginary matrix Y. Because E is an orthogonal projection, X is
symmetric and Y is skew-symmetric. The equations on the slide come from expanding E
squared equals E. They are useful because they tell us where following Y can take a
direction.

<!-- beat -->

Since X is real symmetric, choose a unit eigenvector u from an orthonormal eigenbasis,
and call its eigenvalue lambda. X just rescales u. The equations say Y u has length eta,
the square root of lambda times one minus lambda, and lies in X's eigenvalue one minus
lambda space. If eta is positive, normalize Y u and call that new direction v. So far we
have had to add just one partner to u.

<!-- beat -->

Here is the key return step. Follow the new direction: the same equations give Y v
equals negative eta u. We are back in the span of u and v; there is no third direction
to add. X preserves it too, so this coordinate plane closes under both X and Y.
Conjugation preserves its complex span because u and v have real coordinates. If lambda
is zero or one, Y u is zero and a single coordinate line closes already. Symmetry of X
and skew-symmetry of Y also prevent vectors in the perpendicular remaining space from
acquiring a component in this closed piece. We can therefore repeat the construction on
that remaining space. This return-to-u argument is the reason the blocks stop growing.

## M18RealBlocks: One coordinate or two becomes one angle or two

Why: How do these coordinate lines and pairs become the angle labels in our graph?
Recall: One complex coordinate has two real coordinates; $J$ fixes the source half.

We have made coordinate lines and pairs closed under the operations that matter. Now
translate the dimensions back to the original real problem. One complex coordinate has
two real directions, u and i u. A pair has four: u, v, i u, and i v. The tiles count
actual real directions; they are not a drawing of a four-dimensional solid.

<!-- beat -->

Conjugation fixes u and v and reverses their imaginary partners. Since the source
reflection is this conjugation, the fixed half is exactly the source part of the block.
Thus a two-real-dimensional block has one source direction, while a
four-real-dimensional block has two. W, P, and Q all preserve these pieces. Within each
one, W carries the source part onto the target part, so its source dimension is the
number of its principal-angle entries. These lists combine into the original angle list.
We have now reached the geometric destination promised after the construction: the
positive response-strength part splits into problems with one or two angle entries. The
pairs found here need not be W's original rotation planes or the original principal
planes.

## M19ZeroGradient: The zero response needs its own geometric argument

Why: What happens to the directions on which the cost-response matrix vanishes?
Recall: $\ker G$: vectors with $Gx=0$; $N$: projection onto the negative-one eigenspace of $W$.

We divided by g on positive groups, so we must treat the zero group separately. There
the phase derivative vanishes only at zero and pi. W has only positive-one and
negative-one eigenvalues and is a reflection. Write it as identity minus twice N, where
N projects onto the directions that W reverses. In the plane drawing, a reflection
carries the source line onto the target line.

<!-- beat -->

The two-projection decomposition for P and N splits this group into invariant lines and
planes. One way to picture that familiar construction is to take a principal vector
between their ranges and add its perpendicular partner; repeating gives independent
principal planes. Because W is built from N, and Q is W P W transpose, these same pieces
work for all the maps we need. A leftover invariant line has the same source and target
on it. If W reverses that line, switching to identity preserves feasibility and drops
its cost to zero. Global minimality excludes this unnecessary reversal. So the zero
group also leaves only one-angle planes and fixed directions.

## M20PairCoordinates: Use the same legal-pre-rotation idea inside one pair

Why: Now that pairs suffice, how do we search every map on one pair?
Recall: $D$: direct rotation; $U_0,U_1$: orthogonal changes inside source and complement.

We have finished the structural argument. Now the question changes: what is the least
cost inside a four-dimensional block with two angle entries? We must include every
competitor on that block. Choose the direct rotation D as one known map from the source
onto the target. This is a convenient reference map, not an assumption about the best
one.

<!-- beat -->

For any other transporter W, the map D transpose times W sends the source onto itself.
Being orthogonal, it also preserves the complement. It therefore has two free orthogonal
blocks, U zero and U one. Rearranging gives W equals D times that block diagonal change.
This is the same geometry as our earlier legal wiggles: first change coordinates
internally, then use a fixed map to reach the target. Here we allow every internal
orthogonal change, not only small rotations. We have reduced the local search to two
two-dimensional matrices.

## M20PhaseParameters: Introduce the two phase parameters

Why: Can we replace two free planar matrices by a few scalar angles?
Recall: $h,d$: half-sum and half-difference; $u=\cos x$, $v=\cos y$.

The structural work is behind us. We are now pricing one two-angle piece, and want
scalar coordinates for its free matrices.

Order the principal angles with theta i at least theta j. Let h be their half-sum and d
their half-difference. The sign of the determinant records whether the map preserves or
reverses orientation. For W to have determinant positive one, its two free factors must
have the same sign: either both rotations or both reflections.

For rotations, write their angles as r plus s and r minus s. Any two angles can be
written this way by taking their half-sum and half-difference. Define x and y between
zero and pi by cosine x equals cosine h times cosine s, and cosine y equals cosine d
times cosine r.

For reflections, append the planar coordinate reflection to each rotation. The
corresponding formulas are cosine x equals negative sine d times cosine r, and cosine y
equals sine h times cosine s. So far these are auxiliary parameters defined by the free
factors. The next slide checks that x plus y and x minus y actually describe W's
eigenphases.

## M20PhasePolynomial: Check the eigenphases with the characteristic polynomial

Why: Why do the auxiliary numbers x and y actually describe the spectrum?
Recall: $\chi_W(z)=\det(zI-W)$; $c_2$: its coefficient of $z^2$.

We defined convenient scalar parameters on the last slide. Now we check that they really
determine the rotation phases that enter the cost.

The characteristic polynomial of W is determinant of z identity minus W; its roots are
exactly the eigenvalues we want. Write u for cosine x and v for cosine y. Multiplying
the blocks of W gives trace W equal to four u v. The same calculation gives the
displayed trace of W squared. The coefficient of z squared in the characteristic
polynomial is one half of the difference between the square of the trace and the trace
of the matrix square. Keeping these two operations distinct is essential.

Orthogonality and determinant one make the degree-four polynomial reciprocal: its
coefficients read the same forwards and backwards. The trace fixes both the cubic and
linear coefficients, and the constant is one. These facts give the polynomial on the
slide. Multiply the two quadratic factors associated with x plus y and x minus y; the
result is that same polynomial. Its roots are therefore the four claimed phase
eigenvalues. The study note spells out the block trace multiplication if you want to
reproduce that part by hand.

## M20RectangleBounds: Put both cases in the same rectangle

Why: What range of phase parameters must we compare?
Recall: The rectangle contains both rotations and reflections of positive total determinant.

We know how the parameters describe the spectrum. Next we need the range over which a
cheaper phase choice must be sought.

In the rotation case, the absolute value of cosine x is at most cosine h. Because cosine
decreases on the interval from zero to pi, x lies between h and pi minus h. The same
argument puts y between d and pi minus d. This is the large rectangle in the diagram.

For two reflections, the cosine formulas instead put x between pi over two minus d and
pi over two plus d. They put y between pi over two minus h and pi over two plus h. These
give the smaller rectangle. It lies inside the larger one because h plus d equals the
larger principal angle, which is at most pi over two. We now have one common region
covering every positive-determinant competitor. We do not need to claim every point of
the large rectangle comes from the reflection case.

## M21PhaseRectangle: Reduce two phase parameters to an edge

Why: Can every interior phase choice be compared with a simpler edge choice?
Recall: $\tau$: one scalar in $[d,h]$; the new phases are $h+\tau$ and $h-\tau$.

Our local search covers a two-parameter region. We can simplify it if every point is no
better than some attainable point on one edge.

Let h be half the sum of the two principal angles and d half their absolute difference.
In the positive-determinant class, the matrix calculation gives phase parameters x and y
in the rectangle shown. The eigenphases occur as plus or minus x plus y, and plus or
minus x minus y.

If x plus y exceeds pi, replace x and y by pi minus x and pi minus y. This keeps the
cost and the rectangle unchanged, while making the sum at most pi. This replacement is
what folding the point means here. Set tau to the larger of d and h minus the absolute
difference of x and y. Then tau lies between d and h. The new larger phase, h plus tau,
is no greater than x plus y. The new smaller phase, h minus tau, is no greater than the
absolute difference of x and y. The scalar phase cost is increasing between zero and pi.
Moving to the displayed edge point therefore cannot increase either phase cost. The
visual movement represents this comparison of phase values, rather than a claim that the
objective decreases along a particular path of matrices.

## M22PairMinimum: Attain the scalar minimum

Why: Does that simpler edge represent actual transporters or just a lower bound?
Recall: $b_{ij}(p)$: best paired power cost; $\gamma$: angle of the free planar rotations.

The phase comparison gave a lower bound. To identify the true local minimum, we now
construct a map attaining every edge choice.

The preceding comparison supplies a lower bound for every positive-determinant
transporter. To make it an equality, we must also attain every point of the edge. Set
both free planar factors equal to rotation through gamma, where cosine of gamma equals
cosine of tau divided by cosine of d. This ratio lies between zero and one, and the
denominator is positive.

The resulting transporter has phase parameters x equal to h and y equal to tau. Its cost
is twice f p of h plus tau plus twice f p of h minus tau. We minimize this continuous
scalar function over the closed interval from d to h, so a minimum is attained. The
curve is an illustration of that scalar optimization for p equal to three halves. The
rectangle comparison and this explicit attainer establish both inequalities for the
positive-determinant block cost.

## M23Determinants: Include reflections and two singletons

Why: Have we included reflected competitors as well as rotations?
Recall: $a_i(p)$: best singleton power cost; $b_{ij}(p)$: paired power cost.

Before declaring the local search finished, check its scope: the transporter may reverse
orientation, and two separate singleton choices are also allowed.

A four-dimensional transporter can also have determinant negative one. Its eigenvalues
are positive one, negative one, and a conjugate rotational pair. The free-factor
parametrization bounds its absolute trace by twice cosine of the smaller principal
angle. Since the trace is twice cosine of its rotational phase, that phase cannot be
smaller than the smaller principal angle.

The least cost in this class is attained by reflecting on the larger-angle plane and
rotating on the smaller-angle plane. Compare this with the positive pair minimum and the
four independent rotation-or-reflection choices. The full block minimum becomes the
smaller of the paired cost and the sum of the two singleton costs. That last comparison
is essential: using one four-dimensional block does not force us to choose a matching
edge. It may be better to leave both labels unmatched.

## M24BlockOptimality: Replace one piece without disturbing the others

Why: Why must each independent part of a globally best map also be best locally?
Recall: Common invariant blocks preserve the source, target, and transporter simultaneously.

Recall what our common invariant pieces bought us: each contains its own source part,
target part, and transporter. Suppose one restriction of the global minimizer had a more
expensive cost than another transporter for that same local problem. Replace only that
restriction. All the other pieces are untouched, and the new map still carries the
entire source onto the entire target.

<!-- beat -->

The squared displacement matrix is block diagonal, so its singular values combine from
the pieces and their power costs add. A cheaper replacement would lower the total cost,
contradicting global minimality. Therefore every piece uses the minimum local cost we
calculated. This is the point where global optimality does more than stationarity. We
used derivatives to reveal the pieces; we use a replacement argument to say that each
piece really is cheapest.

## M25MatchingEquality: Prove both bounds for the smooth cost

Why: How do the independent pieces become a matching with the very same cost?
Recall: $C_p(M)$: paired power costs on selected edges plus singleton costs on unmatched labels.

We can now return to the question posed before the derivative detour. The unrestricted
minimizer has small optimal pieces; what do those pieces mean in our graph?

Call C sub p of M the cost of matching M using the paired power costs on its edges and
singleton power costs on unmatched labels. We can now close the two inequalities for phi
p. For the construction bound, start from any matching, realize the paired cost on each
selected pair and the singleton cost on each unmatched label, and take the orthogonal
sum. The unrestricted minimum is at most the minimum matching cost.

For the reverse bound, take the global minimizer we have been studying. Its simultaneous
invariant blocks have one or two angle entries. Their principal-angle lists combine into
the original list, with multiplicity, and their costs add. Each block is optimal, so it
gives either a singleton, a pair, or two singletons. Each angle occurrence is used once.
These choices form a matching with the same total cost. Thus the minimum matching cost
is at most the unrestricted minimum. Together the inequalities prove equality for
exponents strictly between one and two.

## M26ZeroAngles: Common directions do not provide cheaper partners

Why: Could a direction already shared by K and L be used as a cheaper partner?
Recall: A zero principal angle is a common source--target direction.

The graph only includes positive angles, so we should make sure common directions do not
hide an extra opportunity to reduce the cost.

The theorem's graph uses only positive principal-angle labels. We should check that
zero-angle directions cannot improve a positive label's cost by serving as extra
partners. A zero-angle singleton costs zero. If we pair an angle theta with zero, both h
and d equal half theta, so the scalar interval has only one point.

The paired power cost is then twice f p of theta, at least the best singleton cost for
theta. Remove such a pairing and keep the zero-angle direction fixed. This cannot
increase the cost. If it strictly lowered the cost of the matching extracted from our
minimizer, the construction direction would produce a cheaper feasible transporter,
contradicting global minimality. Thus we can use exactly the original positive labels.
Common directions do not add a hidden optimization opportunity.

## M27UniformLimit: Pass minimum values to the trace norm

Why: We solved a smooth cost: how do we get back to the promised trace norm?
Recall: Uniform convergence bounds the error for every feasible $W$ at once.

The smooth problem has become matching. Our original objective was the trace norm, so
one final analytic bridge remains. The key idea is to pass minimum values through the
limit; the minimizing matrices do not have to converge.

Every displacement singular value of an orthogonal matrix lies between zero and two. On
this fixed compact interval, the p-th power converges uniformly to the identity function
as p approaches one from above. With n singular values, the error between phi p and the
trace cost is bounded by n times the maximum scalar error, uniformly over all feasible
W.

If two functions differ by at most epsilon everywhere on the same set, their minimum
values differ by at most epsilon. Evaluate each function at a minimizer of the other to
obtain the two inequalities. The same argument applies to each compact scalar pair
minimum. Finally, there are only finitely many matchings, so convergence of their costs
gives convergence of the minimum matching cost. We have moved minimum values through the
limit without assuming convergence of the minimizing matrices.

## M28EndpointWeights: Evaluate the paired weight at exponent one

Why: Why does the trace-norm pair formula simplify so much?
Recall: $h=(\theta_i+\theta_j)/2$; the best endpoint choice is $\tau=h$.

We have justified passing minimum values to exponent one. Now evaluate the local weights
at that exponent.

At exponent one, the singleton formula becomes the smaller of four sine of half theta
and two. For the pair, the sum-to-product identity rewrites the scalar cost as eight
times sine of half h times cosine of half tau.

As tau increases from d to h, this expression is nonincreasing. Its minimum is therefore
at tau equal to h and equals four sine of h. Since h is half the sum of the two
principal angles, this is exactly the paired trace weight stated in the theorem. The
attaining map has rotational phases two h and zero. It rotates one real plane through
the sum of the two angles and fixes another. Combined with uniform convergence, this
gives the trace-norm matching formula. Compactness also supplies an actual minimizing
orthogonal transporter at the endpoint.

## M29MatchingAlgorithm: Recover a maximum-weight matching problem

Why: What can we now compute, and how does it give a real transporter?
Recall: Maximum total savings means minimum displacement; the empty matching is allowed.

We have returned to the promised trace-norm problem. The geometric and analytic work now
justify the finite graph calculation we saw near the beginning.

Now the geometry and analysis have produced a finite optimization problem. Start with
the all-singleton cost C zero. For each pair of labels, assign edge weight equal to the
two singleton costs minus their paired cost. A matching's total displacement cost is C
zero minus the sum of its selected edge weights.

Minimizing that cost means maximizing total edge weight on a general graph. This is not
maximum-cardinality matching, and an empty matching is allowed. After choosing a
maximum-weight matching, recover an actual transporter using the paired and singleton
constructions. This is an exact reduction of the minimum value, with solution recovery.
It does not identify every orthogonal transporter with a unique matching.

## M30WorkedExample: Build the minimizing map in six dimensions

Why: What does the entire argument deliver for three concrete angles?
Recall: Angles: $30^\circ,45^\circ,75^\circ$; labels $1,2,3$ respectively.

Use the theorem once from start to finish, so the small pieces, the graph, and the
actual transporter meet in a concrete calculation.

Return to principal angles thirty, forty-five, and seventy-five degrees. There are four
matchings: no pair, pair one-two, pair one-three, or pair two-three. Their costs are
approximately four point five six six zero, four point four three five zero, four point
seven zero four one, and four point four nine nine four.

The best choice pairs thirty and forty-five. Their four-dimensional block rotates a
moving plane by seventy-five degrees and fixes another plane. The remaining seventy-five
degree principal plane uses a reflection of cost two. The total is four sine of
thirty-seven point five degrees plus two, approximately four point four three five zero.
The theorem's lower bound establishes that unrestricted six-dimensional mixing cannot
improve this construction. The two sides of the proof meet in this concrete example.

## M31Rehearsal: Retell the argument as a sequence of reasons

Why: Can we explain why every new object was introduced?
Recall: Legal wiggles reveal structure; common small blocks turn structure into matching.

An optimal orthogonal transporter attains a finite matching value. Stationarity derives the small blocks rather than assuming them. Local block bounds and attaining constructions prove opposite inequalities. Here is how the preceding argument fits those conclusions. Try rebuilding the story without the formulas. Why do independent pieces help us? Why
can we actually construct changes that keep the image subspace fixed? What does P keep,
and why does our constructed B commute with it? What does G record, and how do legal
tests force its within-source response to vanish?

Then explain the geometric heart: why squaring G gives common invariant pieces, why two
phase values alone do not bound their dimension, and why following Y from u to v and
back makes a coordinate plane close. Translate one or two complex coordinates back to
real dimensions and source rank. Finally, explain why the pieces must be locally
optimal, how they produce a matching, and why uniform convergence returns us to the
trace norm. Each object was introduced to solve one of these specific problems.

## MatchingComputation: Bonus: implementing the matching reduction

Why: Separate a numerical graph solver from the proof of the reduction.
Recall: $a_i$: singleton cost; $b_{ij}$: pair cost; $g_{ij}=a_i+a_j-b_{ij}$.

As an optional numerical bonus, turn the exact reduction into code. On this card, a sub i denotes a singleton cost, and b sub i j denotes the paired cost. The edge saving g sub i j is the sum of the two singleton costs minus the pair cost. Build one vertex per angle label and weight each edge by its pair savings. A general-graph maximum-weight matching algorithm selects disjoint pairs; a bipartite assignment solver would impose an extra restriction. NetworkX exposes a blossom-based implementation. Keep maxcardinality false, because we maximize savings rather than the number of paired labels. Recover the actual orthogonal transporter from the selected local blocks, then verify its constraint and displacement cost. Floating-point weights can select a slightly suboptimal matching near a tie, so precision is part of the numerical implementation, separate from the exact reduction proved in the lecture.
