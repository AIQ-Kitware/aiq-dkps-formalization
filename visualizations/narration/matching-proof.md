# Theorem 5: presentation text for the matching proof

Each numbered section is the spoken text for one Manim scene. Section identifiers
match the deck manifest and appear in exported text filenames. The paragraphs
use words for equations so they can be sent directly to a text-to-speech model.
The visual slide contains the inference and a shorter justification.

## M00Problem: The optimization problem

We have two subspaces, K and L, of the same dimension inside a finite-dimensional
real Euclidean space. We want an orthogonal transformation W that carries K
onto L. We are not prescribing where each individual source vector must go.
The constraint concerns the whole subspace.

Among all these transformations, we minimize the trace norm of identity minus W.
This is the sum of all displacement singular values, measured on the entire
ambient space. Theorem five says that we can obtain this minimum by solving a
finite maximum-weight matching problem. Our task is to understand why a search
over arbitrary orthogonal matrices can reduce to choosing pairs of angle labels.

## M01PrincipalPlanes: Geometry gives principal planes

Choose orthonormal bases for the source and target subspaces. The singular value
decomposition of their overlap matrix gives the principal angles and corresponding
principal vectors. Each positive angle has a source direction and a target
direction lying in a two-dimensional principal plane. Principal planes belonging
to different angle labels are orthogonal.

In the picture, each little plane shows one source line in amber and its target
line in blue. The panels represent mutually orthogonal coordinate planes, rather
than planes physically lying on the screen. Common zero-angle directions can be
fixed. This describes the two subspaces. It does not say that an optimal W must
preserve the individual principal planes. That is the distinction we will need
to keep in mind when proving the lower bound.

## M02Singleton: Transport one principal plane

Start with one principal angle, theta. A planar rotation through theta carries
the source line onto its target. Its displacement has two equal singular values,
each equal to two times sine of half theta. Adding them gives a trace cost of
four times sine of half theta.

There is another choice. A reflection across an angle-bisecting line also
carries the source line onto the target. Its eigenvalues are positive one and
negative one, so its displacement singular values are zero and two. Its trace
cost is therefore two. The best singleton cost is the smaller of the rotation
cost and two. The source and target are unoriented lines, which is why reflection
is an admissible competitor.

## M03PairedBlock: Let two principal planes interact

We can also group two principal planes into a four-dimensional block. Inside
that block, we allow an orthogonal transporter to mix the two source directions
and their complementary directions. This is more freedom than transporting
each principal plane independently.

At the trace-norm endpoint, there is a paired construction whose cost is four
times sine of half the sum of the two principal angles. In a suitable invariant
basis, it rotates one real plane through the sum of the angles and fixes another
real plane. These moving and fixed planes are generally different from the two
original principal planes. The diagram shows the dimensions and grouping; it is
not a literal drawing of four-dimensional geometry. We will justify both the
construction and the comparison with other transporters later.

## M04Graph: Encode pair choices in a general graph

Now put one vertex at each positive principal-angle label. Every edge is a
possible pair. A matching chooses edges so that each label is used at most once.
For example, pairing labels one and two leaves label three unmatched. Taking
both edge one-two and edge two-three is disallowed because label two would
belong to two blocks.

Each vertex has its singleton cost. The weight of an edge is the cost of its
two singletons minus their paired cost. Starting from all singletons, selecting
an edge subtracts that weight. Therefore we maximize total edge weight.
The empty matching is allowed, and negative edges need not be selected. In our
thirty, forty-five, and seventy-five degree example, the best edge pairs thirty
and forty-five. The seventy-five degree label uses its singleton reflection.

## M05TwoBounds: Separate the two inequalities

Every matching gives us a recipe for a transporter: use a four-dimensional block
for each edge, a two-dimensional block for each unmatched label, and take their
orthogonal sum. Displacement costs add across orthogonal blocks. This proves
that the unrestricted minimum is no greater than the best matching cost.

The reverse inequality is the difficult one. An arbitrary orthogonal transporter
might mix three or more principal planes. Merely drawing principal planes does
not exclude that possibility. We need to show that such unrestricted mixing
cannot achieve a lower minimum. We will choose a global minimizer of a smoother
cost, derive necessary equations from feasible variations, and use those
equations to obtain small invariant blocks. Keep these two inequality directions
separate throughout the proof.

## M06SmoothCost: Use a differentiable cost first

The trace norm is a sum of singular values. At zero singular values it need not
be differentiable. This makes a direct first-derivative argument difficult.
Instead, choose an exponent p strictly between one and two and sum the p-th
powers of the displacement singular values. Call this cost phi p.

The graph shows why the exponent helps: absolute t has a corner at zero,
whereas absolute t to a power greater than one has derivative zero there.
The corresponding finite-dimensional matrix cost is differentiable too,
including at zero displacement singular values. The study note derives this
using a symmetric matrix dilation. We will prove the matching equality for
these smooth costs, then let p approach one from above. We pass minimum values
to that limit; we do not assume one transporter minimizes every exponent.

## M07Existence: Choose an actual global minimizer

Before using optimality, we must know there is a minimizing matrix. The feasible
set is nonempty: map an orthonormal basis of K onto one of L and extend the map
to their orthogonal complements. It is compact: the orthogonal group is closed
and bounded, and the transport condition is a closed constraint.

The condition can be written as W times P times W transpose equals Q, where
capital P and capital Q are the source and target projections. The cost is
continuous, so it attains a global minimum on this nonempty compact set. Choose
one minimizing W for our fixed exponent p. We have not assumed that W has any
particular block structure. All the structure we use next must follow from
optimality and matrix identities.

## M08FeasibleCurves: Vary the map without changing its destination

Let B be a real skew-symmetric matrix. Its exponential at time t is orthogonal,
because its transpose is the exponential at negative time, which is its inverse.
Thus W times the exponential of t B is still orthogonal.

To retain the transport condition, require B to commute with the source
projection P. Every power of B then commutes with P, so its exponential does
too. Both the exponential and its inverse preserve K. The exponential therefore
maps K onto itself, and composing with W still maps K onto L.

The block diagram separates variations within the source and within its
orthogonal complement. These are source-adapted blocks, not W's rotation planes.
Along every such feasible curve, the scalar cost has a minimum at zero. Its
derivative at zero must vanish. This is the necessary condition called stationarity.

## M09RotationCost: Read displacement from a rotation chord

To calculate the derivative, first understand the cost of a rotation plane of W.
A vector and its image under rotation by angle t lie on the same unit circle.
The displacement is the chord between them. Its length is two times sine of
half t. Every unit vector in that plane has the same displacement length.

Algebraically, identity minus the rotation, transpose times itself, is four
times sine squared of half t times identity. There are therefore two equal
displacement singular values. Define the scalar phase cost f p of t as the
p-th power of this chord length. The full real plane contributes twice f p of t.
The factor two comes from the two real dimensions. We must retain it when
computing the first variation.

## M10SignAverage: Why mixing directions do not add a derivative term

Write W in its own orthogonal basis of rotation planes and scalar positive-one
and negative-one lines. The direction B need not preserve those blocks. To
handle the off-diagonal parts of B, use differentiability: the first variation
is a linear functional of B.

Independently multiply each W block by positive or negative identity. These
sign changes commute with W. Conjugating the curve by them preserves every
displacement singular value, so it preserves the derivative. Average over all
sign choices. Each off-diagonal block of B appears equally often with either
sign and cancels. The diagonal blocks remain unchanged. By linearity, this
average has the same derivative as B. These auxiliary directions need not
preserve K: we are calculating the derivative before restricting it to feasible
directions. For many blocks, repeat the same sign cancellation independently.

## M11TracePairing: Identify the gradient and check its sign

On a rotation plane of angle theta, every diagonal skew-symmetric direction
has the form b times the planar quarter-turn J. This varies the rotation angle
at speed b. Since the plane costs twice f p of theta, its derivative is twice
b times f p prime of theta.

Define G on that plane to be f p prime of theta times J. Because J squared is
negative identity in dimension two, minus the trace of G times b J is precisely
twice b times f p prime of theta. On scalar lines G is zero, and the diagonal
skew direction is zero. Summing the block calculations gives the general
derivative: minus the trace of G B. The sign-averaging argument explains why
this formula remains valid when B mixes planes. It is a proved derivative
identity, rather than a definition we may assume arbitrarily.

## M12Stationarity: The gradient has zero diagonal source blocks

We now return to directions that preserve the source. Choose B equal to P G P.
It is skew-symmetric and commutes with P, so its exponential gives a feasible
curve. Stationarity sets minus the trace of G B to zero. Using cyclicity of
trace and P squared equals P, this is minus the trace of B squared.

For a real skew-symmetric B, minus the trace of B squared is the squared
Frobenius norm of B: the sum of the squares of all its entries. That can vanish
only when B is zero. Thus P G P is zero. Repeating with the complementary
projection makes the other diagonal block zero. In source and source-complement
coordinates, G only couples the two spaces. The source reflection J, equal to
two P minus identity, consequently reverses G under conjugation: J G J equals
negative G.

## M13TwoDecompositions: Keep the two bases separate

There are two decompositions in this part of the proof. The first is W's
rotation-plane decomposition. It lets us define G and calculate the derivative.
The second is the source and source-complement decomposition. It identifies
which variations preserve the transport constraint and where G's diagonal
blocks must vanish.

These are generally different bases. We have not proved that a source-adapted
basis diagonalizes W, or that W's rotation planes preserve the source. What we
do have are two coordinate-independent equations: G commutes with W, and the
source reflection J reverses G. The next step combines those equations to find
a new decomposition preserved by W, the source projection, and the target
projection simultaneously.

## M14GradientLevels: Square the gradient to get invariant spaces

G is skew-symmetric, so negative G squared is symmetric and nonnegative. Its
quadratic form at x is the squared length of G x. We can therefore decompose
the real space into its eigenspaces.

Since G commutes with W, its square does too. Although J reverses G, it
commutes with G squared: the two minus signs cancel. Each eigenspace of
negative G squared is consequently preserved by G, W, and J. Since the source
projection is one half of identity plus J, it also preserves each level.
The target projection, W P W transpose, does too. This is a simultaneous
decomposition of the actual minimizer and both subspaces. Its blocks may still
be large. We treat the positive eigenvalues first and reserve the zero
eigenspace for a separate argument.

## M15ComplexCoordinates: A quarter-turn supplies complex multiplication

On a positive level, negative G squared is g squared times identity for a
positive number g. Divide G by g and call the result I sub g. Its square is
negative identity, and it preserves lengths. This is exactly how multiplication
by the imaginary unit acts on a real plane.

Define complex scalar multiplication by saying that a plus i b times x is
a x plus b I sub g x. A real plane spanned by x and I sub g x becomes one
complex line. We are using new coordinates on the original real space.
Because W commutes with I sub g, it is complex-linear and unitary in these
coordinates. The source reflection J reverses I sub g, so it acts as complex
conjugation. In particular, its fixed space has half the original real
dimension. These facts will let us preserve the source when splitting the level.

## M16TwoPhases: A positive gradient level has at most two phases

On our chosen level, an eigenphase t of W must satisfy f p prime of t equals g.
Look at the derivative graph for p equal to three halves. It rises from zero,
reaches one maximum, and falls back to zero. A positive horizontal level can
therefore meet it at no more than two points.

The same calculation works throughout our auxiliary exponent range. The second
derivative changes sign once, where tangent squared of half t equals p minus
one. Thus the complex unitary W has at most two eigenphases on this level.
Write it as one scalar phase times a projection E, plus the other scalar phase
times identity minus E. Multiplicity can still be arbitrarily large. Two phase
values alone do not imply that this level is only four-dimensional. We need
one more decomposition, involving E and the conjugation J together.

## M17ProjectionBlocks: Split the phase projection using real and imaginary parts

Choose complex coordinates in which J is ordinary conjugation. Write the
orthogonal projection E as X plus i Y, with real matrices X and Y. The
projection equations imply that X is symmetric, Y is skew-symmetric,
X squared minus Y squared equals X, and X Y plus Y X equals Y.

Choose a unit eigenvector u of X with eigenvalue lambda. The equations show
that Y u lies in the eigenvalue one minus lambda space, and that Y squared u
is negative lambda times one minus lambda times u. If lambda is strictly
between zero and one, normalize Y u to obtain an orthogonal unit vector v.
The span of u and v is preserved by X and Y. This also works at lambda equal
to one half. At endpoints zero and one, Y u vanishes and a line suffices.
The orthogonal complement remains invariant, so we can repeat until all
coordinate directions have been used.

## M18RealBlocks: Count the dimensions and angle entries

The lines and planes just constructed were in the real coordinate space of
our complex representation. Take their complex spans. A coordinate line gives
one complex dimension, which is two dimensions in the original real space.
A coordinate plane gives two complex dimensions, which is four real dimensions.

These blocks preserve E and conjugation J, hence W and the source projection.
They also preserve the target projection. The fixed space of J is the source
part and has half the real dimension. A two-dimensional block therefore has
source rank one and contributes one principal-angle entry. A four-dimensional
block has source rank two and contributes two entries. This is the step that
makes singletons and pairs exhaustive for the positive-gradient part of a
smooth global minimizer. It follows from the projection calculation, not
merely from counting phase values.

## M19ZeroGradient: Handle the level where division by g is impossible

On the kernel of G we cannot divide by a positive gradient level. The scalar
phase derivative vanishes only at phases zero and pi. W therefore has only
eigenvalues positive one and negative one there. It is a reflection, equal to
identity minus twice the projection onto its negative-one eigenspace.

Apply the two-projection decomposition to that negative eigenspace projection
and the source projection. This gives common invariant real lines and planes.
The nontrivial planes carry one source direction. On an invariant line, source
and target are either both the whole line or both absent. A negative-one action
on that line can be replaced by positive one without changing transport.
The cost drops from two to the power p to zero. A global minimizer cannot
contain that avoidable displacement. This leaves fixed directions and
one-angle planes on the zero-gradient part.

## M20PairCoordinates: Parametrize every four-dimensional competitor

We now know why the minimizer has small blocks. Next we calculate their actual
minimum costs. Singletons have the rotation-or-reflection formula. For two
angles, choose coordinates with the two source directions first and their
two complementary directions second.

The direct rotation D has cosine and sine diagonal blocks built from the two
principal angles. Every other transporter on this four-dimensional space is
D times a block diagonal matrix with two planar orthogonal factors, U zero
and U one. To see this, multiply a transporter by D transpose. The result
preserves the source, so it also preserves its orthogonal complement.
The free factors can mix the two source directions. We have therefore
parametrized all competitors on the block, rather than assuming separate
transport of the original principal planes.

## M20PhaseParameters: Introduce the two phase parameters

Order the principal angles with theta i at least theta j. Let h be their
half-sum and d their half-difference. In the determinant-positive case,
the two free factors are either both rotations or both reflections.

For rotations, write their angles as r plus s and r minus s. Any two angles
can be written this way by taking their half-sum and half-difference. Define
x and y between zero and pi by cosine x equals cosine h times cosine s,
and cosine y equals cosine d times cosine r.

For reflections, append the planar coordinate reflection to each rotation.
The corresponding formulas are cosine x equals negative sine d times cosine r,
and cosine y equals sine h times cosine s. So far these are auxiliary
parameters defined by the free factors. The next slide checks that x plus y
and x minus y actually describe W's eigenphases.

## M20PhasePolynomial: Check the eigenphases with the characteristic polynomial

Write u for cosine x and v for cosine y. Multiplying the blocks of W gives
trace W equal to four u v. The same calculation gives the displayed trace of
W squared. The coefficient of z squared in the characteristic polynomial is
one half of the difference between the square of the trace and the trace
of the matrix square. Keeping these two operations distinct is essential.

Orthogonality and determinant one make the degree-four polynomial reciprocal:
its coefficients read the same forwards and backwards. The trace fixes both
the cubic and linear coefficients, and the constant is one. These facts give
the polynomial on the slide. Multiply the two quadratic factors associated
with x plus y and x minus y; the result is that same polynomial. Its roots
are therefore the four claimed phase eigenvalues. The study note spells out
the block trace multiplication if you want to reproduce that part by hand.

## M20RectangleBounds: Put both cases in the same rectangle

In the rotation case, the absolute value of cosine x is at most cosine h.
Because cosine decreases on the interval from zero to pi, x lies between h
and pi minus h. The same argument puts y between d and pi minus d.
This is the large rectangle in the diagram.

For two reflections, the cosine formulas instead put x between pi over two
minus d and pi over two plus d. They put y between pi over two minus h and
pi over two plus h. These give the smaller rectangle. It lies inside the
larger one because h plus d equals the larger principal angle, which is at
most pi over two. We now have one common region covering every
positive-determinant competitor. We do not need to claim every point of the
large rectangle comes from the reflection case.

## M21PhaseRectangle: Reduce two phase parameters to an edge

Let h be half the sum of the two principal angles and d half their absolute
difference. In the positive-determinant class, the matrix calculation gives
phase parameters x and y in the rectangle shown. The eigenphases occur as
plus or minus x plus y, and plus or minus x minus y.

Fold the point if needed so that x plus y is at most pi. Set tau to the larger
of d and h minus the absolute difference of x and y. Then tau lies between d
and h. The new larger phase, h plus tau, is no greater than x plus y.
The new smaller phase, h minus tau, is no greater than the absolute difference
of x and y. The scalar phase cost is increasing between zero and pi. Moving
to the displayed edge point therefore cannot increase either phase cost.
The visual movement represents this comparison of phase values, rather than
a claim that the objective decreases along a particular path of matrices.

## M22PairMinimum: Attain the scalar minimum

The preceding comparison supplies a lower bound for every positive-determinant
transporter. To make it an equality, we must also attain every point of the
edge. Set both free planar factors equal to rotation through gamma, where
cosine of gamma equals cosine of tau divided by cosine of d. This ratio lies
between zero and one, and the denominator is positive.

The resulting transporter has phase parameters x equal to h and y equal to
tau. Its cost is twice f p of h plus tau plus twice f p of h minus tau.
We minimize this continuous scalar function over the closed interval from d
to h, so a minimum is attained. The curve is an illustration of that scalar
optimization for p equal to three halves. The rectangle comparison and this
explicit attainer establish both inequalities for the positive-determinant
block cost.

## M23Determinants: Include reflections and two singletons

A four-dimensional transporter can also have determinant negative one. Its
eigenvalues are positive one, negative one, and a conjugate rotational pair.
The free-factor parametrization bounds its absolute trace by twice cosine of
the smaller principal angle. Since the trace is twice cosine of its rotational
phase, that phase cannot be smaller than the smaller principal angle.

The least cost in this class is attained by reflecting on the larger-angle
plane and rotating on the smaller-angle plane. Compare this with the positive
pair minimum and the four independent rotation-or-reflection choices.
The full block minimum becomes the smaller of the paired cost and the sum
of the two singleton costs. That last comparison is essential: using one
four-dimensional block does not force us to choose a matching edge. It may
be better to leave both labels unmatched.

## M24BlockOptimality: Every block of a global minimizer is optimal

Suppose a simultaneous invariant block of our global minimizer did not have
the least cost for its own source and target pieces. Replace only that
restriction by a cheaper orthogonal transporter. All other blocks stay fixed.
The resulting ambient matrix is still orthogonal and still carries the source
onto the target.

Displacement costs add across these orthogonal blocks, so the replacement
strictly lowers the global cost. This contradicts our choice of a global
minimizer. Therefore each block attains its local minimum. Stationarity alone
would not justify this replacement argument. We now use the local cost
formulas to translate the block decomposition into singleton and paired
angle labels.

## M25MatchingEquality: Prove both bounds for the smooth cost

We can now close the two inequalities for phi p. For the construction bound,
start from any matching, realize the paired cost on each selected pair and
the singleton cost on each unmatched label, and take the orthogonal sum.
The unrestricted minimum is at most the minimum matching cost.

For the reverse bound, take the global minimizer we have been studying.
Its simultaneous invariant blocks have one or two angle entries. Their
principal-angle lists combine into the original list, with multiplicity,
and their costs add. Each block is optimal, so it gives either a singleton,
a pair, or two singletons. Each angle occurrence is used once. These choices
form a matching with the same total cost. Thus the minimum matching cost is
at most the unrestricted minimum. Together the inequalities prove equality
for exponents strictly between one and two.

## M26ZeroAngles: Common directions do not provide cheaper partners

The theorem's graph uses only positive principal-angle labels. We should check
that zero-angle directions cannot improve a positive label's cost by serving
as extra partners. A zero-angle singleton costs zero. If we pair an angle
theta with zero, both h and d equal half theta, so the scalar interval has
only one point.

The paired power cost is then twice f p of theta, at least the best singleton
cost for theta. Remove such a pairing and keep the zero-angle direction fixed.
This cannot increase the cost. If it strictly lowered the cost of the matching
extracted from our minimizer, the construction direction would produce a
cheaper feasible transporter, contradicting global minimality. Thus we can
use exactly the original positive labels. Common directions do not add a
hidden optimization opportunity.

## M27UniformLimit: Pass minimum values to the trace norm

Every displacement singular value of an orthogonal matrix lies between zero
and two. On this fixed compact interval, the p-th power converges uniformly
to the identity function as p approaches one from above. With n singular
values, the error between phi p and the trace cost is bounded by n times
the maximum scalar error, uniformly over all feasible W.

If two functions differ by at most epsilon everywhere on the same set, their
minimum values differ by at most epsilon. Evaluate each function at a minimizer
of the other to obtain the two inequalities. The same argument applies to
each compact scalar pair minimum. Finally, there are only finitely many
matchings, so convergence of their costs gives convergence of the minimum
matching cost. We have moved minimum values through the limit without assuming
convergence of the minimizing matrices.

## M28EndpointWeights: Evaluate the paired weight at exponent one

At exponent one, the singleton formula becomes the smaller of four sine of
half theta and two. For the pair, the sum-to-product identity rewrites the
scalar cost as eight times sine of half h times cosine of half tau.

As tau increases from d to h, this expression is nonincreasing. Its minimum
is therefore at tau equal to h and equals four sine of h. Since h is half
the sum of the two principal angles, this is exactly the paired trace weight
stated in the theorem. The attaining map has rotational phases two h and zero.
It rotates one real plane through the sum of the two angles and fixes another.
Combined with uniform convergence, this gives the trace-norm matching formula.
Compactness also supplies an actual minimizing orthogonal transporter at
the endpoint.

## M29MatchingAlgorithm: Recover a maximum-weight matching problem

Now the geometry and analysis have produced a finite optimization problem.
Start with the all-singleton cost C zero. For each pair of labels, assign
edge weight equal to the two singleton costs minus their paired cost.
A matching's total displacement cost is C zero minus the sum of its
selected edge weights.

Minimizing that cost means maximizing total edge weight on a general graph.
This is not maximum-cardinality matching, and an empty matching is allowed.
After choosing a maximum-weight matching, recover an actual transporter using
the paired and singleton constructions. This is an exact reduction of the
minimum value, with solution recovery. It does not identify every orthogonal
transporter with a unique matching.

## M30WorkedExample: Build the minimizing map in six dimensions

Return to principal angles thirty, forty-five, and seventy-five degrees.
There are four matchings: no pair, pair one-two, pair one-three, or pair
two-three. Their costs are approximately four point five six six zero,
four point four three five zero, four point seven zero four one, and
four point four nine nine four.

The best choice pairs thirty and forty-five. Their four-dimensional block
rotates a moving plane by seventy-five degrees and fixes another plane.
The remaining seventy-five degree principal plane uses a reflection of cost
two. The total is four sine of thirty-seven point five degrees plus two,
approximately four point four three five zero. The theorem's lower bound
establishes that unrestricted six-dimensional mixing cannot improve this
construction. The two sides of the proof meet in this concrete example.

## M31Rehearsal: Explain the proof without the slides

Pause and reconstruct the argument. First, why does a matching give an upper
bound rather than a lower bound on the unrestricted minimum? Second, why does
the derivative formula hold when the skew direction mixes W's rotation planes?
Third, why do the two gradient equations lead to blocks of dimension two or
four, rather than merely to two phase values of high multiplicity?

Then explain why every block must itself minimize cost, why the four-dimensional
comparison includes two independent singletons, and why uniform convergence
allows us to return to the trace norm. The proof has three parts: construct
transports from angle pairs; show a smooth global minimizer can be decomposed
into the required blocks; and pass minimum values to exponent one. The
accompanying study note gives the longer calculations, including the
differentiability argument and the characteristic polynomial for a pair.
