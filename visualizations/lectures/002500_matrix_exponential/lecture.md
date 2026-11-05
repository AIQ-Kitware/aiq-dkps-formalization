# The exponential of a matrix

Authored transcript for `prereq-matrix-exponential`. Basic matrix multiplication,
power series, and one-variable derivatives are assumed; differential equations
are introduced locally. Historical context: Cayley,
[A Memoir on the Theory of Matrices (1858)](https://doi.org/10.1098/rstl.1858.0002),
and Higham, [The Scaling and Squaring Method for the Matrix Exponential Revisited (2005)](https://doi.org/10.1137/04061101X).
These are context for matrix algebra and numerical computation, not claims
about who first defined the matrix exponential.

Computational references: [Al-Mohy and Higham (2009)](https://doi.org/10.1137/09074721X), [Al-Mohy and Higham (2011)](https://doi.org/10.1137/100788860), [SciPy expm](https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.expm.html), and [SciPy expm_multiply](https://docs.scipy.org/doc/scipy/reference/generated/scipy.sparse.linalg.expm_multiply.html).

## ExTitle: The exponential of a matrix

Why: From a velocity rule to an exact motion.
Recall: No notation is needed on the title slide.

The exponential of a matrix.

## ExSetup: The matrix, the flow, and one trajectory

Why: Separate three objects that are easy to conflate.
Recall: $A$: fixed matrix; $t$: scalar; $x_0$: initial vector.

A is a fixed real square matrix and t is an ordinary real number. A squared means matrix multiplication, and A to the zero is the identity. Exponential t A is another matrix, defined by a power series in those matrix powers. Once that matrix is applied to one initial vector x zero, it gives a particular trajectory x of t. The matrix flow and the trajectory are different objects. We will connect them to differentiation without assuming you have seen that connection elsewhere. When a generator B has transpose equal to minus B, we call it skew-symmetric; later we will prove that its exponential preserves lengths.

## Ex00Question: One matrix function, two ways to understand it

Why: Read scalar and vector trajectories at one shared time.
Recall: Amber is u or x_1; blue is x_2; violet marks the same t on both graphs.

First, a purely mathematical viewpoint. The power series defines a matrix for each value of t. Together these matrices form a family of linear maps. No starting vector is needed to define that family. Once we choose a starting vector, applying the map gives a trajectory. The graphs show these outputs, rather than the entries of the exponential matrix itself.

<!-- beat -->

Now let the same time advance on both graphs. On the left, the amber point follows scalar exponential growth, starting at one. On the right, the two by two matrix mixes the two coordinates. The amber point is the first coordinate and the blue point is the second. They start at one and zero, and follow cosine and sine. We will keep amber for the first coordinate and blue for the second when we draw these motions in the plane later. Each violet line marks the same time; its colored dots give the values at that time. The equations below give the velocity interpretation. The formula above gives the power-series interpretation. These are two descriptions of the same exponential, which we will now construct and study.

## Ex01History: Matrix algebra made functions of a matrix meaningful

Why: Matrix powers extend scalar formulas, but multiplication order matters.
Recall: Cayley emphasized matrix multiplication, powers, and its failure to commute.

Cayley's 1858 memoir develops an algebra of matrices, including powers and
the importance of multiplication order. This is the algebraic setting in
which we can interpret a power series at a matrix argument. There is also
a substantial computational story: Higham's 2005 work revisited scaling and
squaring for evaluating the matrix exponential accurately. Our lecture
focuses on meaning and exact identities, with small numerical illustrations.
The direct Taylor sums and small-step paths we draw are teaching devices;
the definition of a function and a good algorithm for computing it are
different questions.

## Ex02Series: Replace scalar powers by matrix powers

Why: The same convergent series defines the exponential for every finite square matrix.
Recall: $\exp(tA)=I+tA+t^2A^2/2!+\cdots$; $A^0=I$.

Start from the scalar exponential series and use matrix multiplication for
each power. The constant term is the identity matrix, not a matrix of ones.
Every term is a matrix of the same size, so their partial sums make sense.
We are not exponentiating individual entries. In particular, the exponential
of the zero matrix is identity, while applying the scalar exponential to
each zero entry would produce ones everywhere.

<!-- beat -->

Why does this infinite sum converge? For a submultiplicative operator norm,
the norm of each term is bounded by absolute t times the norm of A, raised
to the term's power, divided by its factorial. Those scalar bounds sum to
an ordinary finite exponential. Thus the matrix series converges absolutely
for every finite square matrix and every real time, including when A has
no inverse or cannot be diagonalized.

## Ex03SmallSteps: Many tiny updates approach the exact flow

Why: The exponential accumulates repeated local changes.
Recall: $\exp(tA)=\lim_{n\to\infty}(I+(t/n)A)^n$.

A second viewpoint starts with a small time step. If the present vector is
x, its first-order update is x plus the step length times A x. Apply this
update repeatedly. After n equal steps the resulting map is identity plus
t A divided by n, raised to the n-th power. As n increases, this converges
to the matrix exponential.

<!-- beat -->

For the planar quarter-turn generator, four coarse steps drift outward from
the unit circle. Thirty-two smaller steps stay much closer to it. The exact
exponential follows the circular arc. The finite polygon is an approximation,
not an exactly orthogonal motion. This explains why identity plus t A is
useful as a local approximation but cannot replace the exponential when a
proof requires the constraint to hold at every time.

## Ex04Dynamics: Differentiating the series recovers the velocity rule

Why: The exponential is characterized by the linear motion it generates.
Recall: $X(t)=\exp(tA)$ satisfies $X\prime(t)=AX(t)$ and $X(0)=I$.

Differentiate the series term by term. The constant identity disappears,
and each positive power contributes one lower factorial. Factoring A from
the resulting series gives A times the exponential. We can also factor A
on the other side because every power of A commutes with A. These
differentiations are justified by convergence of the series and its
derivative uniformly on bounded time intervals.

<!-- beat -->

Now multiply by an initial vector x zero. The vector x of t equal to
exponential t A times x zero has derivative A x of t, and its initial value
is x zero. This is the unique solution of that constant linear initial-value
problem. In particular, its initial velocity is A x zero. The exponential
turns a prescribed instantaneous linear rule into a complete motion.

## Ex05Diagonal: Diagonal generators produce independent growth and decay

Why: The scalar exponential survives along directions that do not mix.
Recall: For $A=\operatorname{diag}(a,b)$, $\exp(tA)=\operatorname{diag}(e^{ta},e^{tb})$.

If A is diagonal, its powers are diagonal, and each diagonal entry follows
the scalar exponential series. In this example the horizontal coordinate
grows while the vertical coordinate decays. The image of a unit circle
becomes an ellipse. This motion is invertible, but it is not orthogonal:
lengths need not stay constant.

<!-- beat -->

More generally, if A can be diagonalized, we can compute its exponential in
that eigenbasis and then change back. But diagonalization is a useful
special case, not a requirement for the definition. The next example has
a nonzero generator whose square is zero, and it can be understood directly
without an eigenbasis.

## Ex06Shear: A nonzero generator can have a terminating series

Why: Powers reveal structure even when diagonalization is unavailable.
Recall: $N=\left(\begin{smallmatrix}0&1\\0&0\end{smallmatrix}\right)$ satisfies $N^2=0$.

For this generator N, multiplying it by itself gives zero. All higher powers
therefore vanish. The exponential series stops after identity plus t N.
It sends a vector with coordinates x and y to x plus t y and y.
Points on the horizontal axis stay fixed, while points above that axis
slide horizontally. This is a shear.

<!-- beat -->

Notice that the linear-looking formula is exact here because N squared
vanishes. That does not make identity plus t A exact for arbitrary A.
N itself is singular, whereas its exponential is invertible, with inverse
identity minus t N. Exponentiating does not mean inverting the original
matrix. It builds a new map from the full power series.

## Ex07Rotation: A quarter-turn generator gives sines and cosines

Why: This is the concrete exponential used by the feasible-variation pictures.
Recall: $J=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ and $J^2=-I$.

For the planar quarter-turn J, the powers repeat: identity, J, minus
identity, minus J, and then identity again. Group the even powers of the
exponential series. They give cosine t times identity. The odd powers
give sine t times J. The resulting matrix is exactly the usual planar
rotation matrix.

<!-- beat -->

Watch the vector follow the circle. Its velocity is J times its current
position, which is perpendicular to the position. The generator specifies
turning, while the exponential performs the finite turn. Replacing J by
b times J changes the angular speed to b. This gives the formula used
in the variations lecture, including negative times and negative speeds.

## Ex08Laws: The same generator composes by adding times

Why: Time composition supplies the inverse and transpose identities.
Recall: $e^{sA}e^{tA}=e^{(s+t)A}$ for one fixed generator $A$.

Run the same constant linear motion for time t, then for time s.
The result is running it for time s plus t. Algebraically, multiply the
two absolutely convergent series and group equal total powers. The
binomial formula gives the exponential at the sum of the times. All
the powers involved are powers of the same matrix, so multiplication
order causes no difficulty.

<!-- beat -->

Set s equal to minus t. Since the exponential at zero is identity, the
exponential of minus t A is the inverse of the exponential of t A.
Also, transposing each term of the series gives the exponential of
t A transpose. These identities apply to every finite real square
matrix. They are the two ingredients that will turn skew-symmetry into
orthogonality.

## Ex09Noncommuting: Different generators need not obey the scalar addition rule

Why: Matrix multiplication order cannot be ignored when combining motions.
Recall: $AB=BA$ is sufficient for $e^{A+B}=e^Ae^B$; arbitrary matrices can fail it.

It is tempting to replace the same-generator rule by exponential of
A plus B equals exponential A times exponential B for arbitrary matrices.
That is not valid in general. If A and B commute, the series regrouping
works. Without commutation it may fail, because mixed words such as A B
and B A no longer coincide.

<!-- beat -->

Take the two displayed shear generators. Their exponentials are simple
triangular matrices, whose product has diagonal entries two and one.
But A plus B has exponential with equal diagonal entries, obtained by summing
the even powers, both about one point five four three. The matrices are
different. Commutativity is a sufficient hypothesis for factorization;
we have not claimed it is necessary for every accidental equality.

## Ex10Orthogonal: Skew-symmetry makes the exact flow orthogonal

Why: The exponential solves the orthogonality constraint for all times.
Recall: Let $B^T=-B$ and $V(t)=e^{tB}$.

Now take a skew-symmetric generator B. By the transpose identity,
V transpose is the exponential of t B transpose. Skew-symmetry makes
that the exponential of minus t B. By the inverse identity, it is
V inverse. Therefore V transpose V is identity at every real time.
This proves orthogonality in any finite dimension, not just for the
two-by-two rotation example.

<!-- beat -->

We have constructed an exact curve through identity with initial velocity
B. There is a useful boundary to remember: it stays in the determinant
plus-one component, since the curve starts at identity and the determinant
of an orthogonal matrix is either plus or minus one. We use it for local
variations. This does not restrict the original transporter W to have
positive determinant; multiplying W by this curve stays in whichever
component W already occupies.

## Ex11SourcePreservation: Commutation survives every term of the exponential

Why: A source-preserving velocity produces a source-preserving motion.
Recall: $BP=PB$ implies $e^{tB}P=Pe^{tB}$.

Suppose B commutes with the source projection P. Then B squared commutes
with P, and induction gives the same fact for every power. Every partial
sum of the exponential commutes with P. Passing to the limit preserves
the equality. Consequently the exponential preserves both the source
space and its orthogonal complement.

<!-- beat -->

Its inverse, the exponential of minus t B, has the same property, so the
source is mapped onto itself. If W already carries the source K onto
the target L, then W exponential t B still does so. We have arrived at
the exact feasible curve in the variations proof. Skew-symmetry preserves
lengths; commutation preserves the source. Each hypothesis has a separate job.

## Ex12Recap: A generator specifies velocity; its exponential supplies the motion

Why: These identities let us differentiate without leaving the feasible set.
Recall: Series, constant linear flow, inverse, skew-symmetry, and commutation.

The exponential is a matrix power series, not entrywise exponentiation.
It solves the constant linear equation x prime equals A x. Diagonal
generators stretch, the nilpotent example shears, and a quarter-turn
generator rotates. Inverses come from negative time. Skew-symmetry makes
the flow orthogonal, and commutation with P keeps the source decomposition
fixed. Those are the facts the variations proof needs.

<!-- beat -->

Check two cases. What is the exponential of the zero two-by-two matrix?
It is identity, not a matrix of ones. Can an exponential of a real
skew-symmetric matrix be a reflection? No: this curve remains in the
determinant plus-one component. That is compatible with testing a
negative-determinant transporter: multiply the transporter by the
exponential curve. With these distinctions in place, return to feasible
variations and follow how an exact motion produces a derivative test.

## ExFacts: Three exponential facts to use in a proof

Why: Assemble exact motions with known algebraic properties.
Recall: A and B are bounded operators on a real Hilbert space; star means adjoint.

These are the three reusable rules behind our motion construction. Exponentials of the same generator compose by adding their times. A skew-adjoint generator exponentiates to an orthogonal map. Finally, an operator that commutes with a projection continues to commute with it after exponentiation. For our feasible curve, apply the last two rules to t times B. Skew-adjointness preserves lengths, and commutation preserves the source decomposition. In finite orthonormal coordinates, the adjoint is just the transpose. The identities on this slide do not require finite dimension, but they do require bounded generators; we are not asserting a theorem about general unbounded operators here.

## ExLean: Composition of the flow in Lean

Why: Connect addition of times to composition of maps.
Recall: $e^{(s+t)A}=e^{sA}e^{tA}$.

The common assumptions specify a complete real inner product space. The copyable companion supplies a local rational-algebra instance for the exponential API; it adds no mathematical restriction on the space. The statement fixes one generator A and composes its flows at times s and t. Dot comp is composition of bounded linear maps. The green proof line applies the accepted Tau Ceti flow theorem. The same generator matters; two arbitrary noncommuting matrices do not satisfy this rule.

## ExLeanLengths: Length preservation in Lean

Why: Recognize the exact hypothesis behind an orthogonal exponential.
Recall: $B^*=-B\Longrightarrow e^B$ is orthogonal.

SkewAdjoint means the adjoint of B is minus B. Unitary means that the map times its adjoint, in either order, is identity; over the real field this is orthogonality. The statement says that exponentiating a skew-adjoint bounded operator gives such a map. The green proof applies Mathlib directly. For a real time parameter, apply this result to t times B, which is still skew-adjoint.

## ExLeanSplit: Preservation of a split in Lean

Why: Keep commutation distinct from orthogonality.
Recall: $BP=PB\Longrightarrow e^BP=Pe^B$.

Commute names the equation B P equals P B. The conclusion is the same equation after exponentiating B. The proof line uses the general exponential commutation API. When P is a projection, this says the flow preserves its two subspaces. No skew-adjoint hypothesis appears in this fact: commutation and length preservation are separate conclusions, obtained from separate hypotheses.

## ExComputation: Bonus: Computing an exponential versus applying one

Why: A definition by a series does not prescribe the best numerical evaluation method.
Recall: A rational approximation is a quotient of polynomials; s controls scaling and squaring.

As an optional numerical bonus, here is how this mathematical tool is used in computation. The power series defines the matrix exponential, but a production numerical routine does more than sum a fixed number of its terms. For a dense matrix, SciPy uses an adaptive Padé approximation with scaling and squaring. First scale t times A down by a power of two. On that smaller input, approximate the exponential by a ratio of matrix polynomials. The displayed equation is solved as a linear system; we do not need to form a matrix inverse explicitly. Repeated squaring then reverses the scaling. The approximation degree and scaling are chosen using error estimates. If we only need the product of the exponential with one or a few vectors, we can instead use an exponential-action algorithm such as expm multiply. That can avoid building a large full exponential, especially for sparse operators. Which method is appropriate depends on the desired output, matrix structure, accuracy, and cost.
