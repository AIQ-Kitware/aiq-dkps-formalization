# The exponential of a matrix

Authored transcript for `prereq-matrix-exponential`. Basic matrix multiplication,
power series, and one-variable derivatives are assumed; differential equations
are introduced locally. Historical context: Cayley,
[A Memoir on the Theory of Matrices (1858)](https://doi.org/10.1098/rstl.1858.0002),
and Higham, [The Scaling and Squaring Method for the Matrix Exponential Revisited (2005)](https://doi.org/10.1137/04061101X).
These are context for matrix algebra and numerical computation, not claims
about who first defined the matrix exponential.

## Ex00Question: Turn a velocity rule into an actual motion

Why: The variations proof needs an exact curve, not just a first-order approximation.
Recall: $A$ is fixed; $x\prime(t)=Ax(t)$ prescribes velocity at the current position.

For a scalar, the rule x prime equals a times x produces exponential growth
or decay. What happens if x has several coordinates, and their velocities
are mixed by a matrix A? The matrix exponential is the time-evolution map
for this constant linear rule. Given the initial vector, it tells us where
the vector is at any time. Our immediate purpose is geometric: a
skew-symmetric velocity should produce an exact rotation, so that variations
preserve orthogonality. We will build the exponential, examine stretching,
shearing, and rotation, and establish the identities needed by that proof.

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
