# Feasible variations and stationarity

Prerequisite lecture. Historical context: Euler's
[Methodus inveniendi (1744), E65](https://scholarlycommons.pacific.edu/euler-works/65/).
The connection is the use of variations to obtain necessary conditions;
no claim is made that Euler proved this matrix transport argument.

## VaTitle: Feasible variations and stationarity

Why: Move within the constraints. Test what a minimum requires.
Recall: No notation is needed on the title slide.

Feasible variations and stationarity.

## Va00Question: How do we improve a map without breaking its constraints?

Why: An arbitrary change to a feasible map usually leaves the feasible set.
Recall: Feasible means satisfying the constraints for every parameter value.

First consider a familiar constrained problem: minimize height on the unit
circle. At the bottom point, moving straight downward would lower the height,
but that move leaves the circle. A permissible motion travels along the circle.
Its height has zero derivative at the bottom, even though the ambient gradient
of height is not zero.

<!-- beat -->

Our transport problem has two constraints: W must remain orthogonal, and it
must keep carrying the source subspace onto the target. We need explicit
curves that respect both conditions. At a minimizing W, the cost derivative
along every such curve vanishes. This lecture constructs those curves and
shows how particular derivative tests force the gradient's diagonal blocks
to vanish. We will construct the available directions rather than assume
the existence of an algorithm that knows the answer.

## Va01History: Variations turn an optimization problem into equations

Why: Necessary conditions can expose structure before we know a minimizer explicitly.
Recall: A variation is a parameterized change in the object being optimized.

Euler's 1744 book on the calculus of variations studied extremal curves and
necessary conditions for them, including problems with restrictions on the
curves. Our objects will be finite matrices rather than entire curves, but
the useful pattern is similar: describe allowed changes, differentiate the
objective along them, and use the resulting equations. This historical
connection is about a method of reasoning. We will derive the actual
orthogonality and transport conditions directly, and we will keep necessary
conditions separate from a proof that an optimizer is globally best.

## Va02Velocity: Orthogonality forces a skew-symmetric velocity

Why: Differentiating the constraint identifies possible directions of motion.
Recall: $V(0)=I$ and $B=V\prime(0)$.

Suppose V of t is a differentiable curve of orthogonal matrices starting at
the identity. Differentiate V transpose V equals identity at zero. The product
rule gives B transpose plus B equals zero. Such a matrix B is called
skew-symmetric. It is a velocity, not generally an orthogonal matrix itself.

<!-- beat -->

In a two-dimensional plane it has the displayed form, with a real speed b.
Write J for the displayed quarter-turn, so B is b times J.
Applied to a vector, it points perpendicular to that vector. This is the
instantaneous velocity of a rotation. The skew-symmetry condition is necessary
for an orthogonal motion. Next we need the converse construction: given
such a velocity, build a curve that remains exactly orthogonal, rather than
only satisfying the constraint to first order.

## Va03Exponential: Build an exact motion from its velocity

Why: The linear approximation $I+tB$ does not remain orthogonal.
Recall: $V(t)=\exp(tB)$ and $B^T=-B$.

The naive curve identity plus t B has the correct velocity, but it is not
exactly orthogonal. For a unit vector in the plane, it follows the tangent
line and leaves the circle. The exponential of t B follows the rotation
instead. It starts at identity and has velocity B at zero.

<!-- beat -->

Why does it preserve orthogonality for every t? Transposing the exponential
gives the exponential of t B transpose, which is the exponential of minus
t B. This is the inverse of the exponential of t B. Their product is identity.
Thus every skew-symmetric B supplies an exact orthogonal curve. In the planar
example the exponential is an ordinary rotation through the angle t b.
The exponential has solved the first constraint, but we must still preserve
the source subspace.

## Va04SourceMotion: Rotate within the source rather than away from it

Why: Source-preserving motions exist by an explicit block construction.
Recall: Here $K$ is the first coordinate plane in $\mathbb R^3$.

Take K to be a coordinate plane. Rotate a chosen orthonormal basis within
that plane and leave its perpendicular direction fixed. This is a real,
nontrivial orthogonal motion that sends K onto itself. Its generator has a
two-dimensional skew block on K and zero on the complement.

<!-- beat -->

More generally, choose arbitrary skew-symmetric diagonal blocks in the
decomposition K plus its orthogonal complement. The resulting B commutes
with P, the source projection. Every power of B then commutes with P, so
the exponential does too. Its inverse also preserves K, and therefore the
exponential maps K onto K. If a block is one-dimensional, its only
skew-symmetric velocity is zero; the construction still works on the
other blocks. No mixing between the two spaces is required to make a
nontrivial test available when a block has dimension at least two.

## Va05Feasible: Compose a source motion with the transporter

Why: Right multiplication keeps the transported subspace fixed.
Recall: $W(K)=L$ and $V(t)(K)=K$ imply $(WV(t))(K)=L$.

Now fix any feasible W. First apply our source-preserving motion, then apply
W. Since the first map sends K onto itself, the composite still sends K
onto L. Both maps are orthogonal, so their product is orthogonal too. This
constructs an entire feasible curve through W: W times the exponential of t B.

<!-- beat -->

Notice exactly which map commutes with P. It is B, the chosen source velocity,
and consequently its exponential. We have not required W to commute with P.
Indeed W usually has to carry K to a different subspace. Source-preserving
motions can change which source vector reaches which target vector while
leaving the whole image space fixed. This gives the freedom needed for a
derivative test without restricting the original optimization problem.

## Va06Stationarity: At a minimum, every feasible first derivative vanishes

Why: A scalar derivative condition captures the effect of each allowed motion.
Recall: $h_B(t)=\Phi_p(W\exp(tB))$, with $1<p<2$.

Choose a global minimizer W of the differentiable power cost. For every
admissible B, our feasible curve exists for both positive and negative t.
The ordinary real-valued function h B therefore has a minimum at zero.
Elementary calculus gives h B prime at zero equal to zero. This statement,
for all the allowed B, is stationarity.

<!-- beat -->

The equation is necessary, not sufficient. At the top of the unit circle,
height also has zero derivative along every tangent motion, but that point
is a maximum. In the matching proof we already choose a global minimizer
using compactness. Stationarity extracts information from that chosen
minimizer. It is not the argument establishing its existence or its global
optimality.

## Va07Gradient: Package the first derivatives as a trace pairing

Why: One matrix lets us evaluate all the derivative tests.
Recall: $G^T=-G$ and $D\Phi_p(W)[WB]=\langle G,B\rangle_F=-\operatorname{tr}(GB)$.

At a fixed W, the derivative along W exponential t B depends linearly on the
skew velocity B. To define the gradient, allow every skew-symmetric B, even
when the curve does not preserve the source. Only source-preserving directions
will give stationary tests. In this finite-dimensional space, we can represent that
linear functional by a unique skew-symmetric matrix G using the Frobenius
inner product. This inner product is trace of G transpose B. Since G is
skew-symmetric, the pairing is minus trace of G B. This defines the
right-variation gradient used by the proof.

<!-- beat -->

Check the sign on one rotation plane. Write f p for twice sine of half the
angle, raised to the power p: the power cost of one displacement singular value.
If W rotates through phi and B is b
times the quarter-turn J, the angle changes at speed b. The plane's power
cost is twice f p of phi, so its derivative is twice b f p prime of phi.
Setting G equal to f p prime of phi times J gives exactly the same value:
J squared is minus identity, whose two-dimensional trace is minus two.
This is the source of the negative trace sign. The matching proof constructs
G on all rotation and scalar blocks; here we need the pairing to perform
the stationarity tests.

## Va08Test: Use the gradient to construct an admissible test

Why: A derivative equal to a squared norm forces a whole compression to vanish.
Recall: Choose $B=PGP$, where $P^T=P=P^2$ and $G^T=-G$.

Choose B equal to P G P. Transposing shows that it is skew-symmetric. Multiplying
by P on either side gives P G P again, so it commutes with P. It is therefore
one of our available directions, even though we chose it using the unknown
gradient. This is a proof device: we test a necessary condition at a minimizer,
not an algorithm that needs to know the minimizer in advance.

<!-- beat -->

Stationarity gives zero equal to minus trace of G P G P. By cyclicity of
trace and P squared equals P, this equals minus trace of the square of
P G P. Since that compression is skew-symmetric, the same quantity is its
squared Frobenius norm. The displayed equalities spell out that conversion.

<!-- beat -->

A squared norm can vanish only when its matrix is zero. Hence P G P vanishes.
Repeat the argument with identity minus P in place of P, and the complementary
compression also vanishes. Two explicitly admissible tests have removed both
diagonal gradient blocks. This is the structural information we needed from
stationarity.

## Va09Structure: The conclusion concerns the gradient, not the transporter

Why: Zero diagonal gradient blocks are the entry point to the later decomposition.
Recall: $J_{\mathrm{src}}=2P-I$ acts as $+I$ on $K$ and $-I$ on $K^\perp$.

In source coordinates, G now has zero diagonal blocks. Its remaining blocks
are negatives of each other's transposes because G is skew-symmetric. This
does not say that W is block diagonal in the same coordinates. The tests
constrained the derivative of the objective, not the original transporter's
action on the principal planes.

<!-- beat -->

The source reflection acts by plus identity on K and minus identity on its
complement. Multiplying G by that reflection on both sides reverses the
sign of each remaining off-diagonal block. So the same conclusion is written
as J source G J source equals minus G. The matching proof combines this
identity with the spectral construction of G to find common invariant
blocks. We have now supplied the missing justification for that first
structural step.

## Va10Recap: Construct the motion, then test the derivative

Why: The proof obtains structure from available variations without restricting $W$.
Recall: Skew velocity, source preservation, feasible curve, gradient test.

The chain of reasoning is constructive. A skew-symmetric velocity exponentiates
to an orthogonal motion. Making that velocity commute with the source
projection preserves the source subspace. Right composition with W then
preserves transport. At a minimizing W, every such directional derivative
vanishes. Testing with the two gradient compressions makes both diagonal
gradient blocks zero.

<!-- beat -->

Check your understanding: does this prove that W commutes with P, or that every
stationary point is a minimum? Neither. It proves a necessary condition on the
gradient at a chosen minimizer. You can now return to the matching proof's
stationarity step and explain why its test directions exist. The next layer
of that proof uses the gradient and source reflection to construct the
two- and four-dimensional blocks; it does not assume those blocks at the start.
