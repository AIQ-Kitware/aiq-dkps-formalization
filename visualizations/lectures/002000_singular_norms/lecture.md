# Singular values and displacement cost

Prerequisite lecture. Historical context:
[Eckart and Young (1936), The Approximation of One Matrix by Another of Lower Rank](https://doi.org/10.1007/BF02288367).
This is an application of canonical matrix coordinates, not a claim that the
paper originated the SVD. See README.md for mathematical sources and scope.

Computational references: [SciPy dense SVD](https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.svd.html) and [partial sparse SVD](https://docs.scipy.org/doc/scipy/reference/generated/scipy.sparse.linalg.svds.html).

## SnTitle: Singular values and displacement cost

Why: How a list of stretches determines the cost of a motion.
Recall: No notation is needed on the title slide.

Singular values and displacement cost.

## SnSetup: Our local notation

Why: Distinguish matrix entries, singular values, and norms.
Recall: $s_j(T)$: singular values; $\|T\|_*$: trace norm.

For this lecture, T is a real matrix. T transpose is its adjoint in real coordinates. Apply T and then its transpose: the resulting square matrix T transpose T has nonnegative eigenvalues. Their nonnegative square roots are the singular values of T, which we write s sub j of T. They describe the stretch factors along suitable orthonormal input directions. The operator norm takes the largest stretch factor. The trace norm adds all of them; the Frobenius norm is the square root of the sum of their squares. We will motivate these choices geometrically. When W is a motion, identity minus W is the displacement map. Its singular values measure movement, not the singular values of W itself.

## Sn00Question: What does it cost to move a whole space?

Why: Two sensible measurements can prefer different maps.
Recall: $D=I-W$ measures displacement; its singular values are nonnegative stretches.

To measure movement by an orthogonal map W, apply identity minus W to a vector.
This is its displacement, with an irrelevant choice of sign. But a map moves
many directions at once. Should we charge for the worst direction, or add the
movement across independent directions? Here are two actual orthogonal maps.
A reflection has displacement stretches two and zero. A suitable planar
rotation has two stretches of one point one.

<!-- beat -->

The worst-direction measurement prefers the rotation: one point one is smaller
than two. Adding the stretches prefers the reflection: two is smaller than
two point two. Neither calculation is mistaken. We chose different objectives.
This lecture explains the stretches, the resulting norms, and the rule that
lets the matching proof add costs over independent blocks.

## Sn01History: Matrix approximation made the axes useful

Why: Canonical coordinates turn some matrix problems into scalar questions.
Recall: Low rank means that only a few independent output directions are retained.

In 1936, Carl Eckart and Gale Young studied approximation of a matrix by one
of lower rank, motivated by factor analysis. Their paper uses a canonical
matrix form to solve a least-squares problem. That is one reason the singular
value viewpoint is so useful: after choosing suitable input and output axes,
a matrix acts by separate scalar stretches. Our optimization is different,
but it uses the same benefit. We can read a norm from the stretch list instead
of from a particular array of entries. We will derive that geometric viewpoint
before returning to displacement costs.

## Sn02Stretching: A matrix sends a circle to an ellipse

Why: The singular values are geometric stretches, independent of the original axes.
Recall: $T=U\Sigma V^T$ is a singular-value decomposition.

Apply a linear map T to every point on the unit circle. In this example the
image is an ellipse. Its semiaxis lengths, two and three quarters, are the
singular values. They tell us how strongly T stretches two perpendicular
input directions. The corresponding output directions are perpendicular too.

<!-- beat -->

The singular-value decomposition names these directions. V transpose reads
coordinates in the special input basis. Sigma stretches those coordinates,
and U places the result in the special output basis. The displayed identities
say that T sends each input direction to its singular value times the
corresponding output direction. Singular values are nonnegative; they are
not generally eigenvalues. Rectangular matrices have the same input-to-output
description, even though their input and output spaces may have different sizes.

## Sn03Norms: Different norms summarize the same stretch list

Why: Choose the objective by deciding which features of the movement matter.
Recall: The operator, Frobenius, and trace norms use maximum, sum of squares, and sum.

The operator norm is the largest singular value. It measures the greatest
stretch of a unit input. The Frobenius norm is the square root of the sum of
squared singular values. It also equals the square root of the sum of squared
matrix entries. The trace norm, also called the nuclear norm, is the sum of
the singular values. For our ellipse these three summaries give different
numbers, all computed from the same two stretches.

<!-- beat -->

The name trace norm can be misleading. It is not the absolute value of the
ordinary matrix trace. A diagonal matrix with entries minus two and one has
ordinary trace minus one, but singular values two and one, so its trace norm
is three. Equivalently, the trace norm is the trace of the positive square
root of T transpose T. This removes the signs before summing.

## Sn04Invariance: Changing orthonormal coordinates does not change the cost

Why: The norm should measure the map rather than the chosen basis.
Recall: Orthogonal input and output changes preserve singular values.

Rotate the output axes. The ellipse changes orientation, but its semiaxis
lengths do not change. Rotate the orthonormal input coordinates as well: this
does not change the set of unit vectors being tested. Consequently, neither
operation changes the singular-value list.

<!-- beat -->

Algebraically, multiplying T on the left and right by orthogonal matrices
leaves each of our three norms unchanged. Over complex scalars the analogous
coordinate changes are unitary. This invariance is what allows the proof to
choose convenient coordinates for each block. It does not mean that we may
replace a given operator by any unrelated matrix with convenient entries;
we must justify the coordinate changes or compute the same singular values.

## Sn05Rotation: A rotation moves two independent directions

Why: Compute the singleton costs used by the matching theorem.
Recall: $R_\theta$ is a planar rotation; a reflection has displacement stretches $2,0$.

For a planar rotation, multiply identity minus R transpose by identity minus R.
The product is four times sine squared of half the angle, multiplied by the
identity. Both displacement singular values are therefore twice sine of half
the angle. The trace norm adds them, giving four sine of half the angle.
A reflection has displacement singular values two and zero, so its trace
cost is always two.

<!-- beat -->

At thirty degrees, the rotation is cheaper. At ninety degrees, the reflection
is cheaper. They tie at sixty degrees. Both can carry a source line onto the
same target line: the reflection axis bisects their angle. This is the
singleton choice in the matching formula. The two equal rotation singular
values are important; counting only one would underestimate the full
displacement cost by a factor of two.

## Sn06SmoothCost: A power cost makes the first derivative available

Why: The matching proof needs derivatives, while the trace norm can have corners.
Recall: $\Phi_p(W)=\sum_j s_j(I-W)^p=\|I-W\|_p^p$.

The Schatten p norm takes the sum of the p-th powers of the singular values,
then takes a p-th root. The matching proof uses its p-th power, called Phi p,
so there is no final root. At p equal to one this is the trace norm. For p
strictly greater than one, the finite-dimensional power cost is differentiable,
including at zero displacement singular values.

<!-- beat -->

The scalar picture explains the issue. Absolute value has a corner at zero,
whereas absolute value to the power one point five has derivative zero there.
The matrix differentiability statement uses singular-value calculus; it does
not follow merely by drawing this scalar graph. In the proof we first use
p between one and two to obtain stationarity and a decomposition, then let
p approach one from above. We smooth the objective to reveal structure and
ultimately recover the original trace-norm minimum.

## Sn07BlockCosts: Independent blocks have a combined singular-value list

Why: This is the exact additivity rule behind matching costs.
Recall: A block diagonal map preserves orthogonal input and output pieces.

Suppose T is block diagonal on an orthogonal decomposition. Then T transpose T
is block diagonal too. Its eigenvalues combine from the blocks, so the
singular-value list of T is the union of the block lists, including
multiplicities. We can therefore add trace costs across the blocks. Likewise,
the sum of p-th powers adds across blocks.

<!-- beat -->

Be precise about what adds. For the Frobenius norm, the squares add. For the
operator norm, take the maximum. For the Schatten p norm, the p-th powers
add; the norm itself generally does not. A rotation of sixty degrees contributes
singular values one and one, and a reflection contributes two and zero.
Their orthogonal direct sum has trace cost four. This is the rule used once
the matching proof has established common invariant blocks.

## Sn08Restrictions: Orthogonal inputs alone do not give additive costs

Why: The output pieces must also separate before the block rule applies.
Recall: $T e_1=T e_2=e_1$ in this two-dimensional example.

Here is a tempting incorrect shortcut. Split the domain into the two
perpendicular coordinate lines. Each restricted map has one singular value
equal to one. It is tempting to add those two costs and call the answer the
trace norm of the full map.

<!-- beat -->

But both input directions are sent to the same output line. The full matrix
has singular values square root of two and zero, so its trace norm is square
root of two, not two. There is no orthogonal output split making these
restrictions independent blocks. This is why the proof works to obtain a
simultaneous invariant decomposition. Writing separate domain restrictions
does not by itself justify adding their singular-value costs.

## Sn09Recap: Read the stretches before comparing the costs

Why: The objective and the block rule determine which transporter is cheapest.
Recall: Operator norm: maximum; Frobenius norm: quadratic sum; trace norm: sum.

Our main points are these. Singular values describe independent stretches
after orthonormal input and output changes. Different norms summarize that
same list differently and may prefer different maps. Trace costs and power
costs add over genuine orthogonal blocks, but not over arbitrary domain
restrictions with overlapping images. The power cost Phi p is the p-th
power of a norm, not the norm itself.

<!-- beat -->

As a check, take a map with singular values three and four. Its operator norm
is four, its Frobenius norm is five, and its trace norm is seven. You can now
compute the displacement costs that the matching theorem minimizes. The
remaining question is how a minimizer can reveal useful structure. For that,
we need variations that remain inside the set of allowed transporters.

## SnFacts: Two singular-value facts to use in a proof

Why: Calculate a displacement cost in whichever orthonormal coordinates are easiest.
Recall: A acts on a finite-dimensional real inner product space; p is at least one and finite.

The first formula says exactly how a finite Schatten norm is computed from the singular values. Raise each stretch to the power p, add, and take the power one over p. At p equals one, this adds the stretches; at p equals two, it gives the Frobenius norm. The second identity says that orthogonal changes of coordinates on either side leave the complete singular-value list unchanged. Together these facts justify calculating a Schatten cost in convenient coordinates. They do not justify adding the costs of arbitrary domain restrictions. For that, we still need genuinely separate orthogonal input and output blocks, as we saw earlier.

## SnLean: The finite Schatten formula in Lean

Why: Read the hypotheses of the norm formula.
Recall: $N_p(A)=(\sum_j s_j(A)^p)^{1/p}$.

The left formula is the finite-exponent Schatten norm. On the right, the finite-dimensional real space and exponent assumptions are explicit. The type allows infinity, so the hypothesis h p excludes it; the typeclass Fact supplies the lower bound one. SingularValues is a sequence with a zero tail. The indexed sum therefore gives the finite singular-value sum. The green proof line applies the accepted formula. This card concerns the value formula; invariance is a separate statement.

## SnLeanCoordinates: Coordinate invariance in Lean

Why: Identify which changes of coordinates preserve the singular values.
Recall: $s(UAV)=s(A)$ for orthogonal $U,V$.

Here U and V are isometric linear isomorphisms: orthogonal changes of coordinates in the finite real setting. The circled composition symbol means composition of linear maps. The conclusion says that the entire singular-value sequence is unchanged when we compose on the left and right by these isometries. The proof uses the two accepted invariance theorems in succession. Once the sequence is unchanged, every norm defined from that sequence is unchanged as well.

## SnComputation: Bonus: Computing the singular values you actually need

Why: The chosen norm determines how much spectral information a numerical routine must return.
Recall: The singular-value list determines the Schatten costs introduced in this lecture.

As an optional numerical bonus, here is how this mathematical tool is used in computation. For a dense matrix, numerical libraries call a mature singular value decomposition algorithm. SciPy's default dense driver uses LAPACK's divide and conquer routine. Once the singular values are available, computing the norms is a scalar calculation. For a very large sparse matrix, an iterative partial decomposition can seek only a few singular values. That can suit a task needing the leading stretch, provided the approximation has converged sufficiently. It does not give the full trace norm merely by summing a short leading list: the omitted values may still contribute. The practical question is therefore which part of the singular-value list our objective needs, and how accurately it must be computed.
