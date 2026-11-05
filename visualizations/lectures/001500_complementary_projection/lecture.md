# Thinking about I minus P

A standalone explanation of complementary projection and geometric error.
Mathematical sources: Mathlib `Analysis/InnerProductSpace/Projection/Basic.lean`
and the sine-block notation in the journal's `math_symbol_colors.tex`.
Numerical reference: https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.qr.html

## CpTitle: Thinking about I minus P

Why: Understand the operation hiding inside projection-error formulas.
Recall: P is an orthogonal projection.

Thinking about identity minus a projection.

## CpSetup: The identity, the projection, and the complement

Why: Name the objects before subtracting operators.
Recall: P projects onto K; I is identity; K perpendicular is the orthogonal complement.

We work in real Euclidean space. K is a linear subspace, and P is the orthogonal projection onto it. Projecting twice changes nothing, which is the equation P squared equals P. Orthogonality is the extra property that P transpose equals P. Identity, written I, leaves every vector unchanged. Subtracting two linear maps means subtracting their outputs on the same input. Thus identity minus P applied to x is x minus P x. K perpendicular consists of all directions perpendicular to K. We will show that identity minus P keeps exactly that perpendicular component. Later, W will name a general motion, so we can compare the two subtraction formulas without confusing their geometry.

## CpQuestion: What remains after fitting a vector?

Why: Tie the notation to the classical least-squares approximation problem.
Recall: The projected vector Px lies in K.

The motivating problem is the classical least-squares question: which vector in a subspace best approximates a given measurement? Orthogonal projection answers that fitting question. But after finding the fitted vector, we also want to understand what the fit misses. Write the original vector as the fitted part plus the difference between original and fitted. That difference is x minus P x, or identity minus P applied to x. Before thinking about a matrix of entries, read this as an instruction: keep the original vector, subtract the component that the projection kept, and examine what remains. This same geometric remainder is what appears inside subspace-error formulas.

## CpSplit: Original, fitted, and missing components

Why: See subtraction as a right-triangle decomposition.
Recall: The blue horizontal axis is K; the amber unit vector is v.

For a concrete example, let K be the horizontal coordinate axis. Its projection matrix keeps the first coordinate and sets the second to zero. Take the amber unit vector v, with coordinates cosine theta and sine theta. Its blue projection has coordinates cosine theta and zero. The original vector and its fitted part share the same horizontal coordinate.

<!-- beat -->

The pink arrow runs from the blue projected tip back to the amber original tip. It is the difference v minus P v. Its coordinates are zero and sine theta, so it is perpendicular to the horizontal subspace. We could translate that arrow to start at the origin without changing the vector it represents. Notice the sign: this is original minus fitted. The actual move from the original vector onto the subspace points the other way and is P v minus v. Their norms agree, but their directions are opposite.

## CpKeep: What the complementary projection keeps

Why: Derive the operator from its action on the two subspaces.
Recall: Every vector splits uniquely as k plus z, with k in K and z perpendicular to K.

Now use the same reasoning without choosing coordinates. Split x into k plus z, with k in K and z perpendicular to K. P keeps k and kills z. Identity keeps both. Subtracting therefore kills k and keeps z. That proves identity minus P is the orthogonal projection onto K perpendicular. Applying it a second time changes nothing, because z is already perpendicular. Projecting its output back onto K gives zero. These are the equations identity minus P squared equals identity minus P, and P times identity minus P equals zero. They describe a filter for the perpendicular component, not a new motion that preserves every vector's length.

## CpAngle: Why the sine of an angle appears

Why: Turn the perpendicular component into a quantitative error.
Recall: v is a unit vector making an acute angle theta with K.

In this two-dimensional picture, the original unit vector is the hypotenuse of a right triangle. The projected component is the adjacent side, with length cosine theta. The pink perpendicular component is the opposite side, with length sine theta. Its length is also the shortest distance from v to K, because orthogonal projection is the nearest point in the subspace. This is why sine appears in angle-error formulas: it is the length of the missed perpendicular component of a unit vector.

<!-- beat -->

As the amber vector turns closer to the blue subspace, the pink remainder shrinks. The projection operator P itself has not changed. We are changing the input direction. At angle zero the error vanishes; at a right angle the entire unit vector lies outside K and survives identity minus P. The general tool is to apply the complementary projection and then measure its output.

## CpRestricted: A norm-one operator can give a tiny error

Why: Distinguish a global operator norm from its action on trial vectors.
Recall: The operator norm tests the largest output length over allowed unit inputs.

There is a useful trap here. Unless the complementary subspace is zero, the operator norm of identity minus P is one. Choose any unit vector in K perpendicular: the operator leaves it unchanged. So how can identity minus P appear in a small subspace-error estimate? Because that estimate restricts which inputs we test. An orthonormal frame E zero maps coordinate vectors into a particular trial subspace, preserving lengths. The composition identity minus P times E zero first chooses a trial vector and then extracts its perpendicular error. Its norm tests only those trial vectors. For a single trial line at angle theta, the answer is sine theta, which can be arbitrarily small even though the unrestricted complementary projection still has norm one.

## CpSineBlock: From ambient error to unwanted coordinates

Why: Express the same projection error in ambient and complementary coordinates.
Recall: F zero and F one are orthonormal frames for the wanted space and its complement.

Choose a complete orthonormal decomposition of the ambient space. F zero spans the wanted space K, and F one spans K perpendicular. Then P is F zero times F zero transpose, and identity minus P is F one times F one transpose. E zero is an orthonormal trial frame. The map S equals identity minus P times E zero, so it sends trial coordinates to their geometric error in the ambient space. Now define X as F one transpose times E zero. This records exactly the same error in unwanted-space coordinates. The equation S equals F one times X follows by substitution. Since F one preserves lengths, S a and X a have equal norms for every input a, and their operator norms agree. This explains the two appearances of the sine block. The operator residual R, defined using the studied operator A hat and a trial operator A zero, is a different map; it is not just this geometric error.

## CpDisplacement: Compare projection error with rotation displacement

Why: Distinguish complementary projection from displacement under a general map.
Recall: W rotates the horizontal unit vector u to v through theta.

For any linear map T on the ambient space, identity minus T sends x to the original vector minus its output. In this sense, identity minus P measures displacement under the projection P. It also has the extra structure of a complementary projection. Compare it with a rotation W. Here W moves the horizontal unit vector u to the amber unit vector v. The pink projection error of v has length sine theta. The steel arrow goes from the moved tip v back to the original tip u; it is u minus W u. That is a chord of the unit circle, with length twice sine of half theta. Projection drops a perpendicular component, while rotation preserves lengths and moves the entire vector. Thus the formulas look related but measure different geometric operations. For a general W, identity minus W need not be a projection at all.

## CpSummary: The picture to keep

Why: Keep the operation, its geometry, and its input restriction separate.
Recall: P is orthogonal; the error convention is original minus projected.

Read identity minus P applied to x as the part of x that its projection misses. That part lies in K perpendicular, and its length is the distance from x to K. The actual move onto the subspace has the opposite sign. On all inputs, a nonzero complementary projection has norm one. Restricted to a well-aligned trial subspace, its output can be small, giving the sine block. Finally, identity minus W is the same original-minus-output pattern for a general motion, but its displacement does not usually form a complementary projection. Orthogonality of P is essential throughout: an arbitrary idempotent projects along some complement, which need not be perpendicular.

## CpFacts: Two reusable projection facts

Why: Match the geometric conclusions to precise statements.
Recall: P sub K denotes the orthogonal projection onto K.

The first fact identifies the whole operator: projection onto K perpendicular equals identity minus projection onto K. The second fact identifies where each error vector lies: x minus P sub K x belongs to K perpendicular. These facts apply in an inner product space whenever the orthogonal projection exists; finite coordinates were only our teaching example. They are the two statements shown in Lean next. Neither fact alone is a spectral perturbation theorem: spectral information is needed to relate an operator residual to this geometric error.

## CpLeanOperator: The complementary operator in Lean

Why: See the operator equality behind the picture.
Recall: K starProjection is the ambient orthogonal projection.

On the left is the operator identity. On the right, K perpendicular dot starProjection means the projection onto the orthogonal complement. ContinuousLinearMap dot id is the identity bounded linear map. The conclusion equates that complementary projection to identity minus K dot starProjection. The green line applies Mathlib's established complementary-projection theorem. The common assumptions specify a real inner product space and a subspace admitting an orthogonal projection. Their complete Lean context and imports are in the companion file.

## CpLeanError: The perpendicular error in Lean

Why: Match the output of I minus P to its geometric subspace.
Recall: Membership in K perpendicular means perpendicular to every vector of K.

This card states the pointwise geometric fact. For any vector x, subtract its orthogonal projection onto K. The result belongs to K perpendicular. The green proof line applies Mathlib directly. Together with the preceding operator identity, it gives a precise meaning to the phrase the part outside the chosen subspace. It does not say the error vanishes; vanishing requires that x itself lie in K.

## CpComputation: Bonus: compute the component through a frame

Why: Avoid forming a large dense complementary-projector matrix.
Recall: Q has orthonormal columns spanning K.

As an optional numerical bonus, suppose Q is an orthonormal frame for K. Compute the coordinates Q transpose x, reconstruct the projected vector with Q, then subtract it from x. This avoids storing the dense matrix identity minus Q Q transpose. If a complementary frame is available, its coordinates give the same error as Q perpendicular times Q perpendicular transpose x. A full QR decomposition supplies complementary columns; an economy QR supplies only the fitted-space frame when the input columns have full rank. These are choices of numerical representation for the same geometry. Very small residuals require care with cancellation and floating-point precision, so the exact geometric identity does not by itself guarantee high relative accuracy in a numerical subtraction.
