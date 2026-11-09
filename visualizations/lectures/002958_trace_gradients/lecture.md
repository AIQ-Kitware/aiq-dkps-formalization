# Trace pairings and matrix gradients

## TgTitle: Trace pairings and matrix gradients

Why: Turn a matrix derivative into a scalar test.
Recall: Inner products, matrices, and ordinary derivatives.

Trace pairings and matrix gradients.

## LectureOutcomes: Three statements behind the notation

Why: Give the derivative formula a concrete job.
Recall: Finite real matrices.

The Frobenius pairing is a dot product between matching matrix entries. A matrix gradient stores the first-order response to every matrix direction. Testing only legal directions yields only the corresponding gradient conditions. We want to read a formula such as trace of a matrix product as an ordinary measurement of a change in cost. First we will see its entries, then derive a gradient, and finally restrict the allowed changes.

## TgSetup: A cost and a direction of change

Why: Fix the local setting and explain the objects.
Recall: The opening conclusions describe what we will establish.

Our variables are finite real matrices. X is the current input to a scalar cost F, and D is a proposed matrix direction of the same shape. The curve X plus t D turns the matrix question into an ordinary derivative in t. Trace sums diagonal entries of a square matrix. The Frobenius pairing instead multiplies corresponding entries and adds; we will derive its trace representation. The gradient names the matrix representing all these directional derivatives at X.

## TgPairing: A dot product laid out as a matrix

Why: Explain what the trace is measuring.
Recall: X and D have the same rectangular shape.

A dot product pairs corresponding coordinates and adds the products. A matrix can be viewed as a rectangular list of coordinates, so the same rule gives the Frobenius pairing. The colored boxes match entries of X and D. Their products add to the displayed scalar. This gives the trace expression a meaning before we manipulate it. The name recalls Ferdinand Georg Frobenius, a nineteenth-century algebraist whose work helped shape matrix theory. Here the operation is simply a dot product organized as a matrix.

<!-- beat -->

The diagonal entry j of X transpose D sums the products in column j of the original matrices. Taking the trace adds those column sums. Thus trace of X transpose D is exactly the entrywise dot product. The transpose is essential: trace of X D would in general pair different entries, and for rectangular matrices it might not even be defined.

## TgCyclic: Move factors cyclically, not arbitrarily

Why: Prepare the trace manipulations used in derivative proofs.
Recall: The products must have compatible shapes.

For square real matrices, trace of A B equals trace of B A. Both expand to the same sum of a i j times b j i. Repeating this observation allows cyclic rearrangement of a longer product. It does not permit swapping two adjacent factors while leaving all other positions fixed. The trace may be unchanged even though the product matrix changes. We will use the scalar equality to expose a chosen direction at the end of a derivative formula.

## TgDerivative: Derive a gradient from a cost

Why: Connect the name to a response already computed.
Recall: Example: F of X is one half of the squared Frobenius norm.

Change X to X plus t D. Expanding the squared entries gives F of X plus t times the Frobenius pairing of X and D, plus one half t squared times the squared norm of D. At zero, the derivative is therefore the pairing of X and D. The matrix X stores the response to every direction D. For this cost, it is the gradient.

<!-- beat -->

The graph follows this one-dimensional cost along the chosen matrix direction. Its tangent slope at zero is the scalar pairing. A different D would give a different curve and slope, while the gradient at X would remain the same matrix. A derivative here is a linear function of D; the gradient represents that function using our chosen matrix inner product.

## TgTests: A zero response can mean different things

Why: Distinguish all-direction tests from constrained tests.
Recall: D ranges over the directions we are allowed to test.

If the pairing of H and D vanishes for every matrix D, choose D equal to H. The result is the sum of squared entries of H, so H must be zero. But suppose only diagonal D are allowed. Then every response vanishes exactly when the diagonal entries of H vanish. Off-diagonal entries can remain. The displayed example has zero response to every diagonal direction without having a zero gradient. A constraint determines what the derivative tests can detect.

## TgSkew: Why a skew gradient can give a negative trace

Why: Resolve the sign convention in rotation derivatives.
Recall: G and B are real skew-symmetric matrices.

Some proofs write the derivative as minus trace of G B instead of using the familiar transpose form. Since G transpose equals minus G, these are the same Frobenius pairing. In a plane, write G equals a J and B equals b J, where J is a quarter-turn and J squared is minus identity. The derivative pairing is then two a b. That factor two comes from two real directions. Choosing B equal to G, when that is an allowed direction, makes the pairing a squared norm, which is why it is such a useful stationarity test.

## TgSummary: Read the derivative before using it

Why: Reinforce the opening claims and limits.
Recall: The gradient depends on the inner product convention.

The Frobenius pairing is a dot product between matching matrix entries. A matrix gradient stores the first-order response to every matrix direction. Testing only legal directions yields only the corresponding gradient conditions. Expand one product if the trace notation becomes opaque. Identify the matrix that pairs with the direction. Finally, state which directions are legal before concluding that any part of the gradient vanishes. A zero first derivative is a necessary condition at a differentiable minimum, not a proof of global optimality.

## TgFacts: Two trace identities that power the argument

Why: Connect algebra with the derivative tests.
Recall: The next statements use square real matrices.

Cyclicity lets us write trace A B as trace B A. Positivity says trace of C transpose C is zero exactly when C is zero. The second is a sum-of-squares fact, not a statement that any zero-trace matrix vanishes. Together these identities justify rearranging a derivative and testing it against its own response matrix.

## TgLean: Lean: cyclicity of the trace

Why: Match the symbolic identity to the library theorem.
Recall: A and B are square matrices with the same finite index set.

Matrix trace multiplication commutation names the equality of the two scalar traces. It does not claim that A and B commute as matrices. The Lean proof applies that exact library identity.

## TgLeanPositive: Lean: the squared-norm test

Why: Keep the transpose in the statement.
Recall: C is an arbitrary real matrix.

The theorem uses conjugate transpose in its general form. For real matrices this is transpose, so the displayed statement is the sum-of-squares test we just used. Lean simplifies the scalar convention and applies the accepted zero-if-and-only-if theorem. Removing the transpose would change the claim and make it false.

## TgComputation: Bonus: checking a directional derivative

Why: Use a numerical check without confusing it with a proof.
Recall: F is differentiable at X and D is a chosen direction.

A central difference uses F of X plus h D minus F of X minus h D, divided by two h. Compare it with the gradient pairing. Vary h: large h has approximation error, while extremely small h can amplify roundoff. Try several directions, not just one that happens to give zero. Automatic differentiation can compute gradients, but its output still needs the same matrix-shape and inner-product interpretation.
