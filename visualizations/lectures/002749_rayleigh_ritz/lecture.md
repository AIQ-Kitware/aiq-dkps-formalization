# Rayleigh–Ritz: trial spaces, compression, and residuals

Authored by GPT-6.1-Sol. Mathematical and Lean correspondence: `sources.md`.

## RrTitle: Rayleigh–Ritz

Why: Build a smaller eigenproblem from a chosen search space.
Recall: A trial space is a candidate search space.

Rayleigh–Ritz: trial spaces, compression, and residuals.

## RrSetup: The objects we will keep separate

Why: The subspace, its coordinates, and the small operator have different jobs.
Recall: An orthonormal frame has mutually perpendicular unit columns.

We start with a real symmetric matrix A acting on n-dimensional vectors. Choose a nonzero k-dimensional subspace, with k no larger than n. We call it the trial space because it is where we will search for approximate eigenvectors. Q is a matrix whose k orthonormal columns span that space. B will be the smaller k by k matrix we construct. A Ritz value will be written theta; here theta is an approximate eigenvalue, not an angle. Transposes become conjugate transposes for complex Hermitian matrices, and all the matrix arguments still work.

## RrQuestion: Why choose a smaller search space?

Why: A restricted search can be affordable even when the full problem is not.
Recall: Eigenvectors satisfy A u equals lambda u.

An eigenproblem asks for directions that A only scales. For a large matrix, searching the entire space can be expensive. We may instead have a small collection of plausible directions: previous iterates, physically meaningful functions, or vectors obtained by repeatedly applying A. Their linear combinations form a smaller space in which we can search.

<!-- beat -->

Rayleigh’s work on vibration and Ritz’s variational approximation method are historical landmarks behind this strategy. They were separate contributions, not a joint paper. The mathematical question is how to turn a chosen search space into a useful eigenproblem, and how to check what its answers mean in the original space.

## RrSpace: Trial means chosen for the search

Why: The name describes a role, not an accuracy theorem.
Recall: A subspace contains every linear combination of its vectors.

Choose candidate directions and allow all their linear combinations. That set is the trial subspace. We can choose it before knowing any exact eigenvectors. It might be a line, a plane, or a much higher-dimensional space. Trial does not mean random, and it does not mean already proved close to the answer.

<!-- beat -->

Three claims must be kept separate. A trial space is where we search. An invariant space is one that A maps into itself. A wanted spectral space is the exact eigenspace or cluster we are trying to approximate. A chosen trial space need not be invariant or close to the wanted space. Those are questions to investigate after the choice.

## RrFrame: Q supplies coordinates in the trial space

Why: We need a way to move between a small vector and its ambient representative.
Recall: Q has orthonormal columns: Q transpose Q equals the small identity.

Write the trial space as the range of Q. A small coordinate vector y becomes the ambient vector u equals Q y. Orthonormal columns make this map preserve lengths: the norm of Q y equals the norm of y. Conversely, Q transpose u gives the coordinates of a vector already in the trial space.

<!-- beat -->

For an arbitrary ambient vector v, Q transpose v computes its coefficients against those columns. Lifting those coefficients gives Q Q transpose v, the orthogonal projection onto the trial space. Call that ambient projection P. Q and P are different objects: Q changes the size of the coordinate vector; P maps the ambient space to itself.

## RrCompress: Apply A, then project back

Why: A trial vector can leave the search space when A acts on it.
Recall: P equals Q Q transpose; Q transpose Q is the identity.

Start with trial coordinates y. Lift to Q y, apply A to get A Q y, and take trial coordinates again using Q transpose. The result is Q transpose A Q y. This defines the small matrix B equals Q transpose A Q. This operation is called compression.

<!-- beat -->

Lifting B y back gives Q B y, which equals P A Q y. It is the projection of the true output onto the trial space. The piece outside the trial space has been discarded. Unless the trial space is invariant, B is not simply the restriction of A as an operator into that same space. Compression deliberately includes the projection back.

## RrQuotient: Why this small matrix is the right one

Why: The compression preserves the original directional measurement on every trial vector.
Recall: For a unit vector u, the Rayleigh quotient is u transpose A u.

For a unit coordinate vector y, u equals Q y is also unit. Its original Rayleigh quotient is y transpose Q transpose A Q y, which is exactly y transpose B y. Thus solving the small symmetric eigenproblem is optimizing the original Rayleigh quotient over the chosen trial space.

<!-- beat -->

This is an exact statement about a restricted search, not an assertion that the restricted answer equals the global answer. Symmetry is preserved because B transpose equals Q transpose A transpose Q, which equals B. The small problem therefore has an orthonormal eigenbasis just as the full symmetric problem does.

## RrSolve: Solve small, then lift

Why: Small eigenvectors describe combinations of the trial directions.
Recall: B y equals theta y is a k-dimensional eigenproblem.

Solve B y equals theta y with y a unit vector. Theta is a Ritz value. The lifted vector u equals Q y is a Ritz vector in the original space. It is not generally one of the columns of Q: the small eigenproblem chooses a useful linear combination of those columns.

<!-- beat -->

Inside the trial space, the projected equation is satisfied exactly: P A u equals theta u. In the full space, the error is r equals A u minus theta u. We call that the eigenpair residual. To determine whether the Ritz vector is an exact eigenvector, we must check this full residual, not just the small equation.

## RrGeometry: The missing component is visible

Why: Compression removes the part of the output perpendicular to the trial line.
Recall: This example uses a one-dimensional trial space.

Consider A diagonal with entries one and four. The amber unit vector q spans our trial line. Applying A produces the cyan vector A q, which usually leaves that line. Project it back: the amber output along the line is theta q, where theta equals q transpose A q. The green arrow from that projected output to the true output is the residual.

<!-- beat -->

Now rotate the trial line toward the eigenvector for eigenvalue one. Both theta and the residual change. The residual shrinks to zero as the line becomes invariant. The important identity is A q equals theta q plus r, with r perpendicular to q. This picture explains the algebra of Rayleigh–Ritz before we write it for many trial directions.

## RrExample: A two-dimensional trial space

Why: A small eigenproblem combines candidate directions and reveals different residuals.
Recall: Use the first two coordinate directions as the trial space.

Here is a three by three symmetric matrix, and choose Q with columns e one and e two. Its compression is the top-left two by two block, with diagonal entries two and off-diagonal entries one. That small matrix has the sum direction with Ritz value three, and the difference direction with Ritz value one.

<!-- beat -->

Lift both normalized directions by appending a zero third coordinate. The sum direction has zero full residual: the two couplings into the third coordinate cancel. The difference direction has residual of length square root of two, entirely along the third coordinate. One Ritz vector can be exact even when the whole trial space is not invariant.

## RrBlock: The block structure records where the output goes

Why: Adapt coordinates to the trial space and its perpendicular complement.
Recall: Q spans the trial space; Q perpendicular completes an orthonormal basis.

Complete the columns of Q to an orthonormal basis using a frame for the perpendicular complement. In those coordinates, the matrix has blocks B and C in its first block column. B records the output that remains in the trial space. C records the output that escapes into its perpendicular complement. Symmetry makes the opposite block C transpose.

<!-- beat -->

The compression is B. The Ritz residual is the ambient version of C: in these coordinates its top block is zero and its bottom block is C. So the trial space is invariant exactly when C is zero. This block decomposition does not assume invariance. It separates retained output from leakage, and lets us measure the leakage.

## RrOrthogonality: Derive residual orthogonality

Why: The defining small model removes every residual component inside the trial space.
Recall: B equals Q transpose A Q, and Q transpose Q equals I.

Collect all trial directions at once in the residual matrix R equals A Q minus Q B. Multiply on the left by Q transpose. The first term becomes B by the definition of compression. The second becomes B because Q transpose Q is the identity. Their difference is zero.

<!-- beat -->

Thus every column of R is perpendicular to the whole trial space. This is often called Galerkin orthogonality. Equivalently, R equals I minus P, applied to A Q. For an individual small eigenvector y, its full eigenpair residual is R y. Orthogonal does not mean zero: it means the entire error is in directions our restricted search could not represent.

## RrModel: A trial space and a small model are separate choices

Why: Rayleigh–Ritz makes a particular model choice after the trial space is fixed.
Recall: M is any k by k proposed action on trial coordinates.

Keep Q fixed, but propose an arbitrary small matrix M instead of the compression B. Its residual is A Q minus Q M. Add and subtract Q B. This splits the residual into the Ritz residual R, which lies outside the trial space, plus Q times B minus M, which lies inside it.

<!-- beat -->

Those two pieces are orthogonal column by column. Pythagoras therefore gives the squared Frobenius residual as the squared Ritz residual plus the squared Frobenius norm of B minus M. The choice M equals B is the unique best fit in this norm for this fixed orthonormal frame. That does not choose the best trial space: it chooses the best small model on a space we have already chosen.

## RrQuality: A small residual still needs interpretation

Why: Accuracy of an eigenpair and identification of a wanted spectral target are different questions.
Recall: A is symmetric and the Ritz vector u has unit norm.

Expand u in an exact orthonormal eigenbasis. The squared residual is the sum of the squared coefficients times lambda j minus theta, squared. It follows that some exact eigenvalue lies within the residual norm of theta. A small residual therefore gives a meaningful eigenvalue inclusion statement for a symmetric matrix.

<!-- beat -->

It does not by itself identify the wanted eigenvalue or subspace. In the diagonal example, choosing the eigenvector for four gives zero residual, even if our target was the eigenvector for one. To turn residual size into a bound on the angle to a specified target, we also need the appropriate spectral separation. This is where Davis–Kahan enters.

## RrMinmax: What enlarging the trial space guarantees

Why: A larger search space improves extremal variational estimates.
Recall: Compare nested, nonzero trial spaces for the same symmetric matrix.

The smallest Ritz value is the minimum Rayleigh quotient over unit vectors in the trial space. It is at least the smallest exact eigenvalue, because we minimize over fewer choices. If we enlarge the trial space, that minimum cannot increase. Dually, the largest Ritz value cannot decrease when the trial space grows.

<!-- beat -->

These are useful directional guarantees: the smallest estimate moves downward toward the global minimum, and the largest moves upward toward the global maximum. They do not say how fast an arbitrary sequence of spaces converges, and they do not establish that a particular space approximates a chosen interior spectral cluster. The min–max lecture develops the broader variational picture.

## RrPaper: Translate the residual notation

Why: The general residual framework includes Rayleigh–Ritz as a specific choice.
Recall: The operator under study is written A-hat in the residual theorem.

In the Davis–Kahan residual notation, the trial frame is E zero, the proposed small operator is A zero, and R equals A-hat E zero minus E zero A zero. The trial subspace is the range of E zero. In our finite matrix discussion, E zero plays the role of Q. The Rayleigh–Ritz choice is A zero equals E zero adjoint A-hat E zero.

<!-- beat -->

The general residual theorem need not make that choice. For example, a perturbation argument may use an old operator’s invariant subspace and its old small model while studying a new operator. That residual need not be orthogonal to the trial space. For an unbounded operator, the trial vectors must additionally lie in its domain, with the domain and bounded-residual assumptions required by the theorem. Our matrix derivation explains the geometry without removing those analytic requirements.

## RrSummary: Choose, compress, solve, check

Why: Keep the approximation pipeline and its guarantees distinct.
Recall: Trial space is a search choice; Ritz residual measures the discarded output.

Choose a trial subspace and an orthonormal frame Q. Compress A to B equals Q adjoint A Q. Solve the small eigenproblem, lift each eigenvector, and inspect the full residual. The Ritz residual is perpendicular to the trial space because the projected equation was solved exactly.

<!-- beat -->

The trial space is not assumed invariant, and the compression does not promise that it is a good approximation to our target. It provides a principled small model, a variational interpretation, and an explicit residual. Target identification and spectral separation supply the further information needed for subspace accuracy.

## RrFacts: Three reusable identities

Why: The definitions explain the error decomposition.
Recall: Q is isometric, B is the compression, and R equals A Q minus Q B.

Carry three identities into another proof. Compression is Q adjoint A Q. The Ritz residual satisfies Q adjoint R equals zero. Every other model residual A Q minus Q M equals R plus Q times B minus M. The following Lean cards show accepted Tau Ceti statements for these same identities, in bounded Hilbert-space language.

## RrLean: Lean: the compression

Why: Match the abstract operator definition to the small matrix.
Recall: X in Lean is the isometric trial map Q on the slides.

Lean writes continuous linear maps between a trial-coordinate space F and an ambient space E. X is our frame Q, and adjoint X is Q adjoint. A dot compression X is the small operator B. The first identity simply unfolds that definition. This definition works without a self-adjointness assumption; self-adjointness matters when we interpret the resulting small problem as a Hermitian eigenproblem.

## RrLeanOrthogonal: Lean: residual orthogonality

Why: The isometry hypothesis makes the projected residual vanish.
Recall: A dot sylvester M X means A X minus X M.

The second card inserts the compression as the small model. A dot sylvester of that model and X is our Ritz residual R. Composing on the left with adjoint X gives zero. The hypothesis h X says X is an isometry, which supplies Q adjoint Q equals the identity. The accepted theorem proves exactly the cancellation shown earlier.

## RrLeanSplit: Lean: split any model residual

Why: Changing the small model adds a component inside the trial space.
Recall: M is an arbitrary small bounded operator.

The last card writes every model residual as the Ritz residual plus X composed with the difference between the compression and M. This algebraic splitting itself needs no symmetry or isometry assumption. With the isometry hypothesis from the previous card, the two output pieces are orthogonal. That is the starting point of the Pythagoras and fixed-space minimality argument.

## RrComputation: Computing a Rayleigh–Ritz step

Why: This bonus concerns implementation, after the exact mathematical construction.
Recall: The working basis must be orthonormal for the formulas used above.

An implementation normally obtains Q by a stable orthogonalization such as QR, applies A to its columns, forms Q adjoint A Q, and solves the small Hermitian eigenproblem. With sparse matrices or an operator interface, applying A can avoid storing a dense matrix. If the original basis V is not orthonormal, the corresponding reduced problem uses the Gram matrix V adjoint V: V adjoint A V y equals theta V adjoint V y. Do not silently replace that Gram matrix by the identity. Check orthogonality numerically and recompute the full residual for lifted Ritz vectors. Krylov and subspace iteration methods mainly differ in how they construct and improve the trial spaces.
