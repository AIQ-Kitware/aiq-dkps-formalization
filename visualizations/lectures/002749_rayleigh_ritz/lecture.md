# Rayleigh–Ritz: trial spaces, compression, and residuals

Authored by GPT-6.1-Sol. Mathematical and Lean correspondence: `sources.md`.

## RrTitle: Rayleigh–Ritz

Why: Build a smaller eigenproblem from a chosen search space.
Recall: A trial space is a candidate search space.

Rayleigh–Ritz: trial spaces, compression, and residuals.

## RrSetup: The objects we will keep separate

Why: The subspace, its coordinates, and the small operator have different jobs.
Recall: An orthonormal frame has mutually perpendicular unit columns.

How can a small eigenproblem tell us something reliable about a much larger one? We will follow one approximation from its construction to its error check. First choose the directions we allow. Then build a small matrix that describes what A does along those directions. Finally, return to the full space and measure what the small problem left out. We begin with a real symmetric matrix A; the same matrix argument uses adjoints for complex Hermitian matrices. The first object to understand is the space in which we choose to search.

## RrQuestion: Why choose a smaller search space?

Why: A restricted search can be affordable even when the full problem is not.
Recall: Eigenvectors satisfy A u equals lambda u.

Our plan begins with a choice: which directions will we allow? An eigenproblem asks for directions that A only scales. For a large matrix, searching the entire space can be expensive. We may instead have a small collection of plausible directions: previous iterates, physically meaningful functions, or vectors obtained by repeatedly applying A. Their linear combinations form a smaller space in which we can search.

<!-- beat -->

Rayleigh’s work on vibration and Ritz’s variational approximation method are historical landmarks behind this strategy. They were separate contributions, not a joint paper. The mathematical question is how to turn a chosen search space into a useful eigenproblem, and how to check what its answers mean in the original space. We will give that chosen search space a name, while keeping the hoped-for exact answer separate.

## RrSpace: Trial means chosen for the search

Why: The name describes a role, not an accuracy theorem.
Recall: A subspace contains every linear combination of its vectors.

The directions just described generate all the vectors we will consider. Choose candidate directions and allow all their linear combinations. That set is the trial subspace. We can choose it before knowing any exact eigenvectors. It might be a line, a plane, or a much higher-dimensional space. Trial does not mean random, and it does not mean already proved close to the answer.

<!-- beat -->

Three claims must be kept separate. A trial space is where we search. An invariant space is one that A maps into itself. A wanted spectral space is the exact eigenspace or cluster we are trying to approximate. A chosen trial space need not be invariant or close to the wanted space. Those are questions to investigate after the choice. To compute within the chosen space, we need coordinates that preserve its lengths and angles.

## RrFrame: Q supplies coordinates in the trial space

Why: We need a way to move between a small vector and its ambient representative.
Recall: Q has orthonormal columns: Q transpose Q equals the small identity.

Give our chosen trial directions orthonormal coordinates. Write the trial space as the range of Q. A small coordinate vector y becomes the ambient vector u equals Q y. Orthonormal columns make this map preserve lengths: the norm of Q y equals the norm of y. Conversely, Q transpose u gives the coordinates of a vector already in the trial space.

<!-- beat -->

For an arbitrary ambient vector v, Q transpose v computes its coefficients against those columns. Lifting those coefficients gives Q Q transpose v, the orthogonal projection onto the trial space. Call that ambient projection P. Q and P are different objects: Q changes the size of the coordinate vector; P maps the ambient space to itself. This projection will let us build a small operator even when A sends trial vectors outside their space.

## RrCompress: Apply A, then project back

Why: A trial vector can leave the search space when A acts on it.
Recall: P equals Q Q transpose; Q transpose Q is the identity.

We have our trial space and its coordinate map Q. The missing ingredient is an operator on the small coordinates. Start with y, lift it to Q y, and apply the original operator A. We reach A Q y. Here is the difficulty: that output can leave the trial space. How can we describe it using only the trial coordinates?

<!-- beat -->

Use the projection we just constructed. Q transpose reads the trial coefficients of A Q y. The complete round trip is Q transpose A Q y. Give this small operator a name: B equals Q transpose A Q. This is the compression. Each factor has a job: lift, apply A, then read the trial coordinates.

<!-- beat -->

Lift the small output back to the full space. Q B y equals P A Q y, the projection of the true output. So we now have a small model, together with a precise description of what it keeps. It discards the perpendicular component. Before solving its eigenproblem, we should check that B retains the directional information we intended to approximate.

## RrQuotient: Why this small matrix is the right one

Why: The compression preserves the original directional measurement on every trial vector.
Recall: For a unit vector u, the Rayleigh quotient is u transpose A u.

To check our compression, choose one trial direction. Write it as u equals Q y, with y a unit vector. Because Q preserves lengths, u is unit too. The original Rayleigh quotient in that direction is u transpose A u. What number does the small matrix assign to the same direction?

<!-- beat -->

Substitute Q y for u. The quotient becomes y transpose Q transpose A Q y. The middle expression is B, so this is exactly y transpose B y. Every trial direction gets the same quotient in the original and compressed problems. This equality is why the compression represents the restricted search.

<!-- beat -->

B also remains symmetric: transpose its definition and use A transpose equals A. We can therefore solve B as an ordinary symmetric eigenproblem. Its extremal eigenvectors optimize the original Rayleigh quotient among our allowed directions. We are ready to take a small eigenvector and see what it means back in the full space.

## RrSolve: Solve small, then lift

Why: Small eigenvectors describe combinations of the trial directions.
Recall: B y equals theta y is a k-dimensional eigenproblem.

The small model is ready. Solve B y equals theta y, taking y to be unit. Theta is called a Ritz value. It is an eigenvalue of the small matrix we actually solved. We still need to turn its coordinate vector y into an ambient vector.

<!-- beat -->

Lift y using the same map Q. The vector u equals Q y is the Ritz vector. It is a combination of the trial directions, and its length is one. The small equation implies P A u equals theta u: after projecting back into the trial space, the eigenvector equation holds exactly.

<!-- beat -->

The original problem asks for A u itself to equal theta u. Subtract those two vectors and call the difference r, the full eigenpair residual. This is the piece the projected equation did not inspect. To understand that gap between the small and full problems, let us draw it for a trial space that is just a line.

## RrGeometry: The missing component is visible

Why: Compression removes the part of the output perpendicular to the trial line.
Recall: This example uses a one-dimensional trial space.

Keep the same construction, but let the trial space be one line. Take A diagonal with entries one and four. The amber unit vector q spans our chosen line. There is only one trial coordinate, so the small matrix B will be a single number theta.

<!-- beat -->

Apply A to q. The cyan output A q leaves the line. Project it back: the amber vector along the line is theta q, with theta equal to q transpose A q. This is the small model doing exactly what the compression formula promised.

<!-- beat -->

The green arrow completes the trip from theta q to A q. It is r equals A q minus theta q. The right-angle marker shows why the projected equation could be exact while the full equation still had an error. Projection removed precisely this perpendicular component.

<!-- beat -->

Rotate the trial line toward the eigenvector for eigenvalue one. The compression and the green residual change together; the residual shrinks as the line approaches that invariant direction. We have now seen what the discarded output means. With several trial directions, we will collect their discarded outputs in one residual matrix.

## RrExample: A two-dimensional trial space

Why: A small eigenproblem combines candidate directions and reveals different residuals.
Recall: Use the first two coordinate directions as the trial space.

Move from one trial direction to two. Here A is a three by three symmetric matrix, and Q consists of the first two coordinate vectors. The trial space is their plane. Applying our round trip gives the top-left two by two block B. We can solve this small matrix directly.

<!-- beat -->

Its sum direction has Ritz value three. Lift the normalized sum into the ambient space by appending a zero third coordinate. The couplings into that third coordinate cancel, so its full residual is zero. This Ritz vector happens to be an exact eigenvector.

<!-- beat -->

The difference direction has Ritz value one. Its couplings into the third coordinate reinforce rather than cancel, leaving residual square root of two times e three. Thus one direction stays in the plane while another leaves it. A block picture will organize these two kinds of output without depending on the particular numbers in this example.

## RrBlock: The block structure records where the output goes

Why: Adapt coordinates to the trial space and its perpendicular complement.
Recall: Q spans the trial space; Q perpendicular completes an orthonormal basis.

The example separated output inside the trial plane from output perpendicular to it. Do the same for any trial space. Complete Q to an orthonormal basis using Q perpendicular. In these coordinates, the first block column of A describes what happens to an input from the trial space. Its upper block is B, the part retained by compression; its lower block is C, the part that escapes.

<!-- beat -->

The full symmetric matrix has the displayed four blocks, with C transpose opposite C. Our approximation uses only the first block column. Subtract the model output Q B from A Q: the retained B component cancels, leaving Q perpendicular times C. This is the residual matrix R. It collects the perpendicular arrows from all the trial directions.

<!-- beat -->

If C is zero, no trial input produces output outside the space, so the trial space is invariant. Conversely, invariance forces C to be zero. We did not assume this when drawing the blocks. We have found exactly which block measures its failure. We can verify the same conclusion directly from the original formulas, without choosing complementary coordinates.

## RrOrthogonality: Derive residual orthogonality

Why: The defining small model removes every residual component inside the trial space.
Recall: B equals Q transpose A Q, and Q transpose Q equals I.

Let us check the claim suggested by the block picture: every output of R should be perpendicular to the trial space. We know R equals A Q minus Q B, B equals Q transpose A Q, and Q transpose Q equals the identity. To test for a component inside the trial space, apply Q transpose to R.

<!-- beat -->

The first term becomes Q transpose A Q, which is B. The second becomes Q transpose Q B, also B. Their difference is zero. That short cancellation proves Q transpose R equals zero. Every residual column is perpendicular to every trial direction. This is called Galerkin orthogonality.

<!-- beat -->

Equivalently, R equals I minus P, applied to A Q. For a small eigenvector y, the individual residual is R y. This recovers our green arrow without the block coordinates. It also raises a useful question: could a different small model, on this same trial space, remove more of the error?

## RrModel: A trial space and a small model are separate choices

Why: Rayleigh–Ritz makes a particular model choice after the trial space is fixed.
Recall: M is any k by k proposed action on trial coordinates.

Keep Q and the trial space fixed. Suppose we replace the compression B by another small matrix M. The full residual is then A Q minus Q M. We want to know whether changing this model can reduce the perpendicular error we just identified.

<!-- beat -->

Add and subtract Q B. The residual splits into R plus Q times B minus M. The first piece is perpendicular to the trial space; the second lies inside it. Changing M can alter only this second piece. It cannot cancel the perpendicular arrow R.

<!-- beat -->

Apply Pythagoras to each column and add. The squared Frobenius residual is the squared norm of R plus the squared Frobenius norm of B minus M, because Q preserves lengths. It is smallest, uniquely, when M equals B. We have justified the best model for this fixed space. The next question is what the remaining residual tells us about the exact eigenproblem.

## RrQuality: A small residual still needs interpretation

Why: Accuracy of an eigenpair and identification of a wanted spectral target are different questions.
Recall: A is symmetric and the Ritz vector u has unit norm.

We have measured the error left by our best small model. What does its size certify? Take a unit Ritz vector u and its Ritz value theta. For this argument only, expand u in an exact orthonormal eigenbasis of A. We do not need to compute that basis to use the resulting estimate.

<!-- beat -->

In each eigenvector direction, applying A minus theta multiplies the coefficient by lambda j minus theta. Orthogonality gives the displayed sum for the squared residual. The squared coefficients add to one. Therefore, if every exact eigenvalue were farther from theta than the residual norm, that weighted sum would be too large.

<!-- beat -->

Some exact eigenvalue must lie within the residual norm of theta. To identify a specified target, we need more information: the eigenvector for four in our diagonal example has zero residual even if we wanted the eigenvector for one. A gap supplies the additional separation needed for angle control. We also have another way to improve our approximation: enlarge the search space rather than change its small model.

## RrMinmax: What enlarging the trial space guarantees

Why: A larger search space improves extremal variational estimates.
Recall: Compare nested, nonzero trial spaces for the same symmetric matrix.

So far we kept the search space fixed. What changes if we allow more directions? The smallest Ritz value is the minimum Rayleigh quotient over unit vectors in the trial space. It is at least the smallest exact eigenvalue, because we minimize over fewer choices. If we enlarge the trial space, that minimum cannot increase. Dually, the largest Ritz value cannot decrease when the trial space grows.

<!-- beat -->

These are useful directional guarantees: the smallest estimate moves downward toward the global minimum, and the largest moves upward toward the global maximum. They do not say how fast an arbitrary sequence of spaces converges, and they do not establish that a particular space approximates a chosen interior spectral cluster. The min–max lecture develops the broader variational picture. We can now distinguish improving the space from choosing its internal model. That distinction is also built into the general residual notation.

## RrPaper: Translate the residual notation

Why: The general residual framework includes Rayleigh–Ritz as a specific choice.
Recall: The operator under study is written A-hat in the residual theorem.

The construction we followed has a direct translation into the residual theorem. In the Davis–Kahan residual notation, the trial frame is E zero, the proposed small operator is A zero, and R equals A-hat E zero minus E zero A zero. The trial subspace is the range of E zero. In our finite matrix discussion, E zero plays the role of Q. The Rayleigh–Ritz choice is A zero equals E zero adjoint A-hat E zero.

<!-- beat -->

The general residual theorem need not make that choice. For example, a perturbation argument may use an old operator’s invariant subspace and its old small model while studying a new operator. That residual need not be orthogonal to the trial space. For an unbounded operator, the trial vectors must additionally lie in its domain, with the domain and bounded-residual assumptions required by the theorem. Our matrix derivation explains the geometry without removing those analytic requirements. With that translation, we can read a trial residual and ask which small model produced it. Let us collect the entire approximation procedure once more.

## RrSummary: Choose, compress, solve, check

Why: Keep the approximation pipeline and its guarantees distinct.
Recall: Trial space is a search choice; Ritz residual measures the discarded output.

Choose a trial subspace and an orthonormal frame Q. Compress A to B equals Q adjoint A Q. Solve the small eigenproblem, lift each eigenvector, and inspect the full residual. The Ritz residual is perpendicular to the trial space because the projected equation was solved exactly.

<!-- beat -->

The trial space is not assumed invariant, and the compression does not promise that it is a good approximation to our target. It provides a principled small model, a variational interpretation, and an explicit residual. Target identification and spectral separation supply the further information needed for subspace accuracy. We will keep three identities from this route and connect them to the formal statements.

## RrFacts: Three reusable identities

Why: The definitions explain the error decomposition.
Recall: Q is isometric, B is the compression, and R equals A Q minus Q B.

Carry three identities into another proof. Compression is Q adjoint A Q. The Ritz residual satisfies Q adjoint R equals zero. Every other model residual A Q minus Q M equals R plus Q times B minus M. The following Lean cards show accepted Tau Ceti statements for these same identities, in bounded Hilbert-space language. The first identity defines the small model; the second locates its error; the third explains why another model cannot cancel that error.

## RrLean: Lean: the compression

Why: Match the abstract operator definition to the small matrix.
Recall: X in Lean is the isometric trial map Q on the slides.

Start with the compression identity we have just collected. Lean writes continuous linear maps between a trial-coordinate space F and an ambient space E. X is our frame Q, and adjoint X is Q adjoint. A dot compression X is the small operator B. The first identity simply unfolds that definition. This definition works without a self-adjointness assumption; self-adjointness matters when we interpret the resulting small problem as a Hermitian eigenproblem. Having named the small model in Lean, we can state where its residual lies.

## RrLeanOrthogonal: Lean: residual orthogonality

Why: The isometry hypothesis makes the projected residual vanish.
Recall: A dot sylvester M X means A X minus X M.

Use that same compression in the full residual. The second card inserts the compression as the small model. A dot sylvester of that model and X is our Ritz residual R. Composing on the left with adjoint X gives zero. The hypothesis h X says X is an isometry, which supplies Q adjoint Q equals the identity. The accepted theorem proves exactly the cancellation shown earlier. The last card explains what happens if we replace this model by another one.

## RrLeanSplit: Lean: split any model residual

Why: Changing the small model adds a component inside the trial space.
Recall: M is an arbitrary small bounded operator.

The last card writes every model residual as the Ritz residual plus X composed with the difference between the compression and M. This algebraic splitting itself needs no symmetry or isometry assumption. With the isometry hypothesis from the previous card, the two output pieces are orthogonal. That is the starting point of the Pythagoras and fixed-space minimality argument. That completes the mathematical thread. The remaining bonus explains how to carry out the same steps numerically, before the study questions.

## RrComputation: Computing a Rayleigh–Ritz step

Why: This bonus concerns implementation, after the exact mathematical construction.
Recall: The working basis must be orthonormal for the formulas used above.

Follow the same choose, compress, solve, and check sequence in an implementation. An implementation normally obtains Q by a stable orthogonalization such as QR, applies A to its columns, forms Q adjoint A Q, and solves the small Hermitian eigenproblem. With sparse matrices or an operator interface, applying A can avoid storing a dense matrix. If the original basis V is not orthonormal, the corresponding reduced problem uses the Gram matrix V adjoint V: V adjoint A V y equals theta V adjoint V y. Do not silently replace that Gram matrix by the identity. Check orthogonality numerically and recompute the full residual for lifted Ritz vectors. Krylov and subspace iteration methods mainly differ in how they construct and improve the trial spaces. The study questions now ask what this procedure guarantees, and what remains a choice of search space.
