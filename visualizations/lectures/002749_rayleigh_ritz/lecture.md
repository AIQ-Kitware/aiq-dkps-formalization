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

An eigenproblem asks for directions that A only scales. The large array represents the original operator. Suppose that applying this operator is possible, but solving its entire eigenproblem would be expensive. We choose a smaller collection of directions and search among their combinations. The amber array represents the small model we would like to construct.

<!-- beat -->

The challenge is deciding what that small model should preserve. We also need to check its answers back in the original space. Rayleigh’s work on vibration and Ritz’s variational approximation method are historical landmarks behind this strategy. We will follow the construction from the chosen directions to the error that remains. First, what exactly have we chosen when we choose a trial space?

## RrSpace: Trial means chosen for the search

Why: The name describes a role, not an accuracy theorem.
Recall: A subspace contains every linear combination of its vectors.

The amber sheet represents a trial plane, spanned by q one and q two. These two arrows are the directions we chose. The moving arrow shows their linear combinations: change the two coefficients and we obtain another allowed vector in the same plane. Trial space means the entire collection of these combinations, not just the original two arrows. Higher-dimensional trial spaces play the same role.

<!-- beat -->

This choice tells us where to search. It does not yet say what A does to those vectors, or whether this plane is close to the wanted exact spectral space. Invariance would mean that applying A always stays inside the plane. Accuracy would require a comparison with our exact target. We will test those properties later. To compute within our chosen plane, we first need coordinates for its vectors.

## RrFrame: Q supplies coordinates in the trial space

Why: We need a way to move between a small vector and its ambient representative.
Recall: Q has orthonormal columns: Q transpose Q equals the small identity.

The left circle contains unit vectors in the two small coordinates. Q places each one in the trial plane on the right. The moving dots represent the same vector before and after this embedding. Both have norm one; the right circle looks flattened only because the plane is drawn in perspective. Orthonormal columns make Q preserve lengths. The small coordinates y and the ambient vector u equals Q y are two descriptions of that one trial vector.

<!-- beat -->

Now take a cyan vector v outside the plane. Q transpose reads its coefficients along the trial directions. The result is the left-hand coordinate vector; lifting it again gives the point underneath v in the plane. This is the orthogonal projection P equals Q Q transpose. We have two useful operations: Q lifts small coordinates, and Q transpose reads trial coordinates from any ambient vector. Those are exactly the operations needed to build the small model.

## RrCompress: Apply A, then project back

Why: A trial vector can leave the search space when A acts on it.
Recall: P equals Q Q transpose; Q transpose Q is the identity.

Keep the same trial plane. Start with one trial input, the amber basis vector q one. Applying A gives the cyan arrow, which leaves the plane. We want a small operator that can describe this action using only the two trial coordinates. The difficulty is now visible: the full output contains a component those coordinates cannot represent.

<!-- beat -->

Read the trial coordinates of that output with Q transpose. For a general coordinate vector y, the complete trip is Q transpose A Q y. Define B to be Q transpose A Q. Each factor has a concrete job: lift the input, apply the original operator, then read the coefficients along the trial directions. This operation is called compression.

<!-- beat -->

Lift the small answer back into the plane. The amber output Q B y is P A Q y, the projection of the true output. The green arrow completes the trip from that amber output to the cyan one. Compression has retained the in-plane component and discarded this perpendicular component. Before trusting the model’s eigenproblem, we should ask what numerical information it preserves along each allowed direction.

## RrQuotient: Why this small matrix is the right one

Why: The compression preserves the original directional measurement on every trial vector.
Recall: For a unit vector u, the Rayleigh quotient is u transpose A u.

Use the same example. Its compression B has diagonal entries two and off-diagonal entries one. Turn a unit coordinate vector around the trial plane. The graph records its Rayleigh quotient, the scalar measurement u transpose A u. The value varies with direction: it reaches three in the sum direction and one in the difference direction. Does the small matrix assign the same values?

<!-- beat -->

Substitute u equals Q y into the original quotient. It becomes y transpose Q transpose A Q y, which is exactly y transpose B y. So there are not two competing curves here. The full and compressed calculations give the same curve on every trial direction. This identity is the reason the small matrix represents our restricted search.

<!-- beat -->

Symmetry is preserved too, because transposing B replaces A by A transpose, and A is symmetric. We can solve B with an ordinary symmetric eigensolver. Its extremal eigenvectors identify the highest and lowest points of the quotient curve within our chosen space. Let us lift one of those small eigenvectors and check what it solves in the full problem.

## RrSolve: Solve small, then lift

Why: Small eigenvectors describe combinations of the trial directions.
Recall: B y equals theta y is a k-dimensional eigenproblem.

The difference direction, with coordinates one and minus one divided by square root of two, is an eigenvector of the small matrix B with eigenvalue one. This is a small eigenproblem we have solved exactly. Its eigenvalue is called a Ritz value, written theta; here theta equals one. We will lift this particular direction so that the relation between the small and full equations remains visible.

<!-- beat -->

Apply Q to those coordinates. The amber arrow u lies in the trial plane and is called a Ritz vector. Its norm is one. The projected equation is P A u equals one times u. In this example the projected output lands exactly back on the input arrow: the small model says this direction is only scaled, with scale one.

<!-- beat -->

Now apply the full operator. The cyan output leaves the plane. The green difference is r equals A u minus theta u, the full eigenpair residual. We have solved the projected equation and can see the part it did not test. To describe this error for the whole trial space, we need more than one residual vector: we need a residual matrix.

## RrGeometry: Collect the discarded outputs in R

Why: The residual matrix collects the perpendicular output for every trial input.
Recall: R acts on trial coordinates; its columns come from the trial basis inputs.

The green residual just came from one trial input. Build the same comparison for every input by defining R equals A Q minus Q B. R takes trial coordinates and returns the discarded part of the full output. We can understand this matrix column by column, using the two basis directions that define our trial plane.

<!-- beat -->

For the first basis coordinate, the green arrow points upward, normal to the plane. Its ambient coordinates are zero, zero, one. Those entries form the first column of R. They say exactly where this particular output escaped from the small model.

<!-- beat -->

For the second basis coordinate, the green arrow points the other way. Its coordinates are zero, zero, minus one, giving the second column of R. The columns are not arbitrary error labels; each is the discarded output for one coordinate direction. Linear combinations of inputs produce the same linear combinations of these columns.

<!-- beat -->

Choose equal positive input coordinates. The two normal components cancel and the green arrow disappears. For the difference direction they reinforce, as in the previous slide. Thus R acts on every trial input. When y is a small eigenvector, its individual eigenpair residual is R y. We can now inspect the matrix entries behind these pictures and see why one Ritz vector is exact while the other is not.

## RrExample: A two-dimensional trial space

Why: A small eigenproblem combines candidate directions and reveals different residuals.
Recall: Use the first two coordinate directions as the trial space.

Here is the symmetric operator we have been drawing. The amber top-left block is the compression to the first two coordinate directions. The green entries couple that plane to its normal direction. They are responsible for the upward and downward arrows that formed the columns of R.

<!-- beat -->

The small matrix’s sum direction has Ritz value three. After lifting, its two contributions to the normal component cancel. The cyan true output and amber retained output coincide in the plane, so r plus is zero. This Ritz vector happens to be an exact eigenvector of A.

<!-- beat -->

The difference direction has Ritz value one. Subtracting the two input contributions instead reinforces the normal component, leaving square root of two times e three as the residual. One exact direction therefore does not make the entire plane invariant. The next block diagram collects the retained and escaping outputs we have already drawn, so that the same reasoning works without depending on these particular entries.

## RrBlock: Blocks collect the two outputs

Why: Adapt coordinates to the trial space and its perpendicular complement.
Recall: Q spans the trial space; Q perpendicular completes an orthonormal basis.

Complete the trial frame Q with coordinates Q perpendicular for the normal space. In this basis, an input from the trial space has only its first block of coordinates nonzero. The first block column of A therefore tells the whole story for such inputs. B gives their retained output in the amber plane; C gives their output in the perpendicular directions.

<!-- beat -->

Look at the two green arrows. The upward coefficient is one and the downward coefficient is minus one. Together they form C, the row shown here. Multiplying by Q perpendicular places those coordinates back into the ambient space, so R equals Q perpendicular C. The same escaping output is described by C in normal coordinates and by R in ambient coordinates. Symmetry supplies C transpose in the opposite block of the full matrix.

<!-- beat -->

For the entire trial space to be invariant, every one of these perpendicular outputs would have to vanish. That is exactly C equals zero. Our example has C nonzero, although its sum direction cancels the two columns. The block structure has now earned its meaning: it separates where the output goes. Let us verify this directly from the original formulas, without needing complementary coordinates.

## RrOrthogonality: Derive residual orthogonality

Why: The defining small model removes every residual component inside the trial space.
Recall: B equals Q transpose A Q, and Q transpose Q equals I.

The green arrows in the picture lie normal to the trial plane. To express that algebraically, apply Q transpose to R: this reads the trial coordinates of each residual. The picture predicts zero. We know R equals A Q minus Q B and B equals Q transpose A Q. These two definitions are enough to check the prediction.

<!-- beat -->

Q transpose A Q is B. In the second term, Q transpose Q is the identity, so Q transpose Q B is also B. Subtracting gives zero. This proves Q transpose R equals zero, usually called Galerkin orthogonality. It says that every residual column has zero component in every trial direction.

<!-- beat -->

The projection formula expresses the same fact as R equals I minus P, applied to A Q. For a small eigenvector y, the full residual is R y. We have located the error entirely outside the search space. Could changing the small matrix B, while keeping the same search space, cancel any of that error?

## RrModel: A trial space and a small model are separate choices

Why: Rayleigh–Ritz makes a particular model choice after the trial space is fixed.
Recall: M is any k by k proposed action on trial coordinates.

Keep the trial space and frame Q fixed, but propose another small model M. Its full residual A Q minus Q M is shown by the cyan arrow for one trial input. We want to know whether the freedom to change M can improve on the compression. Add and subtract the compression’s output Q B to find out.

<!-- beat -->

The residual splits into the green component R and the amber component Q times B minus M. Green lies perpendicular to the trial space; amber lies inside it. The right-angle triangle shows why changing the internal model cannot cancel the escaping component. It can only add or remove an in-plane discrepancy.

<!-- beat -->

Apply Pythagoras to each column and add the squared lengths. The squared Frobenius residual is the squared norm of R plus the squared Frobenius norm of B minus M. Q preserves lengths, which removes it from the second term. The unique minimum occurs at M equals B. This chooses the best model for the space already selected. What can the remaining residual tell us about the exact eigenproblem?

## RrQuality: Locate an exact eigenvalue

Why: Accuracy of an eigenpair and identification of a wanted spectral target are different questions.
Recall: A is symmetric and the Ritz vector u has unit norm.

The white dots are the exact eigenvalues of our three by three example. The amber marker is the Ritz value one. We will use an exact eigenbasis only to reason about the error; the computation does not require finding that basis. Expand the unit Ritz vector in it, with coefficients c j. Their squared magnitudes add to one.

<!-- beat -->

Applying A minus theta multiplies each coefficient by lambda j minus theta. Orthogonality gives the displayed sum for the squared residual. Consequently, if every exact eigenvalue were farther from theta than the residual norm, this weighted sum would be too large.

<!-- beat -->

The green interval has radius equal to that residual norm, square root of two here. At least one exact eigenvalue must lie inside. This tells us proximity to some eigenvalue; identifying a wanted spectral target needs additional separation information. Our other Ritz value, three, is exact but would still be the wrong choice if we wanted the smallest eigenvalue. We can also improve the approximation by enlarging the search space itself.

## RrMinmax: What enlarging the trial space guarantees

Why: A larger search space improves extremal variational estimates.
Recall: Compare nested, nonzero trial spaces for the same symmetric matrix.

Keep the same operator and enlarge the allowed directions: first a coordinate line, then the trial plane, then the full space. The smallest Ritz value minimizes the original Rayleigh quotient over each chosen set of unit vectors. Enlarging the set cannot raise this minimum, because all the old candidates remain available.

<!-- beat -->

In our example the minimum moves from two to one, then to three minus square root of six, the exact smallest eigenvalue. The number-line marker follows that change. The largest Ritz value moves in the opposite direction when the space grows. These are monotone extremal bounds, not a rate of convergence for arbitrary spaces. We can now distinguish improving the search space from optimizing its internal model, which is precisely the distinction used in the general residual notation.

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
