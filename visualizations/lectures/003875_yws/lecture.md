# Yu–Wang–Samworth: a population-gap perturbation theorem

Authored by GPT-6.1-Sol. Scope and exact source/Lean anchors are in `sources.md`.
The core proves Theorem 2; the rectangular section explains the corrected
ambient-spectrum version of Theorem 3.

## YsTitle: A population-gap perturbation theorem

Why: Understand the mathematics behind the YWS statistical variant.
Recall: The main concept is subspace error controlled by a population gap.

A population-gap perturbation theorem.

## YsSetup: The setting: one matrix, one estimate, one block

Why: Fix the objects before comparing their eigenspaces.
Recall: All matrices in the main theorem are real symmetric.

Yu, Wang, and Samworth ask how accurately an estimated matrix recovers a selected eigenspace of a population matrix. Their paper appeared as a preprint in 2014 and in Biometrika in 2015. We will call the population matrix A, the estimate A hat, and their difference H. These are real symmetric p by p matrices. The result we study is deterministic: the estimate may come from random data, but no probability assumption is needed to apply the inequality once the two matrices are given.

List the eigenvalues of both matrices in decreasing order. Choose positions r through s, and write d for the number of positions. V contains orthonormal population eigenvectors at those positions, and V hat contains estimated eigenvectors at the same ordered positions. A frame means this matrix of orthonormal columns. Our goal is to compare the spaces spanned by these two frames, then compare the frames after an allowed change of basis. The notation is local to this lecture; the paper calls A sigma, A hat sigma hat, and H E.

## YsMotivation: Why a population gap?

Why: A theorem should separate model information from estimation error.
Recall: Population quantities belong to the underlying model; sample quantities come from data.

A common statistical version of Davis–Kahan uses a mixed separation: selected population eigenvalues must be separated from unwanted sample eigenvalues. That can be awkward because the sample eigenvalues are random. One often uses another inequality to show that this random gap is at least a fraction of a population gap on a suitable event. YWS packages the population information directly into the perturbation theorem.

<!-- beat -->

The resulting bound has a denominator involving only population eigenvalues and a numerator measuring the difference between the matrices. Later, a statistical argument can bound that numerator with high probability. These are different jobs. The deterministic theorem converts matrix error into subspace error. Concentration or another statistical argument supplies the matrix error. The theorem does not estimate the population gap for us, and it does not turn an observed sample gap into a guaranteed population gap.

## YsMixedExample: A mixed gap can vanish

Why: A failed certificate need not mean the actual spaces differ.
Recall: The published example selects positions 2 through 4.

The paper gives a revealing diagonal example. The population eigenvalues are fifty, forty, thirty, twenty, and ten. The sample eigenvalues are fifty-four, thirty-seven, thirty-two, twenty-three, and twenty-one. Select positions two through four. The population interval is twenty to forty, and its two exterior boundary gaps are both ten.

<!-- beat -->

The unwanted sample value twenty-one enters the population interval, so the mixed interval separation is zero. The population boundary gap is still ten. In this diagonal example, the selected spaces actually agree, because the same coordinate positions are selected. The mixed-gap certificate nevertheless becomes unusable. YWS gives a valid population-gap inequality here, although its numerical upper bound may be loose. A theorem being applicable and a bound being sharp are distinct questions.

## YsGap: What exactly is the population gap?

Why: Only separation from the exterior of the selected block is needed.
Recall: Eigenvalues are ordered from largest to smallest.

The population gap, which we call g, is the smaller of two boundary differences: the eigenvalue just above the block minus the first eigenvalue in the block, and the last eigenvalue in the block minus the one just below. Each difference separates a selected eigenvalue from the population spectrum outside the block. Internal spacings within the selected block do not enter g. Repeated eigenvalues inside the block are allowed.

<!-- beat -->

For a leading block there is no upper boundary, and for a trailing block there is no lower boundary. Omit the missing side, equivalently assign its gap infinity. We focus on a proper block so at least one boundary exists and g is a finite positive number. If the block is the entire space, the subspace error is zero and two full orthonormal bases can be aligned exactly. Sample eigenvalues may have ties; the theorem does not assume a sample eigengap.

## YsGeometry: Measure the space, not arbitrary basis choices

Why: Principal angles ignore sign changes and rotations within the same space.
Recall: V and V hat have d orthonormal columns.

A basis is not uniquely attached to its space. A vector and its negative span the same line. A rotation among d basis columns preserves the same d-dimensional subspace. So first measure an error that ignores these changes. The singular values of V transpose V hat are cosines of principal angles. The Frobenius sine error is the square root of the sum of the squared sines of these angles.

<!-- beat -->

Complete V to an orthonormal population eigenbasis by adding V perpendicular. Then X equals V perpendicular transpose V hat records the estimated frame in unwanted population coordinates. Its Frobenius norm is exactly the sine error. Each column contributes the squared length lying outside the population space. This identity is our bridge from a geometric question to a matrix calculation. A later step will recover a basis comparison by choosing an orthogonal alignment.

## YsTheorem: Theorem 2: the two conclusions

Why: Keep both the geometry bound and the aligned-frame bound in view.
Recall: The Frobenius norm sums squared entries; the operator norm is the largest stretch.

Here is the main theorem. The Frobenius sine error is at most two divided by g, times the smaller of square root d times the operator norm of H and the Frobenius norm of H. There is also a d by d orthogonal matrix O such that the Frobenius distance from V hat O to the fixed population frame V is at most two square root two divided by g, times the same smaller numerator.

<!-- beat -->

The two numerator choices can differ substantially, so the minimum is useful. There is no assumption that H is smaller than a specified fraction of the gap. If the right side is large, the result may be numerically uninformative but remains valid. The sine error is always at most square root d. The proof explains both the factor two and the extra square root two in the aligned conclusion. We will separate those explanations rather than treat the constants as mysterious decorations.

## YsRoadmap: A proof with two estimates and one conversion

Why: Every next step has a specific job in the final inequality.
Recall: X is the unwanted component; R will be a population residual.

The proof has three tasks. First, find a residual R that is cheap to bound from above using H. Second, show that the population gap forces this residual to be at least g times the unwanted component X. Combining these gives the sine bound. Finally, use principal angles to choose an alignment and convert sine error to frame error.

<!-- beat -->

The key choice is to test the estimated frame against population eigenvalues at the same ordered positions. That may look unusual: V hat is an eigenframe of A hat, not A. But precisely this mismatch produces an error whose unwanted coordinates see only population spectral differences. Our proof will use that observation directly. It does not require a case split into small and large perturbations or a random-gap event.

## YsResidual: Choose a residual with population eigenvalues

Why: The denominator will stay entirely on the population side.
Recall: Lambda contains selected population eigenvalues; Lambda hat contains sample eigenvalues.

Let Lambda be the diagonal matrix of the selected population eigenvalues, and Lambda hat the diagonal matrix of selected sample eigenvalues. Define R as V hat Lambda minus A V hat. This residual is not the usual residual of an approximate eigenframe with its own sample eigenvalues: that residual for A hat is zero. We deliberately compare with population values.

<!-- beat -->

Because A hat V hat equals V hat Lambda hat and A hat equals A plus H, rearrangement gives R equals H V hat minus V hat times Lambda hat minus Lambda. Thus the residual has two sources: applying the perturbation to the estimated frame, and shifting its ordered eigenvalues. The triangle inequality will bound those two sources separately. We keep the same R in the lower-bound argument so that the two estimates can be combined.

## YsOperatorUpper: Upper bound 1: operator norm and Weyl

Why: Control each of the d residual columns.
Recall: An orthonormal frame has d unit columns.

For the first residual term, every column of H V hat has length at most the operator norm of H. Squaring those d column lengths and adding gives a Frobenius norm at most square root d times the operator norm. This is why the block dimension enters the operator-norm branch.

<!-- beat -->

For the second term, multiplication by the orthonormal frame preserves the Frobenius norm of the diagonal coefficient matrix. Weyl’s inequality bounds each ordered eigenvalue shift by the operator norm of H. There are d selected shifts, so their squared sum has square root at most square root d times that norm again. The triangle inequality adds two equal upper bounds, producing the factor two.

## YsFrobeniusUpper: Upper bound 2: Frobenius norm and Hoffman–Wielandt

Why: A second estimate can be better for some perturbations.
Recall: Both eigenvalue lists are sorted in the same decreasing order.

For a different bound, orthonormal compression gives the Frobenius norm of H V hat at most the Frobenius norm of H. For the eigenvalue shifts, the Hoffman–Wielandt inequality for real symmetric matrices bounds the sum of squared shifts over the full ordered spectrum by the squared Frobenius norm of H. Restricting that sum to our block can only decrease it.

<!-- beat -->

The second residual term is therefore also at most the Frobenius norm of H. The triangle inequality gives a residual bound of twice that norm. Since both upper bounds hold at the same time, we may take their minimum. For example, a rank-one perturbation has equal operator and Frobenius norms, so the Frobenius branch avoids the square root d factor when the selected block has several columns. This is a comparison of two valid estimates for one residual, not a choice between two different theorems or two differently defined errors.

## YsBlocks: Why population blocks appear

Why: The spectral theorem supplies the splitting; we are not assuming an algorithm finds it.
Recall: V perpendicular consists of the population eigenvectors outside the selected block.

Now we need the residual lower bound. Choose the full orthonormal eigenbasis of the real symmetric population matrix A. In these coordinates A is block diagonal: Lambda on the selected population space and Lambda one on its orthogonal complement. The zero off-diagonal blocks follow from the eigenvector equations. They are not extra assumptions about the sample matrix.

<!-- beat -->

Write the estimated frame in these coordinates as a top part and a bottom part. The bottom part is X equals V perpendicular transpose V hat. It measures exactly what lies outside the selected population space. We are using a basis that exists by the spectral theorem to prove an inequality. We are not claiming that this population basis or X is observable from data. The final inequality will remove them in favor of H and g.

## YsLowerIdentity: Project the residual onto the unwanted coordinates

Why: Throwing away the wanted part can only decrease a Frobenius norm.
Recall: The unwanted population block is Lambda one.

Multiply the residual equation on the left by V perpendicular transpose. The first term becomes X Lambda. In the second term, the population eigenvector relations give V perpendicular transpose A equals Lambda one V perpendicular transpose. Consequently the unwanted residual is X Lambda minus Lambda one X.

<!-- beat -->

This projection cannot increase the Frobenius norm, so the norm of R is at least the norm of X Lambda minus Lambda one X. This is the same operator-equation structure that appears in Sylvester estimates, but we can see the required Frobenius estimate directly in diagonal coordinates. The selected eigenvalues in Lambda and the unwanted eigenvalues in Lambda one all belong to the population matrix.

## YsEntrywise: The gap multiplies every unwanted entry

Why: A matrix lower bound reduces to scalar inequalities.
Recall: Column j uses a selected population eigenvalue; row i uses an exterior one.

The entry in row i and column j of X Lambda minus Lambda one X is the entry x i j multiplied by the difference between the selected eigenvalue lambda j and the exterior eigenvalue mu i. Because the block is consecutive and g is its exterior boundary gap, every such absolute difference is at least g. This remains true whether the exterior value is above or below the block.

<!-- beat -->

Square the entries and add them. Every multiplier squared is at least g squared, so the residual norm squared is at least g squared times the Frobenius norm squared of X. Taking square roots gives g times the sine error at most the residual norm. This explains why two-sided separation works for this Frobenius argument without pretending that all exterior eigenvalues lie on the same side.

## YsCombine: Combine lower and upper bounds

Why: The unexplained residual disappears from the conclusion.
Recall: The same R occurs in both estimates.

We now have a sandwich. The lower bound says g times the sine error is at most the residual norm. The upper bounds say that residual norm is at most twice the smaller of square root d times the operator norm of H and the Frobenius norm of H. Divide by positive g to obtain the first conclusion of Theorem Two.

<!-- beat -->

Notice what never entered the denominator: the sample eigenvalues. They did appear in the residual identity, but their shifts were bounded from above by perturbation norms. In the lower bound, only population eigenvalue differences occur. This is the mechanism behind the population-gap theorem. It works for any ordered estimated eigenframe at the selected positions, including ties, without an additional small-perturbation hypothesis.

## YsAlignment: Why an orthogonal alignment is necessary

Why: A large column difference may describe only a change of basis.
Recall: Multiplying V hat on the right by O changes its coordinates, not its column space.

We have bounded the subspace error, but sometimes an application compares coordinates or embedding matrices. Directly comparing V hat with V can be misleading. Even if they span exactly the same space, their columns may differ by signs or by an orthogonal change of basis. A sign flip already makes a unit vector differ from its negative by length two while the subspace error is zero.

<!-- beat -->

Allow V hat to be multiplied on the right by a d by d orthogonal matrix O. This keeps its span unchanged and holds the population frame V fixed. The question is now how close the best-aligned sample frame can be to V. The singular value decomposition of V hat transpose V chooses this alignment using the same principal angles that define the sine error.

## YsAlignmentProof: Alignment costs at most an extra square root two

Why: Principal angles connect the basis and subspace conclusions.
Recall: All principal angles lie between zero and a right angle.

Write V hat transpose V as L C Q transpose, where L and Q are orthogonal and C has diagonal entries cosine theta j. Choose O equal to L Q transpose. Expanding the squared Frobenius distance gives two d minus twice the sum of the cosines. Each cosine lies between zero and one, so it is at least its square.

<!-- beat -->

Therefore the squared aligned error is at most two d minus twice the sum of squared cosines, which equals twice the sum of squared sines. Taking square roots gives aligned error at most square root two times the sine error. Combine this with the first theorem conclusion to obtain the constant two square root two. This step is geometric; the earlier factor two came from estimating the residual.

## YsRotationExample: A rotated two-dimensional example

Why: Check the geometric quantities against a concrete matrix pair.
Recall: The leading population eigenvector is the first coordinate direction.

Take A diagonal with entries three and one. Rotate its eigenbasis by theta to obtain A hat, keeping its eigenvalues unchanged. The leading estimated vector is cosine theta, sine theta. The population gap is two. The sine error is sine theta, and after choosing the compatible sign the frame error is two sine of theta over two.

<!-- beat -->

For this example, the residual is the vector zero, two sine theta, so its norm is exactly gap times sine error. The operator norm of H is two sine theta. The theorem’s operator branch gives sine error at most two sine theta. That is valid but not an equality away from zero. The factor lost here comes from the general residual upper bound, not the geometric lower bound. This example illustrates the proof; it does not claim the theorem is optimally sharp for every matrix pair.

## YsRectangular: Rectangular matrices: apply the theorem to a Gram matrix

Why: Singular subspaces become eigenspaces of symmetric matrices.
Recall: Right singular vectors are eigenvectors of B transpose B.

YWS also treats rectangular matrices. To avoid confusing this with the symmetric setting, call them B and B hat, with D their difference. Their right singular vectors are eigenvectors of B transpose B and B hat transpose B hat. The corresponding eigenvalues are squared singular values. This lets us apply the symmetric population-gap theorem to a Gram matrix.

<!-- beat -->

The Gram perturbation expands as B transpose D plus D transpose B plus D transpose D. Its operator norm is at most two times the largest singular value of B plus the operator norm of D, all multiplied by the operator norm of D. Its Frobenius norm has the analogous bound with the Frobenius norm of D as the final factor. Substitution into Theorem Two gives the rectangular estimate. Left singular subspaces use B B transpose instead.

## YsRectangularGap: Keep zero eigenvalues at the rank boundary

Why: The Gram matrix has its full ambient spectrum, including zeros.
Recall: A zero singular value is an actual eigenvalue of the Gram matrix.

Select positions r through s among the positive population singular values, so s is at most the rank of B. The denominator is an exterior gap in squared population singular values. For right singular vectors, the Gram matrix acts on the full input space, so its spectrum includes zeros beyond the rank. If the selected block ends at the last positive singular value and there are further input directions, its lower boundary gap is that last positive singular value squared minus zero. It is not infinity.

<!-- beat -->

The repository records and refutes the printed rank-based infinity convention in Theorem Three and proves the corrected ambient-spectrum version. For this lecture, the displayed rectangular bound uses that corrected gap. This is a source correction to state explicitly, rather than silently teaching a false endpoint convention. The aligned-frame bound again has an extra square root two, and the symmetric proof supplies the reason.

## YsSummary: What the proof has established

Why: Keep the roles of geometry, perturbation, and probability separate.
Recall: The theorem is deterministic and its denominator is population-only.

The main proof chose a residual measured against population eigenvalues, bounded it above using either Weyl or Hoffman–Wielandt, and bounded it below using the unwanted population coordinates. That produced the Frobenius sine bound. An orthogonal alignment converted the subspace bound to a frame bound at the cost of square root two. The rectangular extension applies the same theorem to Gram matrices.

<!-- beat -->

For statistical use, provide a positive population gap and a bound on the perturbation norm. A probability argument can supply the latter, but the theorem itself needs no random assumptions. Internal population multiplicities and sample ties are allowed within the stated ordered-block setup. The next cards repeat the two reusable inequalities beside checked Lean applications. The optional computation slide then explains how to inspect these quantities in an experiment without confusing an observed sample gap with the population assumption.

## YsFacts: Two reusable inequalities

Why: These are the conclusions to carry into another proof.
Recall: N abbreviates the smaller perturbation numerator, before the factor two.

Let N be the smaller of square root d times the operator norm of H and the Frobenius norm of H. For real symmetric matrices, matched ordered blocks, and positive population boundary gap g, the sine error is at most two N over g. There exists an orthogonal alignment whose frame error is at most two square root two N over g. The same V and V hat occur in both statements, and the population frame is held fixed.

## YsLean: Lean companion: the sine bound

Why: The compact code applies the source-facing theorem with all hypotheses.
Recall: Full context and alias definitions are retained in facts.lean.

The first Lean card is an application of theorem two sine theta from the YWS package. Sin error abbreviates the Frobenius sine distance between the spans of V and V hat. Noise abbreviates the same minimum numerator shown on the mathematical card. The context includes real symmetric matrices, ordered eigenvector blocks, the dimension relation, and the positive source population gap. Lean uses zero-based indices; the lecture uses the paper’s one-based indices. The companion source records that translation.

## YsLeanAligned: Lean companion: an actual orthogonal matrix

Why: Existence of an alignment is part of the conclusion, not an extra assumption.
Recall: Aligned error means the Frobenius distance from V hat O to the fixed V.

The second Lean card exhibits a matrix O in the orthogonal group. Aligned error expands to the square root of the sum of squared column differences between V hat O and V. The theorem therefore gives an alignment of the supplied sample frame while keeping the supplied population frame fixed. These are checked applications of the source-facing declarations, not replacement proofs or assumptions that the desired inequalities already hold.

## YsComputation: Computing an experimental check

Why: Numerical work can illustrate the theorem without certifying an unknown population gap.
Recall: This slide is optional; the mathematical proof is already complete.

In an experiment with a known population matrix, use a symmetric eigensolver and sort eigenvalues in decreasing order before selecting matching positions. Compute principal angles from the singular values of V transpose V hat. For an orthogonal alignment, take the singular value decomposition of V hat transpose V and form L Q transpose. Compute both perturbation norms before choosing the smaller numerator. Near zero angles, subtracting squared cosines from one can lose relative accuracy; the unwanted-coordinate matrix V perpendicular transpose V hat offers another way to inspect the sine error. With observed data alone, these computations do not certify the unknown population gap.
