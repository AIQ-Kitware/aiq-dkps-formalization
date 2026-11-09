# 070000 — Hilbert–Schmidt Sylvester group estimates

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `057000` Schatten and Frobenius norms; `062000–069000` Sylvester equations and spectral gap estimates. **Next:** `071000` Sylvester identities for compressed blocks.

<!-- BEGIN SPOKEN LECTURE -->

# Turning operators into vectors

Consider A X minus X B equals C with self-adjoint coefficients. If every spectral value of A is at least delta away from every spectral value of B, the Hilbert–Schmidt norm obeys the sharp estimate delta times the norm of X at most the norm of C, even when the spectral sets interlace. The same constant-one statement can fail in operator norm. The difference comes from how the two norms combine matrix coefficients.

Today we will explain the mechanism behind this difference. We will treat an operator as a vector in a larger Hilbert space, turn left and right multiplication into a single self-adjoint generator, and measure the Sylvester equation by the spectral gap of that generator. Our route begins with ordinary rectangular matrices and ends with the same idea on infinite-dimensional Hilbert spaces.

## A Hilbert space whose vectors are matrices

Consider a two-by-three complex matrix Z. Its Hilbert–Schmidt norm is the square root of the sum of the squared absolute values of its six entries. Now introduce an inner product on matrices: multiply the conjugate of each entry of Z by the matching entry of W, and sum. Its induced norm is exactly the Frobenius norm.

A matrix can therefore be a point in a six-dimensional complex inner-product space. The original matrices act on vectors in two different spaces, but we can study all rectangular maps together as a third space.

This matters because orthogonality is now available between distinct matrix blocks. If a matrix is split into four submatrices by orthogonal row and column projections, the square of its Frobenius norm is the sum of the four block energies. The operator norm does not have this property. Two blocks can interfere when they act on the same input directions.

To see it numerically, take Z with entries one, two, three, and four in a two-by-two array. Its squared Hilbert–Schmidt norm is one plus four plus nine plus sixteen, namely thirty. Cutting it into its four individual entries leaves the same total energy of thirty. There is no corresponding sum-of-squares identity for the largest singular value.

## The Sylvester operator becomes one linear map

Let A be a self-adjoint operator on the output space and B a self-adjoint operator on the input space. Define S of Z to be A times Z minus Z times B.

For now, assume the spaces are finite-dimensional. The Hilbert–Schmidt inner product shows that S is itself self-adjoint. To check this, move A across the inner product using its adjoint, which equals A. Do the same for B. The two minus signs match. Consequently, the inner product of S of Z with W equals the inner product of Z with S of W.

Choose orthonormal eigenvectors for A and B. From one left eigenvector u and one right eigenvector v, construct the rank-one map taking an input x to u times the inner product of v with x. These rank-one maps form an orthonormal basis of the matrix Hilbert space.

If A sends u to a times u and B sends v to b times v, the Sylvester operator sends this rank-one map to a minus b times itself. Thus the spectrum of the Sylvester operator consists of all left-right eigenvalue differences. We have built the familiar entrywise denominators into the spectrum of a single self-adjoint operator.

## The square-norm inequality

Suppose every such difference has absolute value at least delta, with delta positive. Expand Z in our rank-one basis. Applying S multiplies every coefficient by a number of absolute value at least delta.

Square its Hilbert–Schmidt norm. Each squared coefficient is multiplied by at least delta squared. Add the inequalities. Taking a square root proves that the Hilbert–Schmidt norm of S of Z is at least delta times the Hilbert–Schmidt norm of Z.

If S of X equals C, this is precisely delta times the Hilbert–Schmidt norm of X at most that of C. There is no factor counting how many entries the matrices have, and no need to put the spectra in any particular order.

Take A diagonal with entries negative two and three, and B diagonal with entries negative one and two. All four differences have absolute value one or greater. So delta equals one. Whatever matrix C we choose, the unique solution X has Hilbert–Schmidt norm no greater than that of C. In contrast, the operator-norm argument cannot simply square the individual entries and add.

## The time-dependent group

There is a second perspective that survives without an eigenvector basis. Exponentiate the self-adjoint operators with imaginary time. For each real time t, define a transformation of Z by multiplying on the left by the exponential of i times t times A, and on the right by the exponential of negative i times t times B.

Both exponential factors are unitary. Consequently, this transformation preserves the Hilbert–Schmidt inner product. The family of transformations is a one-parameter unitary group: time zero acts as the identity, and composing two times adds them.

Differentiate the trajectory at time zero. Its derivative is i times A Z minus Z B. In other words, the self-adjoint Sylvester map S is the generator after removing the factor i. We now have a way to study the Sylvester equation through spectral theory of one unitary group acting on a Hilbert space of operators.

For bounded A and B, differentiation holds in the Hilbert–Schmidt norm. For unbounded self-adjoint generators it becomes a statement on an appropriate domain. That domain is part of the theorem, not a detail to ignore.

## What changes in infinite dimensions

Let the original input and output spaces have countably infinite orthonormal bases. A bounded map Z need not be Hilbert–Schmidt: the identity on an infinite-dimensional space has infinitely many columns of length one, so the sum of squared column lengths diverges.

The Hilbert–Schmidt maps form their own complete Hilbert space. We may measure a map by summing squared column lengths in any orthonormal basis; the answer is independent of the basis.

Left and right multiplication by bounded operators preserve this class. In particular, unitary multiplication preserves its norm. So the same Sylvester group acts by unitaries on the Hilbert space of Hilbert–Schmidt maps.

For self-adjoint A and B with pairwise spectral separation, the associated Sylvester generator has no spectral values near zero. A spectral gap for that generator gives the same lower bound as in the finite matrix calculation. Applied to a Hilbert–Schmidt right-hand side, the inverse produces a Hilbert–Schmidt solution with constant one.

There is a further conclusion beyond the scalar inequality. Suppose X is already known as a bounded solution, but we know only that C has finite Hilbert–Schmidt energy. The theorem establishes that X is Hilbert–Schmidt as well, then proves the bound. Membership of the solution in the smaller operator ideal is itself a conclusion.

## Recovering the gap without eigenvectors

How can we prove the gap if neither A nor B has an eigenbasis? Replace individual eigenspaces by narrow spectral bands. Divide the spectra into small measurable pieces, and cut an operator on the left and right with the corresponding spectral projections.

On one block, A is close to multiplication by a chosen scalar a, and B is close to multiplication by a chosen scalar b. Hence the Sylvester operator is close to multiplication by a minus b. If all possible spectral differences have magnitude at least delta, the scalar part is large compared with sufficiently narrow correction terms.

Each block has its own Hilbert–Schmidt energy. Orthogonality of spectral projections makes the total squared energy the sum of those block energies. Let the band widths tend to zero. The lower bound for the full Sylvester generator emerges from all the blockwise lower bounds together.

This is the step at which the Hilbert-space structure of operators becomes essential. We can reassemble squared norms because distinct spectral blocks are orthogonal. The proof also explains why an operator-norm claim cannot be imported unchanged: operator norm has no comparable orthogonal energy sum.

## Turning Sylvester estimates into angle estimates

A subspace perturbation theorem does not initially present us with an arbitrary Sylvester equation. Instead, it presents us with spectral projections for two operators. We must discover which cross-projection block is the unknown X, what the two compressed generators are, and why the perturbation appears as the right-hand side.

This estimate converts a residual bound into a bound on the angle between spectral subspaces.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For finite Hilbert spaces, equip rectangular maps with
\[
\langle Z,W\rangle_{HS}=\operatorname{tr}(Z^*W),\qquad
\mathscr S(Z)=AZ-ZB.
\]
For self-adjoint \(A,B\), the induced \(\mathscr S\) is self-adjoint; on rank-one eigenblocks \(u_i v_j^*\) it has eigenvalue \(a_i-b_j\). Hence, under \(\operatorname{dist}(\sigma(A),\sigma(B))\ge\delta>0\),
\[
\|\mathscr S Z\|_{HS}^2=\sum_{i,j}|a_i-b_j|^2|z_{ij}|^2
\ge\delta^2\|Z\|_{HS}^2.
\]
For infinite-dimensional Hilbert spaces, the spectral-block and unitary-group construction replaces the finite eigenbasis. The source theorem also proves Hilbert–Schmidt membership of a bounded solution when the defect has finite energy.

**Lean bridge (verified source excerpts).**

`DavisKahan/Sources/DavisKahan1970/Sylvester/HilbertSchmidtEstimate.lean` — `hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap` (exact source declaration header):

```lean
theorem hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    {X C : F →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C)
    (hC : approximationNumberEnergy C ≠ ⊤) :
    approximationNumberEnergy X ≠ ⊤ ∧
      δ * ContinuousLinearMap.hilbertSchmidtNorm X ≤ ContinuousLinearMap.hilbertSchmidtNorm C :=
```

The hypotheses require complex Hilbert spaces, self-adjoint partial operators, a positive pairwise spectral gap, an exact Sylvester equation, and finite defect approximation-number energy. The conclusion includes both solution ideal membership and the sharp square-norm estimate.

`ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidt/Block.lean` — `tsum_enorm_sq_blockFun` (exact source declaration header):

```lean
theorem tsum_enorm_sq_blockFun {ι' : Type*} (b : HilbertBasis ι 𝕜 F)
    (P : ι' → (E →L[𝕜] E)) (Q : ι' → (F →L[𝕜] F))
    (hP : ∀ v : E, ∑' i, ‖P i v‖ₑ ^ 2 = ‖v‖ₑ ^ 2)
    (hQ : ∀ v : F, ∑' j, ‖(Q j).adjoint v‖ₑ ^ 2 = ‖v‖ₑ ^ 2)
    (f : lp (fun _ : ι => E) 2) :
    ∑' p : ι' × ι', ‖blockFun b (P p.1) (Q p.2) f‖ₑ ^ 2 = ‖f‖ₑ ^ 2 := by
```

This is the orthogonal block-energy reassembly on the ell-two column model, subject to norm-splitting hypotheses for the two projection families.
