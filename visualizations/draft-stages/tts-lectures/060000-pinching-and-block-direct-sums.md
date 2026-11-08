# 060000 — Pinching and block direct sums

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `016000` orthogonal block operators; `054000` Ky Fan sums; `058000` unitarily invariant norms; `059000` padding. **Next:** form inequalities and singular values.

<!-- BEGIN SPOKEN LECTURE -->

# Remove the coupling between two orthogonal subspaces

Suppose a linear operator acts on a space split into two mutually orthogonal parts. In block coordinates, the operator has four pieces. Two blocks describe what happens within each part. The other two describe how the operator sends vectors from one part into the other.

What happens to the operator's size if we erase those two cross terms?

For an arbitrary norm on a list of matrix entries, there is no universal answer. But for every unitarily invariant norm, the block-diagonal part cannot be larger than the original operator. This operation is called pinching.

Today we will derive pinching from an elementary reflection identity, prove the norm inequality using only convexity and unitary invariance, and connect the result to the singular values of block direct sums. These ideas appear repeatedly when perturbation proofs separate a difficult operator into pieces adapted to spectral subspaces.

## The four blocks of an operator

Let H be an inner-product space and let P be the orthogonal projection onto a subspace M. Its orthogonal complement has projection I minus P.

Write H as the orthogonal direct sum of M and its complement. Relative to this splitting, a linear operator A has four blocks.

The upper-left block maps M back into M. The lower-right block maps the orthogonal complement back into itself. The upper-right block sends vectors from the complement into M. The lower-left block sends vectors from M into the complement.

The block-diagonal part of A retains only the first and fourth blocks. In coordinate-free language it is P A P plus the complementary projection on both sides of A.

We will call that operator the pinch of A by P. Notice that it is not generally equal to A. It deletes the coupling between the two subspaces.

## Build the reflection

From P, construct a new operator J by taking twice P and subtracting the identity. On M, J acts as plus one. On the orthogonal complement, J acts as minus one.

Therefore J is self-adjoint and its square is the identity. In particular, it is unitary: it preserves all lengths and has itself as inverse.

Consider J A J. In block form, the diagonal blocks are unchanged. Each off-diagonal block changes sign, because it crosses exactly one component on which J acts as minus one.

So A plus J A J has the original diagonal blocks twice and the off-diagonal blocks zero.

Divide by two. We obtain a simple identity: the pinch of A is the average of A and J A J.

This identity is the entire geometric mechanism behind pinching. We did not need eigenvalues or singular vectors to derive it.

## Prove the contraction inequality

Let the symbol N denote any unitarily invariant matrix norm on the appropriate square matrix space.

Because J is unitary, N of J A J equals N of A.

Now use the triangle inequality on the average. The norm of one half of A plus J A J is at most one half the norm of A plus one half the norm of J A J.

The two terms on the right are equal. Their average equals N of A.

Thus the pinched operator has norm no larger than the original operator.

The proof applies simultaneously to operator norm, Frobenius norm, nuclear norm, every Schatten p norm, and every Ky Fan norm. It does not require the blocks to be self-adjoint. It does not require the off-diagonal blocks to be adjoints of one another.

We can also isolate just the off-diagonal part. It is one half of A minus J A J. Because multiplying an operator by minus one does not change its norm, the same triangle argument proves that the off-diagonal part has norm no larger than A.

Do not misread these inequalities as saying the two parts have norms adding to the original norm. The triangle inequality gives an upper bound on the whole by the sum of the parts, but there is generally no equality.

## Work through a two-by-two example

Consider the real matrix with first row three, four, and second row four, three. Split the space into the first coordinate axis and the second.

The pinch erases the two fours, leaving the diagonal matrix with three in both positions.

The original symmetric matrix has eigenvalues seven and negative one. Its singular values are seven and one. The pinched matrix has singular values three and three.

The operator norm drops from seven to three. The nuclear norm drops from eight to six. The Frobenius norm drops from the square root of fifty to the square root of eighteen.

The Ky Fan one norm is just the operator norm, so it also decreases. The Ky Fan two norm is the nuclear norm for this two-by-two example, and decreases as well.

But there is a subtler pattern: the leading singular value of the pinch is smaller, yet its second singular value is larger. Three is greater than one. So pinching does not imply a coordinatewise singular-value inequality.

Instead it implies a comparison of partial sums. That is exactly the distinction between weak majorization and entrywise domination defined by comparing leading partial sums.

## Pinching as a Ky Fan statement

Apply the norm inequality separately to every Ky Fan prefix norm. For each positive integer k, the sum of the k largest singular values of the pinched operator is at most the corresponding sum for A.

This says that the entire singular-value list of the pinch is weakly majorized by that of A.

Conversely, once we know these Ky Fan inequalities, the weak-majorization theorem tells us that every symmetric gauge must also decrease. Therefore pinching illustrates both directions of our general strategy: the reflection proof gives the whole family of inequalities, and the Ky Fan comparisons encode their common numerical content.

This proof extends to finite Hilbert-space block decompositions with more than two parts. We may pinch one splitting, then another, repeatedly removing cross terms. Each step is a contraction, so the final block-diagonal operator has no greater invariant norm than the initial operator.

## Direct sums have a different rule

Now suppose A acts on one space and B acts on another. Form an operator that applies A to the first component and B to the second, with no coupling between them. This is a block direct sum.

The Gram operator of the direct sum is the direct sum of the two Gram operators. Hence the positive singular values of the new operator are precisely the singular values of A together with those of B, rearranged in decreasing order, with zeros added as necessary.

For the operator norm, this means the direct-sum norm is the larger of the two component operator norms.

For Frobenius norm, the squared norm of the direct sum equals the sum of the two squared component norms. We can see this by adding the squared singular values block by block.

For nuclear norm, the direct-sum norm equals the sum of the two nuclear norms. The singular values are simply concatenated and added.

For a finite Schatten p norm, the p-th power of the new norm equals the sum of the p-th powers of the component norms.

These formulas are specific to the gauge. A general unitarily invariant norm does not necessarily make direct-sum norms additive. For example, two one-by-one identity blocks each have operator norm one. Their direct sum is the two-by-two identity, whose operator norm is still one, not two.

## Where the block arguments will be used

In the Davis–Kahan setting, we often have an operator represented relative to a target spectral subspace and its complement. The diagonal blocks describe the action within the chosen pieces. The off-diagonal blocks carry the defect of invariance.

Pinching gives a controlled way to delete cross terms when comparing singular-value measurements. Block direct sums let us reassemble estimates that have already been established on independent orthogonal pieces.

The two operations should not be conflated. Pinching starts with one operator and deletes couplings. Taking a direct sum builds a new operator from separate pieces whose singular values combine in a precise way.

## What to reconstruct

Using the decomposition into M and its orthogonal complement, write J as plus identity on the first block and minus identity on the second. Multiply the block matrices to verify that the diagonal part is the average of A and J A J.

Derive the invariant-norm contraction from the triangle inequality. Then check the singular values seven and one for our two-by-two example, and explain why the second singular value can increase even though every Ky Fan prefix sum decreases.

Finally, derive the operator, Frobenius, and nuclear direct-sum formulas from the union of singular-value lists.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

With \(P=P^*=P^2\), put \(J=2P-I\), so \(J=J^*=J^{-1}\). The pinching map is
\[
\mathcal P(A)=PAP+(I-P)A(I-P)=\tfrac12(A+JAJ),
\]
and every unitarily invariant norm satisfies \(\|\mathcal P(A)\|_\Phi\le\|A\|_\Phi\). The singular values of \(A\oplus B\) are the multiset union of the two lists, with zeros padded. For \(1\le p<\infty\), \(\|A\oplus B\|_{S_p}^p=\|A\|_{S_p}^p+\|B\|_{S_p}^p\), while \(\|A\oplus B\|_{op}=\max(\|A\|_{op},\|B\|_{op})\).

**Lean bridge (verbatim excerpts).**

`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Pinching.lean`:

```lean
theorem kyFanApproximationGauge_diagBlock_le_complex
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] (A : E →L[ℂ] E) (k : ℕ) :
    ((U.diagBlock A).kyFanGauge k : ℝ) ≤
      (A.kyFanGauge k : ℝ) := by
```

This is the complex Hilbert-space Ky Fan approximation-gauge pinching inequality. The theorem works with a submodule that has an orthogonal projection and does not directly state every general invariant norm as a separate conclusion.

`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/BlockSum.lean`:

```lean
theorem operatorAbs_orthogonalBlockSum
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂) :
    LinearMap.operatorAbs ((A.prodMap B).withLpMap 2) =
      ((A.operatorAbs).prodMap (B.operatorAbs)).withLpMap 2 := by
```

This operator-modulus identity underpins the assertion that singular values of a block sum concatenate.

`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/FiniteBlocks.lean`:

```lean
theorem schatten_rpow_of_orthogonal_blocks
    (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤) (A : E →ₗ[𝕜] E)
    (hinv : ∀ i, ∀ x ∈ W i, A x ∈ W i)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten 𝕜 E E p A ^ p.toReal =
      ∑ i, UnitarilyInvariantSeminorm.schatten 𝕜 (W i) (W i) p
        (A.restrict (hinv i)) ^ p.toReal := by
```

The displayed theorem is a finite orthogonal invariant decomposition with a complete span. It is an exact power-sum statement for finite Schatten p, not a general additive formula for all invariant norms.

**Reconstruction exercise:** Reprove the principal displayed identity from the spoken lecture, then identify the exact source/target types and extra assumptions in each displayed Lean declaration.
