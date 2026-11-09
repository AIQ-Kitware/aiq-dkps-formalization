# 101000 — Ideal estimates for compressions and block sums

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `054000` Ky Fan sums, `060000` pinching, `097000` Hilbert-space Ky Fan dominance, `098000` symmetric ideals, `100000` modulus invariance. **Next:** `102000` real Hilbert complexification.

<!-- BEGIN SPOKEN LECTURE -->

# Cutting an operator into pieces without losing its norm estimates

Suppose a bounded operator maps one Hilbert space into another, and suppose its symmetric ideal gauge is finite. We want to look at the operator only on selected source and target subspaces. Can we guarantee that the resulting block still belongs to the same ideal? And if several such blocks are put together, which inequalities survive?

These questions will matter for subspace perturbation. The sine of an angle will appear as a rectangular block of a projection or of a coordinate map. We need to know that passing from a full operator to such a block does not introduce a larger ideal gauge.

We will prove that contraction on either side never increases the gauge, distinguish that operation from addition of blocks, and then derive the exact behavior of Ky Fan prefixes under orthogonal direct sums.

## Begin with source and target projections

Let T map a Hilbert space E into a Hilbert space F. Let P be an orthogonal projection on E, and Q an orthogonal projection on F.

The map Q T P first discards the source component outside P, then applies T, then discards the output component outside Q. Think of it as the upper-left rectangle in a block matrix whose rows refer to target subspaces and whose columns refer to source subspaces.

Orthogonal projections are contractions. Their operator norms are at most one. The defining ideal inequality therefore gives the gauge of Q T P at most the gauge of T.

Here is the proof in two moves. First, composing T with P on the right cannot increase its gauge. Second, composing that result with Q on the left cannot increase it either. By transitivity, the block is no larger in ideal gauge than the original operator.

The source and target spaces do not need to have equal dimensions. The argument uses legal compositions and norms of the factors. It does not require a square matrix.

There is also an important membership assertion. If T belongs to the ideal, then Q T P belongs to the ideal. For a trace-class operator, every compression is trace class. For a Hilbert–Schmidt operator, every compression is Hilbert–Schmidt. The same conclusion holds for every operator ideal with the composition property.

A number alone would not express this. In a general ideal, the gauge is only finite on its carrier. Proving that the compressed map belongs is part of the theorem, not a technical afterthought.

## Cutting all four corners

Decompose the input into the range of P and its orthogonal complement. Decompose the output using Q and its complement. Then T is the sum of four maps: Q T P, Q T times one minus P, one minus Q times T P, and one minus Q times T times one minus P.

Each map has gauge at most the gauge of T. But do not add those four inequalities and conclude that the gauge of T is the sum of the block gauges. The triangle inequality gives one direction. It does not assert additivity, and cancellation or overlap can make the sum much larger.

A more useful construction retains just the two diagonal blocks. Define D to be Q T P plus one minus Q times T times one minus P. We call this rectangular diagonal pinching relative to the two orthogonal decompositions.

Why should the gauge of D be no larger than the gauge of T? We could bound the two pieces separately and get twice the gauge, but that loses the sharp constant.

Instead define a source reflection that acts as plus one on the range of P and minus one on its orthogonal complement. Define the analogous target reflection using Q. Both reflections are unitary: each is its own inverse and preserves lengths.

Compose T on the left with the target reflection and on the right with the source reflection. This changes the signs of the two off-diagonal blocks, while leaving the diagonal blocks unchanged. Average this reflected operator with T. The off-diagonal pieces cancel, leaving exactly D.

A symmetric ideal gauge is unchanged by unitary factors and obeys the triangle inequality. Thus the gauge of the average is at most the average of two copies of the gauge of T. This proves the constant-one pinching inequality.

The same averaging argument applies to a finite decomposition into several orthogonal blocks, using a suitable family of sign changes or phase rotations. The two-block version already contains the method.

## Orthogonal sums are a different operation

Now take two independent maps, A from E zero to F zero, and B from E one to F one. Their orthogonal direct sum sends the pair x zero, x one to A x zero, B x one.

This operator does not discard off-diagonal pieces of an existing map. It puts two maps next to each other on orthogonal input and output spaces.

In finite dimensions, the singular values of the direct sum are exactly the two singular-value lists merged into one descending list. To see why, compute its Gram operator. The adjoint of the direct sum times the direct sum is block diagonal, with A adjoint A in the first block and B adjoint B in the second. Each block contributes its positive eigenvalues. Taking square roots produces the merged singular values.

Consider A with singular values five and one, and B with singular values four and two. The direct sum has singular values five, four, two, one. Its first Ky Fan sum is five; its second is nine; its third is eleven; its fourth is twelve.

The second Ky Fan sum can be calculated without first merging the entire lists. Allocate two slots between the blocks. Taking two from A gives six. Taking one from each gives five plus four, or nine. Taking two from B gives six. Choose the largest allocation. The answer is nine.

In general, the first k singular values of the direct sum have a total equal to the maximum, over all ways of allocating k slots, of the first r singular values of A plus the first k minus r singular values of B.

This formula also works for approximation-number Ky Fan prefixes on Hilbert spaces. Proving that extension requires the min–max and finite-dimensional localization arguments developed earlier. We cannot simply appeal to an infinite list of eigenvectors when the blocks are arbitrary bounded operators.

## What different norms do with direct sums

The exact merge rule explains several familiar formulas.

For operator norm, the norm of the direct sum is the larger of the norms of A and B. For Hilbert–Schmidt norm, the square of the direct-sum norm is the sum of the squares of the two Hilbert–Schmidt norms. For trace norm, the direct-sum norm is the sum of the two trace norms, provided both maps belong to trace class.

These are three different combination laws. None should be treated as the general rule for an arbitrary symmetric ideal gauge.

The Ky Fan prefix formula is more fundamental: it records the full singular-value distribution, from which many norm comparisons can be derived using dominance properties.

## Dominance persists under adding blocks

Suppose every Ky Fan prefix of A is at most the corresponding prefix of C. Also suppose every Ky Fan prefix of B is at most the corresponding prefix of D.

For each possible allocation of k slots, add the two corresponding inequalities. The allocation sum for A and B is at most the allocation sum for C and D. Taking the maximum over all allocations preserves the inequality.

Therefore every Ky Fan prefix of the direct sum of A and B is at most that of the direct sum of C and D.

If a symmetric ideal has Ky Fan dominance, and the larger direct sum belongs to the ideal, then the smaller direct sum belongs too, with a gauge no larger. That final step uses the ideal's dominance hypothesis. It does not follow merely from the definition of a symmetric gauge.

This distinction keeps our arguments legal in infinite dimensions. A statement about a finite number of singular values is one ingredient. A statement about membership in a possibly proper subset of bounded maps is another.

## Why the distinction will recur

We now have three tools. A compression is bounded by the whole operator through contractive composition. A diagonal pinching is bounded by the whole operator through reflection averaging. An orthogonal direct sum has a Ky Fan prefix determined by the maximum over allocations between the blocks.

In a perturbation proof, we will cut a residual into coordinates associated with a trial subspace and an exact spectral complement. Contractive factors will control its ideal size. Direct-sum formulas will reassemble estimates when several spectral pieces must be treated separately.

The critical habit is to specify which operation we are performing. Cutting a block, averaging away off-diagonal terms, and adjoining independent blocks are mathematically different constructions. Their estimates are related, but their proofs are not interchangeable.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For orthogonal projections `P` on `E` and `Q` on `F`, the ideal-composition inequality gives `gauge(Q ∘ T ∘ P) ≤ gauge(T)` and preserves the carrier. The rectangular pinching identity is

\[
QTP+(I-Q)T(I-P)=\tfrac12(T+U_QTU_P),\qquad U_Q=2Q-I,\quad U_P=2P-I.
\]

Both reflections are unitary, so the symmetric ideal triangle and invariance laws yield the sharp bound. For the orthogonal direct sum, the exact prefix formula is

\[
K_k(A\oplus B)=\max_{0\le r\le k}\bigl(K_r(A)+K_{k-r}(B)\bigr).
\]

### Actual Lean source declarations

`ForTauCeti/Analysis/OperatorIdeal/Family/BlockSum.lean` — `gauge_blockSum_le` (exact declaration header; proof omitted):

```lean
theorem gauge_blockSum_le {T : E →L[𝕜] F} {P₁ P₂ : E →L[𝕜] E} {Q₁ Q₂ : F →L[𝕜] F}
    (hP₁ : ‖P₁‖ ≤ 1) (hP₂ : ‖P₂‖ ≤ 1) (hQ₁ : ‖Q₁‖ ≤ 1) (hQ₂ : ‖Q₂‖ ≤ 1)
    (hsplit : Q₁ ∘L T ∘L P₁ + Q₂ ∘L T ∘L P₂ = T) :
    max (N.gauge (Q₁ ∘L T ∘L P₁)) (N.gauge (Q₂ ∘L T ∘L P₂)) ≤ N.gauge T ∧
      N.gauge T ≤ N.gauge (Q₁ ∘L T ∘L P₁) + N.gauge (Q₂ ∘L T ∘L P₂) := by
```

`DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean` — `kyFanApproximationGauge_continuousOrthogonalBlockSum` (exact declaration header; proof omitted):

```lean
theorem kyFanApproximationGauge_continuousOrthogonalBlockSum
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    (k : ℕ) (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) :
    ((continuousOrthogonalBlockSum A B).kyFanGauge k : ℝ) =
      splitKyFanGauge k A B := by
```

`DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean` — `kyFanApproximationGauge_blockSum_le` (exact declaration header; proof omitted):

```lean
theorem kyFanApproximationGauge_blockSum_le
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    {A C : E₀ →L[𝕜] F₀} {B D : E₁ →L[𝕜] F₁}
    (hA : ∀ k, (A.kyFanGauge k : ℝ) ≤ (C.kyFanGauge k : ℝ))
    (hB : ∀ k, (B.kyFanGauge k : ℝ) ≤ (D.kyFanGauge k : ℝ)) :
    ∀ k, ((continuousOrthogonalBlockSum A B).kyFanGauge k : ℝ) ≤
      ((continuousOrthogonalBlockSum C D).kyFanGauge k : ℝ) := by
```

**Type and hypothesis map.** `gauge_blockSum_le` assumes four contractive factors and an exact two-block reconstruction, and gives both a maximum lower bound and a sum upper bound. The two Ky Fan statements concern `ContinuousLinearMap` block sums between possibly different Hilbert spaces, without assuming a finite singular-vector basis. Their outputs are finite-prefix comparisons, not automatic membership in every symmetric ideal.

These Lean snippets are copied exactly from the supplied DKPS repository snapshot. The narration is an independent mathematical derivation; this appendix does not claim that the narrated text was compiled in Lean. Foundational results currently in `ForTauCeti` may have been developed in DKPS before upstreaming.
