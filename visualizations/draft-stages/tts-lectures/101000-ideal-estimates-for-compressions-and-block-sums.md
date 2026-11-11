# 101000 — Ideal estimates for compressions and block sums

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `054000` Ky Fan sums, `060000` pinching, `097000` Hilbert-space Ky Fan dominance, `098000` symmetric ideals, `100000` modulus invariance. **Next:** `102000` real Hilbert complexification.

<!-- BEGIN SPOKEN LECTURE -->

# What happens to operator size when we cut a matrix into blocks?

Take a two-by-two matrix. Imagine that its first row is three and four, and its second row is one and two.

Suppose we're interested only in what happens when an input points horizontally, and only in the horizontal part of the output. Under those restrictions, the matrix behaves like multiplication by three.

We have thrown away most of the original operation. A natural question is whether this remaining piece could somehow be larger, in a singular-value norm, than the operator it came from.

The answer is no. Compressing an operator between orthogonal subspaces cannot increase a symmetric ideal gauge.

But there's a second question that looks similar and has a different answer. What if we keep several pieces, put them on the diagonal, or assemble independent operators into one big block matrix? To reason correctly about these operations, we'll distinguish three things: selecting a block, averaging away off-diagonal blocks, and forming a direct sum.

## Selecting one block

Return to our matrix with rows three, four and one, two.

Let P project an input onto the horizontal axis. So P keeps its first coordinate and discards its second. Let Q do the same thing to the output.

The composed map Q T P has just one nonzero entry: three in the upper-left position. This is the selected source-to-target block.

Why can't this compression increase an ideal gauge?

Because an orthogonal projection never lengthens a vector. Its operator norm is at most one. An operator ideal is stable under composition by bounded operators: the gauge of A T B is at most the norm of A times the gauge of T times the norm of B.

With A equal to Q and B equal to P, both outside factors have norm at most one. So the compressed gauge is at most the original gauge.

This argument works even if the source and target have different dimensions. And it does more than compare numerical values. If T belongs to a proper operator ideal, the compressed map belongs too.

For example, a trace-class map stays trace class after compression. The same is true for Hilbert–Schmidt operators.

## Four pieces, but no automatic addition rule

Now keep both the horizontal and vertical parts of the source and target. Our matrix has four blocks: three in the upper-left, four in the upper-right, one in the lower-left, and two in the lower-right.

Each individual block is a compression. Each has gauge at most the gauge of the full matrix.

Can we add all four of their gauges and get the gauge of T? Not in general.

For instance, the trace norm of a rank-one matrix with all four entries equal to one is two. But each of its four single-entry blocks has trace norm one. Adding the block trace norms gives four, not two.

Blockwise estimates remain useful, but they don't turn the gauge into a sum over matrix entries.

Let's try a different operation. Keep the two diagonal blocks and discard both off-diagonal blocks. For our running example, the result is the diagonal matrix with entries three and two.

We would like a sharp estimate saying that this diagonal part has gauge no larger than the original matrix. Bounding the two diagonal entries separately and adding would waste a factor. There is a cleaner argument.

## Pinching by reflection and averaging

Imagine reflecting the horizontal and vertical coordinates with opposite signs: keep the horizontal direction as it is and reverse the vertical one.

Apply this reflection to the input side and the output side of our matrix. The diagonal entries stay three and two. The off-diagonal entries change sign, from four and one to negative four and negative one.

Now average the original matrix and this reflected matrix. The off-diagonal entries cancel, and the diagonal entries survive. The average is exactly the diagonal matrix with three and two.

Why does this give a norm estimate? Both reflections are unitary: they preserve all vector lengths. A symmetric ideal gauge is invariant under multiplying by unitaries. So the reflected matrix has exactly the same gauge as the original.

The triangle inequality then tells us that the gauge of their average is at most the average of their gauges. That's just the original gauge.

We've proved the constant-one pinching inequality.

There is a useful difference between the two proofs we've used. A single block is controlled by contractive composition. The sum of the diagonal blocks is controlled by symmetry and averaging. Those are different mechanisms, and recognizing which one applies prevents unnecessary constants.

## Put independent blocks next to each other

Now consider a new construction. Take an operator A with singular values five and one, and an operator B with singular values four and two.

Build a bigger operator that applies A to one input space and B to an orthogonal input space, without mixing the two. This is called their orthogonal direct sum.

Its singular values are the values from both blocks merged into one descending list: five, four, two, one.

Here is why. When we take the adjoint of the direct sum and multiply, the result stays block diagonal. Its diagonal blocks are A adjoint A and B adjoint B. So the eigenvalues that describe squared singular values come from the two blocks independently. We merge them and take square roots.

Let's look at the Ky Fan sums: sums of the largest few singular values.

The first sum is five. The first two sum to nine. The first three sum to eleven. All four sum to twelve.

The two-slot result is worth calculating another way. We could take both slots from A, giving five plus one, or six. We could take one from each, giving five plus four, or nine. Or we could take both from B, giving four plus two, or six. The best allocation gives nine.

For any number of slots, the Ky Fan sum of a direct sum is the maximum over possible allocations between its blocks.

## Why the exact allocation rule is useful

The direct-sum rule immediately explains three familiar but different norms.

For operator norm, we only take the largest singular value, so the direct-sum norm is the larger block norm.

For Hilbert–Schmidt norm, we square all singular values and add them. Consequently, the square of the direct-sum Hilbert–Schmidt norm is the sum of the squares for the two blocks.

For trace norm, we add the singular values directly. So the direct-sum trace norm is the sum of the two trace norms when both operators are trace class.

These combination laws are different. An arbitrary symmetric gauge does not have to follow any single one of them.

The Ky Fan allocation formula survives on general Hilbert spaces when singular values are expressed through approximation numbers. That extension uses the appropriate min–max theory; it does not require the operator to possess a finite eigenbasis.

## Dominance and the membership question

Suppose A has every Ky Fan prefix no larger than C, and B has every prefix no larger than D.

Take any allocation of slots between A and B. The sum from those blocks is no larger than the corresponding allocation between C and D. Maximizing over allocations preserves the inequality.

So the direct sum of A and B has every Ky Fan prefix no larger than the direct sum of C and D.

Can we now conclude an inequality for every operator ideal gauge? Only if the ideal has the Ky Fan dominance property, and the dominating operator belongs to the ideal. Under those hypotheses, the dominated operator also belongs, and its gauge is no larger.

In infinite dimensions, comparing each finite prefix does not automatically guarantee membership in any chosen ideal. The dominance property supplies that implication.

The three constructions are now distinct. Selecting a block uses projections and contractions. Keeping diagonal blocks uses reflection averaging. Combining independent maps uses a merge of singular-value data. Knowing which operation we're performing tells us which proof and which constant are justified.

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

### Worked example: compression, pinching, direct sum

For \(T=\begin{pmatrix}3&4\\1&2\end{pmatrix}\), let \(P=Q=\operatorname{diag}(1,0)\) and \(J=2P-I\). Then
\[
QTP=\begin{pmatrix}3&0\\0&0\end{pmatrix},\quad
J T J=\begin{pmatrix}3&-4\\-1&2\end{pmatrix},\quad
\tfrac12(T+JTJ)=\operatorname{diag}(3,2).
\]
The rectangular pinching is an average of two unitarily equivalent operators. The trace norm of the pinching is \(5\), while \(\|T\|_1=\sqrt{\|T\|_F^2+2|\det T|}=\sqrt{34}\).

For \(A=\operatorname{diag}(5,1)\) and \(B=\operatorname{diag}(4,2)\), the singular values of \(A\oplus B\) are \((5,4,2,1)\), yielding prefixes \((5,9,11,12)\). For the two-slot prefix, \(\max\{K_2(A),K_1(A)+K_1(B),K_2(B)\}=\max\{6,9,6\}=9\).

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
