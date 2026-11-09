# 122000 — Direct-sum norm comparison

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `054000–056000` Ky Fan sums and majorization; `060000` block direct sums. **Next:** `123000` pinching through an involution.

<!-- BEGIN SPOKEN LECTURE -->

# Direct-sum norm comparison

An estimate for one corner of a block matrix is often the easy part of a perturbation proof. A full angle between subspaces has two complementary corners. How can we combine bounds for the two corners without losing a constant or miscounting singular values?

Davis and Kahan answer this with Lemma six point one. Its basic operation is an orthogonal direct sum. When the two summands act on orthogonal initial spaces and have orthogonal output spaces, their singular values merge into a single ordered list. That list admits a precise Ky Fan comparison.

We will prove the finite-dimensional formula directly, then explain the weak-majorization argument, the converse under matching singular values, and the operator-ideal qualifications in Hilbert space.

## Begin with ordinary diagonal matrices

Take a matrix A with singular values five and two, and a matrix B with singular values four and one. Form their block direct sum. Its nonzero singular values are five, four, two, and one, in decreasing order.

The first Ky Fan sum is five. The second is nine. The third is eleven. The fourth is twelve.

The point is that the direct sum has a combined singular-value list, not the termwise sum of two lists. In particular, the second Ky Fan sum is not the second Ky Fan sum of A plus the second Ky Fan sum of B: that would give seven plus five, or twelve, while the correct second prefix is nine.

To get the first two singular values of the direct sum, we choose how many to take from each block. We might take two from A, none from B, or one from each, or none from A and two from B. The largest sum among those choices is nine.

## Prove the exact prefix formula

Let the singular values of A decrease as a one, a two, and so on. Let those of B decrease as b one, b two, and so on. Include trailing zeros after the rank if needed.

For a fixed positive integer k, the sum of the k largest singular values of their direct sum is the maximum, over all splits of k into i plus j, of the sum of the i largest a values and the sum of the j largest b values.

Why is this formula exact? Every choice of k entries from the merged list takes some number i from the first block and j from the second. For that split, the largest possible selected sum uses the first i values of A and the first j values of B. Conversely, those leading entries are a valid selection from the union, so their sum never exceeds the largest k-entry sum of the union.

Taking the maximum over splits proves both inequalities. This is the Ky Fan direct-sum formula.

The same proof works in finite dimensions when one block is rectangular. Singular values depend on the map, not on whether its matrix is square. Adding zero dimensions for the direct sum does not alter the nonzero singular-value list.

## Derive the forward comparison

Suppose every Ky Fan prefix of A is at most the corresponding prefix of C. Suppose also every Ky Fan prefix of B is at most the corresponding prefix of D.

For every split k equal to i plus j, the sum of the first i singular values of A and the first j of B is at most the analogous sum for C and D. Taking the maximum over all splits preserves the inequality.

Thus every Ky Fan prefix of A direct sum B is at most the corresponding prefix of C direct sum D.

This is exactly a weak-majorization statement for the merged singular-value sequences. It is stronger than a comparison for one selected Schatten norm. It says that every leading partial sum is controlled.

By the symmetric-gauge dominance principles established earlier, the weak-majorization conclusion yields a bound in every applicable unitarily invariant norm. In an infinite-dimensional ideal, it can also imply membership, provided the chosen ideal has the required dominance property and the comparison operator belongs to the ideal.

## Why orthogonality matters

Consider two operators whose ranges overlap and whose domains overlap. Their sum may have cancellations or reinforcing interference. The singular values of the sum need not be the merged lists of their individual singular values.

For the direct-sum formula we need the operator to be block diagonal after suitable orthogonal coordinate changes. More precisely, the first block must act on an initial subspace orthogonal to the second block's initial subspace, and their images must lie in orthogonal final subspaces.

Under those conditions, the Gram operator of the sum is block diagonal in the initial-space coordinates. Its positive square root therefore has the two block moduli on the diagonal. The union of singular values follows directly.

In the Davis–Kahan setting, projection blocks have exactly this structure. One block maps the source subspace into the target subspace. Its complementary partner maps the orthogonal source complement into the orthogonal target complement. Their sum is isometrically equivalent to a true block direct sum.

One can describe a cross-block map either by compressing between the actual subspaces or by inserting the corresponding ambient projections. These are operators with different source and target spaces. Their nonzero singular values agree by an explicit isometric identification; they should not be equated as typed operators.

## The converse requires a symmetry

Can we infer separate bounds on A from a Ky Fan bound for A direct sum B? Not in general. The second block might carry the entire improvement or entire loss, making the combined comparison uninformative about the first block.

There is an important exception. Suppose A and B have identical singular-value sequences, and C and D also have identical singular-value sequences. Then the merged singular values of A direct sum B consist of each singular value of A repeated twice. The same holds for C direct sum D.

Therefore the sum of the first two k singular values of A direct sum B is exactly twice the sum of the first k singular values of A. This can be checked from the merged list, or from the prefix formula by showing that a balanced split maximizes the sum of two decreasing-prefix functions.

If all Ky Fan sums of the direct sum on the left are at most those of the direct sum on the right, apply the inequality at even index two k and divide by two. We recover the Ky Fan bound for A versus C.

That is the converse direction in Lemma six point one. Its matching-singular-value hypothesis is essential; without it, the even-prefix identity is false.

## A concrete converse example

Let A have singular values three and one, and let B have the same list. Their direct sum has singular values three, three, one, one. At k equal to one, the Ky Fan prefix of A is three, and the Ky Fan prefix at two for the direct sum is six.

Let C and D each have singular values four and two. Their direct sum has singular values four, four, two, two. The first two entries sum to eight, twice the first Ky Fan sum of C.

The inequality six at most eight recovers three at most four. At even index four, we obtain eight at most twelve, recovering the full singular-value sum four at most six.

The example is simple, but the algebra survives in arbitrary dimension because it depends only on decreasing singular-value sequences.

## Why this appears in subspace perturbation theory

Let P and Q be orthogonal projections. An ambient sine operator can be assembled from complementary cross maps. One cross map measures the part of vectors in P that lies outside Q; the other measures the reverse direction from P perpendicular.

A spectral Sylvester argument often estimates each cross map against a corresponding projected perturbation. Lemma six point one combines the two inequalities into a comparison for the ambient block sum, preserving all Ky Fan prefixes.

The second lemma in this pair then shows that the corresponding perturbation blocks, taken together, have no larger unitarily invariant norm than the original perturbation. Together they let us pass from directed estimates to ambient estimates without blindly doubling the right-hand side.

## Infinity and ideal membership

For a compact operator in infinite-dimensional Hilbert space, singular values form a sequence tending to zero. The direct-sum reasoning remains valid through finite Ky Fan prefixes. No infinite sum is required to establish a fixed prefix inequality.

But a symmetric ideal norm may be finite only on a proper class of compact operators. To claim an ideal estimate, show that the right direct sum lies in the ideal and invoke the ideal's dominance property to place the left direct sum there as well.

The lemma may be stated by controlling every Ky Fan prefix, or by quantifying over an appropriate family of normalized unitarily invariant norms. The latter statement must also specify membership in each norm's domain. The domain condition cannot be omitted.

## The proof to remember

The entire argument has three steps. Orthogonal blocks yield the union of their singular-value lists. The k-th Ky Fan prefix of that union is the maximum of the sums over all splits of k. Componentwise weak majorization controls every one of those splits and therefore the maximum.

Under matching singular-value lists, even prefixes of the direct sum are twice the prefixes of a single block, giving the converse.


<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For rectangular maps `A,B` between orthogonal input/output summands, write `K_k(A)=Σ_{i=1}^k s_i(A)`. Then

\[K_k(A\oplus B)=\max_{0\le i\le k}\bigl(K_i(A)+K_{k-i}(B)\bigr).\]

If `K_i(A)≤K_i(C)` and `K_i(B)≤K_i(D)` at every `i`, the formula implies weak majorization of `A⊕B` by `C⊕D`. Under `s(A)=s(B)` and `s(C)=s(D)`, `K_{2k}(A⊕B)=2K_k(A)` and similarly for `C,D`; hence the converse. The source formalization explicitly tracks `SameSingularValues` across heterogeneous rectangular and ambient projection blocks.

### Exact Lean declaration excerpts

`DavisKahan/Sources/DavisKahan1970/SineTheta/Lemma61.lean` — `projectionBlock_same_compression` (exact declaration header; proof body omitted):

```lean
theorem projectionBlock_same_compression
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    ContinuousLinearMap.SameSingularValues
      (projectionBlock Ω Γ K) (blockCompression Ω Γ K) := by
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/Lemma61.lean` — `lemma61_all_kyFan` (exact declaration header; proof body omitted):

```lean
theorem lemma61_all_kyFan
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[𝕜] E)
    (h₀ : ∀ k,
      ((projectionBlock Ω Γ K).kyFanGauge k : ℝ) ≤
        ((projectionBlock Ω Γ L).kyFanGauge k : ℝ))
    (h₁ : ∀ k,
      ((projectionBlock Ωᗮ Γᗮ Ktilde).kyFanGauge k : ℝ) ≤
        ((projectionBlock Ωᗮ Γᗮ Ltilde).kyFanGauge k : ℝ)) :
    ∀ k,
      ((projectionBlock Ω Γ K +
            projectionBlock Ωᗮ Γᗮ Ktilde).kyFanGauge k : ℝ) ≤
        ((projectionBlock Ω Γ L +
            projectionBlock Ωᗮ Γᗮ Ltilde).kyFanGauge k : ℝ) := by
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/Lemma61.lean` — `lemma61_converse` (exact declaration header; proof body omitted):

```lean
theorem lemma61_converse
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[𝕜] E)
    (hK : ContinuousLinearMap.SameSingularValues
      (projectionBlock Ω Γ K)
      (projectionBlock Ωᗮ Γᗮ Ktilde))
    (hL : ContinuousLinearMap.SameSingularValues
      (projectionBlock Ω Γ L)
      (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hsum : ∀ k,
      ((projectionBlock Ω Γ K +
            projectionBlock Ωᗮ Γᗮ Ktilde).kyFanGauge k : ℝ) ≤
        ((projectionBlock Ω Γ L +
            projectionBlock Ωᗮ Γᗮ Ltilde).kyFanGauge k : ℝ)) :
    ∀ k,
      ((projectionBlock Ω Γ K).kyFanGauge k : ℝ) ≤
        ((projectionBlock Ω Γ L).kyFanGauge k : ℝ) := by
```

**Mapping.** `projectionBlock_same_compression` identifies singular values of an ambient projected map with those of its rectangular compression. `lemma61_all_kyFan` combines two **all-prefix** inequalities, not merely one fixed norm bound. `lemma61_converse` additionally assumes `SameSingularValues` for the paired blocks on each side; the even-prefix argument is the reason.

