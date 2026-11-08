# 097000 — Ky Fan dominance in Hilbert space

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `054000` Ky Fan sums, `055000` weak majorization, `056000` convex descent, `096000` approximation numbers. **Next:** `098000` symmetric operator ideals and membership.

<!-- BEGIN SPOKEN LECTURE -->

# Comparing operators one prefix at a time

For a finite matrix, the sum of its first k singular values is its k-th Ky Fan norm. We proved that comparisons of all such sums can control many other unitarily invariant norms.

We now have an approximation-number sequence for every bounded operator between Hilbert spaces. That makes it possible to transplant the same idea to an infinite-dimensional setting. But we must be careful: finite prefix sums are always well-defined, while an infinite sum or ideal norm may be infinite.

Today we will construct the Ky Fan approximation gauges, prove their elementary bounds, and formulate exactly what additional dominance principle is needed to infer membership in a symmetric operator ideal.

## Finite prefixes in an infinite space

Let a one of T, a two of T, and so forth denote the approximation numbers defined as the distance to operators of lower rank. Define K sub k of T to be the sum of the first k approximation numbers, for any positive integer k. Set K sub zero equal to zero.

Although there may be infinitely many singular directions, each fixed K sub k is a finite sum. Every approximation number is bounded above by the operator norm of T, so K sub k is at most k times that norm.

If T is compact, we may interpret these terms as the largest k singular values, with zeros inserted when the operator has finite rank. If T is not compact, the definition still works; for the identity on infinite-dimensional ell two, K sub k equals k.

The first prefix, K sub one, is exactly the operator norm. Later prefixes measure how much leading size remains after the strongest direction has been accounted for.

## The finite-rank picture returns

Suppose T is compact and positive, with eigenvalues five, two, one, and then zero. For k equal to two, K sub two equals seven. For k equal to three, K sub three equals eight.

The finite spectral theorem and the min–max principle give another description: K sub k is the maximum of sums of k suitable diagonal contributions when k orthonormal input vectors and corresponding output directions are chosen to align with the largest singular directions. In finite dimensions, we proved this by the singular-value decomposition and an orthonormal-frame variational principle.

For compact Hilbert-space operators, finite-rank truncations approximate T in operator norm. Each finite truncation has the familiar variational formula. A fixed prefix K sub k changes by at most k times the operator-norm change in T, so we may pass to the limit.

The important point is that a finite prefix asks about only finitely many directions, even if the ambient Hilbert space is infinite-dimensional.

## Prefix sums obey a triangle inequality

Let S and T be bounded maps with the same source and target. We want K sub k of S plus T at most K sub k of S plus K sub k of T.

In finite dimensions the claim follows from the Ky Fan variational principle. For bounded operators on Hilbert space, finite-rank restrictions and approximation-number inequalities supply the extension, provided the limiting restrictions are justified.

We can understand the finite-rank proof. Choose orthonormal source vectors and matching orthonormal target vectors that nearly realize the leading k-value for S plus T. Pair the sum with those vectors. Split it into an S contribution and a T contribution. Each contribution is bounded by its own Ky Fan k-value. Taking the supremum gives the desired inequality.

Thus, for fixed k, K sub k is a norm on operators, provided the source and target spaces have sufficient dimensions and one handles the zero-dimensional convention appropriately. Even without that extra formulation, it is a finite, subadditive gauge that dominates the operator norm for k at least one.

## Weak majorization between operators

Say T is weakly dominated by S in approximation-number prefixes if K sub k of T is at most K sub k of S for every positive integer k.

This relation compares the cumulative size of singular directions, not the values one by one. For example, compare the finite lists three, one, zero with two, two, zero. Both have total four. The first has a larger leading singular value, so the list two, two, zero is weakly dominated by three, one, zero. The reverse comparison fails at the first prefix.

Do not replace weak prefix domination by coordinatewise domination. The first relation is weaker and is the one naturally preserved by averaging and pinching.

Also, domination is relative to a chosen operator pair. It does not say that an arbitrary bounded operator has a finite trace norm. We can compare every finite prefix of the identity with something else while its infinite nuclear sum remains infinite.

## From prefixes to other gauges

In the finite-dimensional majorization lectures, we proved that a symmetric convex gauge respects weak majorization. A key step was to describe a more balanced vector as a succession of transfers and coordinate reductions.

In infinite dimensions we can first apply that result to a finite initial segment. If an ideal norm is obtained as the supremum or an appropriate limit of such finite symmetric gauges, the finite inequalities can be passed to the limit—provided the norm has the required lower-semicontinuity or completeness property.

This leads to the Ky Fan dominance principle for a symmetric ideal: if S belongs to that ideal, and every approximation prefix of T is no larger than the matching prefix of S, then T also belongs and its ideal gauge is no larger than that of S.

I am stating this as an additional property of the ideal. The formal development calls it Ky Fan dominance. It should not be silently assigned to every possible norm or every arbitrary class of operators without checking its assumptions.

## Why membership is part of the theorem

Consider the Schatten two class, also called the Hilbert–Schmidt class. Its norm is the square root of the sum of squared singular values.

If the singular-value list of S is square-summable and the approximation-number prefixes of T are weakly dominated by those of S, majorization and monotone passage to the limit give square-summability for T and the norm inequality.

The result has two parts. First, T is in the Hilbert–Schmidt class. Second, its Hilbert–Schmidt norm is bounded by the norm of S. The second statement has no finite real meaning before the first is established.

For comparison, take the diagonal operator with entries one divided by n. Its singular values have finite square sum but divergent ordinary sum. Hence it is Hilbert–Schmidt and not trace class. The prefix sums of its singular values exist for every k, but grow without bound. Finite prefixes by themselves cannot certify nuclear membership.

## Strong approximation does not supply ideal convergence

Suppose P sub N are projections onto the first N coordinates of ell two. Then P sub N converges strongly to the identity. But each P sub N has finite rank, and its trace norm equals N. Their ideal norms diverge. They cannot converge to the identity in trace norm, because the identity does not belong to the trace class.

This example warns us not to treat strong operator convergence as convergence in a symmetric ideal gauge. Ideal membership and ideal-norm convergence need their own proofs.

We now have the comparison tool needed for the main Davis–Kahan program: control every leading singular-value sum of a displacement or residual, then transfer that control to a chosen symmetric norm, but only within a class where the required domination theorem applies.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let a_j(T) be approximation numbers indexed from one. The finite Ky Fan gauge is K_k(T) = sum from j=1 through k of a_j(T). For every k, K_k(T) is finite even when T is not compact. The weak prefix preorder is K_k(T) ≤ K_k(S) for all k. An ideal with the Ky Fan dominance property transfers membership S in ideal to T in ideal and yields gauge(T) ≤ gauge(S). The dominance property is an explicit hypothesis in the formalization, not an automatic statement about every conceivable operator norm.

### Actual Lean source declarations

`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean` — `kyFanGaugeReal_comp_eq_of_leftInverse` (declaration header, proof omitted):

```lean
theorem kyFanGaugeReal_comp_eq_of_leftInverse {G : Type x}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {ι : F →L[𝕜] G} {π : G →L[𝕜] F} (hπι : Function.LeftInverse π ι)
    (hι : ‖ι‖ ≤ 1) (hπ : ‖π‖ ≤ 1) (T : E →L[𝕜] F) (k : ℕ) :
    ((ι ∘L T).kyFanGauge k : ℝ) = (T.kyFanGauge k : ℝ) :=
```

`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean` — `kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax` (declaration header, proof omitted):

```lean
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    (hlb : TauCeti.HasMinMaxLowerBound 𝕜 E₀ F₀)
    {ι : Type w} {P : ι → E₀ →L[𝕜] E₀} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E₀))
    (k : ℕ) (K : E₀ →L[𝕜] F₀) :
    Tendsto
      (fun i => ((K ∘L P i).kyFanGauge k : ℝ))
      l (𝓝 ((K.kyFanGauge k : ℝ))) := by
```

`DavisKahan/Sylvester/Unbounded/FormBoundedGap.lean` — `davisKahan1970_sylvester_complex` (declaration header, proof omitted):

```lean
theorem davisKahan1970_sylvester_complex
    (N : TauCeti.SymmetricOperatorIdealFamily ℂ)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gaugeReal X ≤
        N.gaugeReal C := by
```

**Type and hypothesis map.** Contractive inclusion plus contractive left inverse preserve all finite Ky Fan gauges. Strongly converging orthogonal projections yield convergence of each fixed finite Ky Fan prefix, under the stated min–max assumptions. The source-facing theorem includes the explicit `IsKyFanDominant` typeclass hypothesis. The theorem is a downstream application, not the definition of the dominance property.

These are exact excerpts from the supplied DKPS source snapshot. The mathematical narration develops its arguments independently; citing these declarations does not assert that the narrated intermediate proof has been separately compiled in Lean. Where the current declaration lives in `ForTauCeti`, its placement does not imply the mathematical result originated outside the DKPS project.
