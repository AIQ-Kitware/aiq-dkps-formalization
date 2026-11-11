# 097000 — Ky Fan dominance in Hilbert space

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `054000` Ky Fan sums, `055000` weak majorization, `056000` convex descent, `096000` approximation numbers. **Next:** `098000` symmetric operator ideals and membership.

<!-- BEGIN SPOKEN LECTURE -->

# Comparing whole patterns of singular values

Suppose two machines have the same total amount of stretching, but they distribute it differently. One stretches its three principal directions by three, one, and zero. The other stretches them by two, two, and zero.

If you judge the machines by their single largest stretching factor, the first is larger: three versus two. If you add all their stretching factors, they tie at four. If you add the squares, the first gives ten, while the second gives eight.

So a comparison based on one number can depend on which number we choose. What kind of information would let us compare operators under many different ways of measuring their size?

The central idea is to compare the running totals of the largest singular values. These are called Ky Fan sums, and the resulting comparison is called weak majorization.

## Build the comparison from a short list

Let's use our two lists again. List A has singular values three, one, and zero. List B has two, two, and zero.

The first running total of A is three. The second is four. The third is still four.

The running totals of B are two, four, and four.

At every stopping point, B's running total is no larger than A's. So B is weakly majorized by A.

This does not mean each individual entry of B is smaller. Its second entry, two, is larger than A's second entry, one. We are comparing cumulative totals starting from the largest entry.

Why is that useful? A symmetric norm is insensitive to how singular directions are labeled. Many such norms also behave predictably when a fixed total is redistributed more evenly. Weak majorization captures the comparisons that survive this redistribution.

For instance, the largest-singular-value norm is two for B and three for A. The trace norm is four for both. The square-root-of-sum-of-squares norm is square root of eight for B and square root of ten for A. All three comparisons point in the same allowed direction.

The remarkable part is that, under the right conditions, checking every Ky Fan running total lets us compare a whole family of norms.

## Define Ky Fan sums for operators

A singular-value list is available for compact operators. But we want to discuss bounded operators on Hilbert spaces even when no discrete singular-value expansion exists.

We can do that with approximation numbers. The first approximation number is the operator norm. The k-th is the best possible operator-norm error when we replace the operator by one of rank strictly less than k.

For each positive integer k, define the k-th Ky Fan approximation gauge as the sum of the first k approximation numbers. The first Ky Fan gauge is therefore the operator norm.

Each fixed sum is finite for every bounded operator. Since every approximation number is at most the operator norm, the sum of the first k is at most k times that norm.

For a compact operator, this is exactly the sum of its k largest singular values, counting multiplicities and adding zeros after the rank if necessary.

For the identity on infinite-dimensional ell two, every approximation number is one. Consequently its k-th Ky Fan gauge equals k. Every individual finite prefix is well-defined, although the infinite sum of all approximation numbers diverges.

That distinction will become important. Being able to compare every finite prefix does not automatically mean an infinite trace norm is finite.

## Why the first few directions are enough

Consider a positive finite-rank operator whose nonzero eigenvalues are five, two, and one. Its first Ky Fan gauge is five. Its second is seven. Its third is eight. Every later gauge stays eight because the remaining singular values are zero.

In a finite-dimensional matrix, each Ky Fan sum has a variational interpretation. We look at collections of k orthonormal input directions and matching orthonormal output directions, and measure the total aligned action of the matrix. The largest achievable total equals the sum of the k largest singular values.

We can understand the idea from a diagonal matrix. If we choose two directions, the best pair is the pair with stretches five and two. Taking a smaller direction in place of either can only reduce the total.

The variational principle remains valid for the finite prefixes of bounded Hilbert-space operators, with the appropriate finite-dimensional conventions. Approximation numbers give a way to state the same result without assuming the entire operator has an eigenbasis.

For compact operators, there is a particularly clean proof. Truncate the singular-value expansion. On each finite truncation, the matrix variational principle applies. Then let the truncation grow. Every fixed approximation number changes by no more than the operator-norm approximation error, so a fixed Ky Fan sum converges as well.

The key is that we are fixing k. We are only asking about a finite amount of the leading behavior.

## Why Ky Fan sums satisfy a triangle inequality

Now suppose S and T act between the same pair of Hilbert spaces. Why should the k-th Ky Fan gauge of their sum be no larger than the sum of their separate k-th gauges?

Think first about matrices. Choose k orthonormal input and output directions that almost attain the largest aligned action for S plus T. When we evaluate S plus T on those chosen directions, linearity splits the total into an S contribution and a T contribution.

Neither individual contribution can exceed its own optimal Ky Fan value. Therefore their sum cannot exceed the sum of the two optimal values. Taking better and better choices of directions proves the triangle inequality.

The Hilbert-space formulation uses the corresponding finite-frame variational principle. So the same argument gives a triangle inequality for each finite Ky Fan approximation gauge, including operators that are not compact.

This is a useful surprise. The finite prefixes behave like norms even when the full infinite singular-value sum is infinite.

## Weak majorization is a family of inequalities

We say the approximation numbers of T are weakly majorized by those of S if, for every positive integer k, the sum of the first k approximation numbers of T is at most the matching sum for S.

This is an infinite family of finite, checkable inequalities. It compares the cumulative leading size of the operators.

Return to our short lists. The operator with singular values two, two, zero is weakly majorized by the one with three, one, zero. The reverse is false, because the first prefix would demand three to be no greater than two.

Sometimes neither of two operators dominates the other. Consider five, one, zero and four, three, zero. The first list wins at the first position, while the second wins in the total of the first two. In that case there is no weak-majorization conclusion in either direction.

Weak majorization is a partial comparison. It does not promise that any two operators can be ranked.

## From prefixes to a chosen norm

For finite vectors of nonnegative numbers, symmetric convex gauges are monotone under weak majorization. The proof is a general fact about redistributing entries: coordinate rearrangements leave the gauge unchanged, while suitable averaging operations cannot increase a convex symmetric gauge.

This includes the largest-entry norm, the sum norm, and the square-root-of-sum-of-squares norm. It also includes every finite-dimensional unitarily invariant matrix norm through its symmetric gauge on singular values.

Infinite dimensions introduce a new issue. A norm based on an infinite sequence may not be finite for every bounded operator. The trace norm, for example, is only finite for trace-class operators.

Therefore an infinite-dimensional dominance theorem must address both membership and the bound. It should say that if S belongs to a particular symmetric operator ideal, and T is weakly dominated by S in all Ky Fan prefixes, then T also belongs to that ideal and its norm is no larger.

That conclusion holds for familiar Schatten classes. In a more general abstract symmetric ideal, we require the appropriate Ky Fan dominance property as a hypothesis. We cannot simply assume every imaginable normed ideal has it.

## See the membership issue with a sequence

Take an operator diagonal on ell two with entries one over n. Its singular values are one, one half, one third, and so on.

Each finite Ky Fan sum exists. But as we include more entries, the partial sums grow without bound, because the harmonic series diverges. This operator is not trace class.

On the other hand, the sum of its squared singular values is finite. So it is Hilbert-Schmidt.

Now think of a theorem that says the Hilbert-Schmidt norm of T is at most the Hilbert-Schmidt norm of S. That statement is only a finite numerical bound if both operators belong to the Hilbert-Schmidt class. A proper dominance theorem establishes the membership of T as part of its conclusion.

The same distinction explains why a family of finite inequalities is not by itself an infinite-norm convergence theorem.

For example, project ell two onto its first N coordinates. These finite-rank projections converge on each fixed vector to the identity. But their trace norms equal N, and the identity has infinite trace norm. Strong convergence is far too weak to imply trace-norm convergence.

## A final comparison

The idea of Ky Fan dominance is to avoid choosing a single preferred norm too early. Instead, we compare every leading singular-value total. Under the correct ideal hypothesis, that family of inequalities transfers to the ideal norm we actually need.

The finite-dimensional example with three, one, zero versus two, two, zero explains the geometry. The infinite-dimensional diagonal with entries one over n explains why we must also prove summability.

Those are the two pieces to retain: prefix inequalities control how singular-value mass is distributed, and an ideal's dominance property turns that control into a meaningful finite norm estimate.

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
