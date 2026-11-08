# 129000 — One complete original-paper proof reconstruction

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `065000`, `070000`, `095000–100000`, `122000–124000`. **Next:** `130000`, restricted direct-rotation optimality.

<!-- BEGIN SPOKEN LECTURE -->

# One complete original-paper proof reconstruction

We have now learned many results that appear separately in the Davis–Kahan paper: the spectral theorem, operator ideals, Sylvester equations, principal-angle operators, Ky Fan inequalities, and pinching. In this lecture we will assemble them into one complete argument for Proposition six point one, the ambient sine theorem.

Our goal is to prove that delta times the unitarily invariant norm of the sine of the ambient angle is at most the norm of the perturbation. We will identify every hypothesis, derive the two Sylvester equations, justify their norm bounds, recover the ambient sine singular values, and transfer the result to a symmetric norm ideal.

## State the theorem precisely

Work first on a finite-dimensional real or complex inner-product space. Let A and B be self-adjoint matrices, and write K for B minus A. Let U be a reducing subspace of A, and V a reducing subspace of B. Their projections are P and Q.

Take a positive number delta. Assume the spectrum of A on U is separated from the spectrum of B on V perpendicular by at least delta in an interval-versus-exterior configuration. Assume also that the spectrum of B on V is similarly separated from the spectrum of A on U perpendicular by delta.

These are two independent crossed separation conditions. They are stronger than saying each pair of selected eigenvalues is distinct. They authorize the sharp constant-one Sylvester estimate in the norm class we will use.

Let N be any unitarily invariant matrix norm. We want to prove delta times N of the absolute value of P minus Q is at most N of K. Because N is unitarily invariant, taking the modulus does not change the singular-value norm. And because the ambient sine-angle operator has the same singular values as that modulus, this is the advertised sine bound.

## First prerequisite: a valid Sylvester inverse estimate

Consider a general equation H X minus X L equals C. Suppose the spectrum of L lies in a closed interval from beta to alpha, while the spectrum of H lies outside the expanded open interval from beta minus delta to alpha plus delta.

First handle the part of H's spectrum above alpha plus delta. Shift both operators by the same scalar alpha. On that high spectral component, H minus alpha is positive and at least delta, while L minus alpha is negative semidefinite.

For positive time t, the product of the decaying exponential of minus t times H minus alpha, the operator C, and the exponential of t times L minus alpha has norm at most the norm of C times exponential of minus delta t.

Integrating from zero to infinity produces a bounded X. Differentiate the integrand to verify the Sylvester equation, with the sign chosen for H X minus X L. The norm of the integral is at most the integral of exponential decay, which equals one over delta times N of C.

The lower spectral component is handled by reversing the order and signs. In the interval-versus-exterior case, the two parts of H lie on opposite sides. Treating the two pieces as an operator-norm sum could waste a factor of two. The source instead uses the bounded-inverse formulation of the Sylvester theorem, or an equivalent blockwise spectral argument that preserves the compatible invariant norm. That theorem supplies the constant-one estimate for the complete exterior spectrum.

In this reconstruction we use that established Sylvester inverse result exactly as proved in the earlier Sylvester unit. We will not substitute the pairwise-distance Hilbert–Schmidt theorem, which does not authorize a constant-one estimate for arbitrary invariant norms.

## Build the first crossed equation

Define X as the cross projection from U into V perpendicular. Because U reduces A and V perpendicular reduces B, the restricted operators compose with X in the expected way.

Compute B on V perpendicular times X, minus X times A on U. The two terms combine into the V-perpendicular projection of B minus A applied to U. In other words, the Sylvester right-hand side is the corresponding block of K.

The first separation hypothesis therefore yields, for every positive integer k, delta times the first k singular values of X added together at most the first k singular values of that K block added together.

We state the estimate for every prefix, rather than just one preferred norm, because the later direct-sum argument combines prefixes of potentially different sizes.

## Build the reverse crossed equation

Now define X prime as the cross projection from U perpendicular into V. This is the adjoint of the escape map from V into U perpendicular, so it has the same nonzero singular values as that reverse escape.

Compute B on V times X prime, minus X prime times A on U perpendicular. The resulting right-hand side is the other selected block of K.

The second separation hypothesis gives the same all-prefix inequality for X prime and that second K block.

This step is the reason Proposition six point one is symmetric. A single trial residual would give only one equation; our two reducing subspaces and ambient perturbation give a matched pair.

## Identify the ambient angle algebraically

Let D be P minus Q. Expand D squared. Since P and Q are orthogonal projections, D squared equals P plus Q minus P Q minus Q P.

On the decomposition U plus U perpendicular, this operator is block diagonal. On U, its block is the cross projection X adjoint X. On U perpendicular, its block is the product of the adjoint of X prime with X prime.

Taking the positive square root gives the modulus of D. Its nonzero singular values are exactly those of X together with those of X prime, including multiplicities.

This is the exact ambient sine representation. If U and V have unequal dimensions, right-angle defect directions are included in the appropriate cross block. No equal-rank simplification was used.

## Prove the direct-sum prefix step

For any two matrices M and N, the sum of the largest k singular values of their orthogonal direct sum is the maximum over all splits of k into i and k minus i, of the first i singular values of M plus the first k minus i of N.

Why? The singular values of the direct sum are the decreasing rearrangement of the two component lists. Choosing the top k entries is equivalent to choosing some number from the first list and the remaining number from the second. The best such split gives exactly the prefix sum.

Apply this identity to X and X prime. Because each of their prefix sums is bounded by the corresponding projected perturbation block, the merged singular-value prefix of the ambient sine is at most one over delta times the merged prefix for the pair of K blocks.

This is Lemma six point one's forward direction. We did not need its converse, and we did not assume the component singular-value lists matched.

## Prove the pinching step

The pair of right-hand-side K blocks occupies orthogonal input and output corners, after reordering the output decomposition V plus V perpendicular. Call their block sum K pinched.

Construct an input reflection that is positive on U and negative on U perpendicular. Construct an output reflection with opposite signs on V and V perpendicular, chosen so the selected corners keep their sign.

Conjugating K by the output reflection on the left and input reflection on the right negates the discarded corners and preserves the selected corners. Average this transformed operator with K. The off-diagonal corners cancel, leaving K pinched.

Both reflections are unitary. Therefore every unitarily invariant norm gives N of K pinched at most one half of N of K plus one half of N of the reflected K, which equals N of K.

This is Lemma six point two. It gives the constant one that would have been lost by bounding the two blocks separately.

## Put the inequalities together

We have three all-prefix comparisons. First, the two crossed Sylvester equations yield the respective delta-scaled bounds. Second, direct-sum comparison combines them into an ambient sine prefix inequality. Third, pinching bounds the combined perturbation blocks by the original K at every prefix.

Thus, for each k, delta times the Ky Fan k norm of the ambient sine is at most the Ky Fan k norm of K.

In finite dimensions every unitarily invariant norm is determined by a symmetric gauge of the singular values. A weak-majorization inequality for all prefixes implies the corresponding symmetric-gauge inequality. Consequently delta times N of the ambient sine is at most N of K.

That completes the finite-dimensional proof, with no hidden dependence on a particular singular-vector basis.

## Extend the logic to Hilbert-space ideals

The original source works in a separable Hilbert space. Here an arbitrary bounded operator need not have finite N norm, and singular-value prefixes are formulated using approximation numbers.

The bounded self-adjoint restrictions and crossed interval-versus-exterior gaps still supply the corresponding Sylvester estimates. The reflection identity is algebraic, hence valid on Hilbert spaces. The direct-sum prefix principle uses approximation-number machinery rather than a finite list of matrix singular values.

To avoid assuming the conclusion's finiteness, begin with K in the chosen symmetric ideal. Ideal closure under bounded left and right multiplication places its projected blocks in the ideal. The two Sylvester inequalities and Ky Fan dominance then place the crossed operators and their direct sum in the ideal. Finally the ambient sine representative, having the same approximation singular values, belongs to the ideal and satisfies the bound.

If the proof uses finite basis or spectral cutoffs, establish convergence of each fixed approximation singular value and preserve all finite prefixes before invoking the ideal's dominance property. Strong convergence alone does not imply convergence of arbitrary ideal norms.

In the unbounded common-domain version, there is further work: the difference B minus A must extend to the bounded perturbation K on a shared domain, the reducing restrictions must preserve their domains, and cutoff limits must justify the Sylvester identities. Those are additional hypotheses and lemmas, not consequences of the bounded proof by notation.

## One sharp example and one boundary failure

Take A with eigenvalues zero and four, and let B be its rotation by theta. Choose U and V as the corresponding zero-eigenspaces. Both crossed gaps are four. The operator norm of their projection difference is sine theta, while the norm of B minus A is four sine theta. Equality holds.

Now imagine using only the first crossed equation and allowing U to be a line contained in a larger V. Its directed sine is zero, while the ambient projection difference has norm one. Without the second equation, the ambient conclusion cannot follow. This checks the logic of the theorem, not just its numerical constant.

## Final reconstruction

The proof rests on four mathematical mechanisms that now have independent justifications. Self-adjoint spectral restrictions and crossed gaps authorize two Sylvester inverses. Projection algebra identifies the ambient sine with two directed singular-value lists. Ky Fan direct-sum comparison merges the two spectral estimates. Reflection averaging contracts the pair of perturbation blocks into the original perturbation.

Tracking ideal membership makes the argument valid beyond matrices. Tracking both gap conditions prevents a directed theorem from being misstated as an ambient one. That is a complete proof architecture for Proposition six point one and a model for the source-faithful perturbation arguments that follow.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)


Reconstruction target: the bounded self-adjoint, **two-crossed-gap** Proposition 6.1, at the source's separable-Hilbert-space scope. Denote \(K=B-A\) and the crossed maps \(X=P_{V^\perp}P_U\), \(X'=P_VP_{U^\perp}\). The chain is
\[
 \begin{aligned}
 \delta\,\|X\|_{(k)}&\le\|P_{V^\perp}KP_U\|_{(k)},\\
 \delta\,\|X'\|_{(k)}&\le\|P_VKP_{U^\perp}\|_{(k)},\\
 \delta\,\||P_U-P_V|\|_{(k)}&\le\|K\|_{(k)}\quad(\forall k).
 \end{aligned}
\]
The last line combines Ky Fan direct-sum comparison (`lemma61_all_kyFan`) and two-sided pinching (`lemma6_2_separable`). For a Fan-dominant normalized unitarily invariant ideal, all-prefix dominance transfers membership and the gauge bound. The proof's finite-dimensional part is fully expanded in the narration; the Hilbert-space step uses the spectral/Sylvester and approximation-number results proved in earlier lectures, as indicated, rather than silently asserting operator-norm cutoff convergence.


### Exact Lean declaration excerpts


`DavisKahan/Sources/DavisKahan1970/Section6SourceScope.lean` — `proposition6_1_printedGap_sourceExact_complex` (exact declaration header; proof body omitted):

```lean
theorem proposition6_1_printedGap_sourceExact_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A) (hV : Submodule.IsReducing V B)
    {δ : ℝ} (hδ : 0 < δ)
    {β α β' α' : ℝ} (hβα : β ≤ α) (hβα' : β' ≤ α')
    (hgapUV : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap
      (DavisKahanExt.PartialMap.boundedReducingBlock A U hU)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl B V hV) β α δ)
    (hgapVU : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap
      (DavisKahanExt.PartialMap.boundedReducingBlock B V hV)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl A U hU) β' α' δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (cfc Real.sin (DavisKahan.Angle.angleOperator U V)) ∧
      δ * N.gauge (cfc Real.sin (DavisKahan.Angle.angleOperator U V)) ≤ N.gauge (B - A) :=
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


`DavisKahan/Sources/DavisKahan1970/Section6SourceScope.lean` — `lemma6_2_separable` (exact declaration header; proof body omitted):

```lean
theorem lemma6_2_separable {𝕜 : Type} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} 𝕜)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.Mem (diagonalPair U V K) ∧ N.gauge (diagonalPair U V K) ≤ N.gauge K :=
```



**Mapping.** `proposition6_1_printedGap_sourceExact_complex` is the exact bounded-complex source-facing theorem. `lemma61_all_kyFan` handles the all-prefix direct-sum comparison. `lemma6_2_separable` supplies contraction of the two-sided pinching in the paper’s separable ambient setting. The complete argument depends on the independent Sylvester estimates, on ideal membership and Fan dominance, and on both crossed gap hypotheses.

