# 127000 — The generalized tangent bound

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `027000`, `107000`, `111000`, `112000`, `125000`. **Next:** `128000`, spectral cutoff and finite-rank source lemmas.

<!-- BEGIN SPOKEN LECTURE -->

# The generalized tangent bound

The single-angle tangent theorem controls a tangent of the subspace error when spectral separation is measured from a Rayleigh–Ritz compression. Davis and Kahan's Theorem six point three develops this geometry in a generalized form. The trial space may have smaller dimension than the exact selected space, and the conclusion concerns a directed tangent.

A tangent bound is stronger than a sine bound when the angle is large. Yet the theorem does not simply divide a previously known sine estimate by a cosine. The Rayleigh–Ritz orthogonality and the placement of the unwanted spectrum do additional work. We will derive their role and prove the maximal-angle bound directly in finite dimensions before explaining the all-singular-values extension.

## Which spaces are being compared?

Let A be self-adjoint. Let V be an exact reducing subspace, with complementary space W. Let Z be a trial subspace with an orthonormal coordinate map. We do not initially require Z and V to have equal dimension.

Compress A to Z. The result is the Rayleigh–Ritz operator A zero. Assume its spectrum lies at or below an upper threshold alpha. Assume the spectrum of A on the unwanted exact complement W lies at or above alpha plus delta, where delta is positive.

This is the source's one-sided separation. The trial compression is below; the unwanted exact spectrum is above. The subspace V itself may have a larger dimension than Z, and its exact spectrum need not consist of one eigenvalue.

Form the Ritz residual R by applying A to the trial frame and subtracting the trial frame followed by A zero. It is orthogonal to the trial space by the definition of compression.

## Why a right angle is impossible

Suppose a nonzero trial vector z lies entirely in W. Because the Rayleigh–Ritz compression has spectrum at most alpha, its quadratic form on z is at most alpha times the squared length of z. But because z also belongs to W and A restricted to W is bounded below by alpha plus delta, the same quadratic form is at least alpha plus delta times its squared length.

This is impossible for positive delta. Hence Z has no nonzero vector perpendicular to V.

In finite dimension, the projection from Z into V is therefore injective and bounded below. We can regard Z as a graph over its image in V. Its graph map gives a finite tangent angle operator. No equal-dimension assumption was needed to establish this one-sided transversality.

For infinite-dimensional trial spaces, the absence of an exact perpendicular vector alone does not guarantee a bounded inverse of the projection. A bounded tangent representative requires quantitative control of the projection inverse. Mere injectivity does not ensure its range is closed.

## A principal-vector calculation

Choose a unit trial vector z realizing the largest directed principal angle theta in the finite-dimensional case. Write it as cosine theta times a unit vector v in V, plus sine theta times a unit vector w in W. The chosen directions are principal vectors, so projection of w back onto Z is sine theta times z.

Let T be the Rayleigh–Ritz compression of A to Z. Since z is in Z, the quadratic form of T at z is at most alpha. Since w is in W, the quadratic form of A at w is at least alpha plus delta.

Take the inner product of the residual R z with w. The A term contributes sine theta times the quadratic form of A at w. The compression term contributes sine theta times the quadratic form of T at z, using the principal-vector projection identity.

Subtract. The result is at least delta times sine theta. This is the gap estimate in one chosen principal direction.

But we can improve the Cauchy–Schwarz step using Ritz orthogonality. Since R z is perpendicular to Z, its pairing with w equals its pairing with w minus sine theta times z. The latter vector has length cosine theta.

Therefore delta times sine theta is at most the residual norm times cosine theta. Divide by cosine theta, which is positive by transversality. We obtain delta times tangent theta at most the residual norm.

We did not obtain that cosine from the spectral gap. It came from the residual being perpendicular to Z. Without that orthogonality, this derivation gives only a sine estimate.

## Check the bound on a rotated line

Take A diagonal with eigenvalues zero and d, with d positive. The exact selected subspace is the horizontal axis, and W is the vertical axis. Let the one-dimensional trial subspace be the line at angle theta above the horizontal.

Its Ritz value is d times sine squared theta. The unwanted exact eigenvalue is d, so the gap between that eigenvalue and the Ritz compression is d cosine squared theta.

The Ritz residual has length d sine theta cosine theta. Multiply the spectral gap by tangent theta. We get d cosine squared theta times sine theta divided by cosine theta, which equals d sine theta cosine theta.

Equality holds. The gap used in the tangent estimate is the distance from the Ritz eigenvalue to the unwanted exact eigenvalue, not the full distance d between the original coordinate eigenvalues.

As theta approaches a right angle, the Ritz value approaches the unwanted eigenvalue and the available gap closes. This explains why the theorem cannot promise a finite tangent bound from a gap that is no longer present.

## Why the full theorem needs singular-value machinery

Our principal-vector proof controlled the largest tangent, hence the operator norm. A theorem for every unitarily invariant norm requires considerably more: the sum of the first k tangent singular values must be bounded by the corresponding residual singular-value prefix, for each k.

It is not sufficient to apply the operator-norm proof independently to each singular direction. The Ritz compression can mix those directions, and the extremizing subspaces can differ with k. The full proof uses finite-rank variational principles, compression identities, and Ky Fan dominance to control all prefixes simultaneously.

Directed tangent singular values are tangents of the principal angles, equivalently tangents of arcsines of the directed sine singular values. They are finite only when those sine values are strictly below one. The relevant spectral-placement theorem must establish this strict bound before a tangent representative is formed.

This last construction matters in infinite dimensions, where a coordinate map with the right formal name is not enough to establish an actual bounded operator.

## Dimensions and the precise tangent theorem

The printed generalized theorem uses a strict dimension inequality between the trial and exact selected coordinate spaces. In the common finite-dimensional situation, a smaller trial space can still be compared with the larger selected exact space through directed principal angles.

The equal-rank tangent theorem is a separate companion, not a consequence of specializing a strict inequality. Extensions to arbitrary trial dimension require explicit transversality and ideal hypotheses and must be stated separately.

The finite-dimensional strict-lower-rank, equal-rank, and Hilbert-space statements have different assumptions. A directed tangent map may exist even when a symmetric ambient tangent representation of both subspaces does not.

## Domain and norm requirements

For an unbounded self-adjoint A, the trial subspace must lie in its domain, and the Ritz compression and residual must be bounded in the appropriate senses. The exact spectral complement needs to reduce A. The gap must compare the actual Ritz compression spectrum with the unwanted exact spectrum.

For a chosen symmetric ideal, finiteness of the residual ideal norm is a hypothesis and finiteness of the tangent ideal norm is part of the conclusion. The Lyapunov or Sylvester steps that lead to the all-prefix bound must respect the same norm class.

The generalized tangent theorem therefore involves more than an angle identity. It packages a spectral placement, a variational orthogonality property, a transversality conclusion, and a singular-value comparison.

## Close

The operator-norm proof is memorable. Compare a principal direction's unwanted spectral energy with its Ritz energy. Use residual orthogonality to gain a cosine factor. Divide to obtain tangent rather than sine. Then extend from the largest principal angle to all singular-value prefixes using the Ky Fan machinery.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)


The finite source-faithful strict-rank theorem takes `finrank 𝕜 F < finrank 𝕜 U`, an isometric trial frame `X`, `TanThetaIntervalGap`, and an explicit tangent representative whose singular values equal `(approximateSubspace X).principalTangents U`. It concludes
\[\delta\,N(\tan\Theta_0)\le N(\operatorname{ritzResidual}(A,X)).\]
The `theorem6_3_all_kyFan_core` declaration supplies every approximation-number prefix in the bounded infinite-ambient setting. The perturbation companion additionally assumes the trial subspace is invariant under \(T+E\), which implies a residual block bounded by the perturbation restricted to that trial subspace. These have different scopes; none is an unconditional assertion about arbitrary ambient tangents.


### Exact Lean declaration excerpts


`DavisKahan/FiniteDimensional/TanTheta/RitzResidual.lean` — `davisKahan1970_generalizedTanTheta0_ritzResidual_le` (exact declaration header; proof body omitted):

```lean
theorem davisKahan1970_generalizedTanTheta0_ritzResidual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A))
    (X : F →ₗᵢ[𝕜] E) (_hrank : finrank 𝕜 F < finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      (approximateSubspace X).principalTangents U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
```


`DavisKahan/TanTheta/Theorem63FiniteSource.lean` — `theorem6_3_all_kyFan_core` (exact declaration header; proof body omitted):

```lean
theorem theorem6_3_all_kyFan_core
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (hV : Submodule.IsReducing V T) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0) :
    ∀ k, delta * (tanTheta0.kyFanGauge k : ℝ) ≤
      ((theorem63Residual T Z).kyFanGauge k : ℝ) := by
```


`DavisKahan/Sources/DavisKahan1970/Section2TanThetaPerturbation.lean` — `theorem6_3_perturbation_infiniteTrial` (exact declaration header; proof body omitted):

```lean
theorem theorem6_3_perturbation_infiniteTrial
    (N : TauCeti.SymmetricOperatorIdealFamily ℂ)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    (T E : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (hV : Submodule.IsReducing V T) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (hinv : ∀ x ∈ Z, (T + E) x ∈ Z)
    (hEmem : N.Mem (E ∘L Z.subtypeL)) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gaugeReal tanTheta0 ≤ N.gaugeReal (E ∘L Z.subtypeL) := by
```



**Mapping.** `ritzResidual` corresponds to the Galerkin-orthogonal residual. `TanThetaIntervalGap` compares the trial Ritz compression with the unwanted exact spectral part. In the finite theorem, the literal rank comparison is strict. The Ky Fan theorem proves a *family* of prefix bounds; the perturbation companion uses `(T + E) x ∈ Z` to replace residual by restricted perturbation. The source has additional finite-trial and infinite-trial formulations with distinct premises.

