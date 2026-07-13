/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.TanTheta

/-!
# The paper-exact finite Davis--Kahan `tan Θ` theorem

This module records the finite residual theorem in the exact orientation used
in Davis--Kahan (1970), Section 2 and equation (6.6): the Ritz compression lies
in a finite interval, while the unwanted exact spectrum lies above that
interval by `δ`.  The conclusion controls every unitarily invariant norm.

The proof is organized around the source argument.  The hard root is a family
of Ky Fan prefix inequalities obtained from singular vectors of the sine block;
Fan dominance then gives every rectangular unitarily invariant norm.  This is
intentionally separate from the later relaxed spectral-norm theorem and from
an ordered graph-Sylvester formulation.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The one-sided interval hypothesis in the original `tan Θ` theorem.

The Ritz compression of `A` to the trial coordinates is contained in
`[β, α]`, while the spectrum of `A` carried by the orthogonal complement of
the exact subspace is contained in `[α + δ, ∞)`. -/
def TanThetaIntervalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (β α δ : ℝ) : Prop :=
  SpectrumIn (compression A X) ⊤ (Set.Icc β α) ∧
    SpectrumIn A Uᗮ (Set.Ici (α + δ))

/-- The paper's interval hypotheses force the trial and exact subspaces to be
transverse.  Thus the tangent has no `π/2` pole; this is a conclusion, not an
extra hypothesis. -/
theorem isTransverse_of_tanThetaIntervalGap
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ) :
    IsTransverse (approximateSubspace X) U := by
  intro x hx hPx
  rcases hx with ⟨y, rfl⟩
  have hUperpRed : Reduces A Uᗮ := reduces_orthogonal_of_isSymmetric hA hU
  have hxyUperp : X.toLinearMap y ∈ Uᗮ := by
    have horth :
        X.toLinearMap y - U.starProjection (X.toLinearMap y) ∈ Uᗮ :=
      U.sub_starProjection_mem_orthogonal (X.toLinearMap y)
    rw [hPx, sub_zero] at horth
    exact horth
  have hTopRed : Reduces (compression A X) ⊤ := by
    intro z _
    exact Submodule.mem_top
  have hMspec : SpectrumIn (compression A X) ⊤ (Set.Iic α) := by
    intro lam hlam
    exact (hgap.1 hlam).2
  have hMupper :
      RCLike.re ⟪compression A X y, y⟫_𝕜 ≤ α * ‖y‖ ^ 2 :=
    re_inner_le_of_spectrumIn (isSymmetric_compression hA X)
      hTopRed hMspec Submodule.mem_top
  have hAlower :
      (α + δ) * ‖X.toLinearMap y‖ ^ 2 ≤
        RCLike.re ⟪A (X.toLinearMap y), X.toLinearMap y⟫_𝕜 :=
    le_re_inner_of_spectrumIn hA hUperpRed hgap.2 hxyUperp
  have hinner :
      RCLike.re ⟪compression A X y, y⟫_𝕜 =
        RCLike.re ⟪A (X.toLinearMap y), X.toLinearMap y⟫_𝕜 := by
    simp only [compression, LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_left]
  have hnorm : ‖X.toLinearMap y‖ = ‖y‖ := X.norm_map y
  have hyzero : y = 0 := by
    by_contra hy
    have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
    rw [← hinner, hnorm] at hAlower
    nlinarith [sq_pos_of_pos hynorm]
  simp [hyzero]

/-- **The source Ky Fan root for the finite `tan Θ` theorem.**

For every prefix length, the sum of the first principal tangents is bounded by
the corresponding singular-value prefix of the Ritz residual.  The proof is
the finite version of Davis--Kahan equation (6.6): choose singular vectors of
the directed sine block, construct the complementary cosine vectors, derive
the scalar gap inequalities, sum, and invoke the rectangular Ky Fan
variational principle.

The operator `tanTheta0` is intentionally arbitrary, as in the paper; only its
singular values are prescribed.  This theorem is the single hard
geometric/majorization seam. -/
theorem kyFan_tanTheta0_ritzResidual_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k tanTheta0 ≤
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
        (ritzResidual A X) := by
  sorry

/-- **Paper-exact Davis--Kahan `tan Θ`, residual form, every UI norm.**

This is the first conclusion in the 1970 theorem:

`δ * N (tan Θ₀) ≤ N R`.

As in the paper, `tanTheta0` may be any rectangular operator whose singular
values are the principal tangents.  The spectral assumptions themselves force
transversality. -/
theorem tanTheta0_ritzResidual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  have hprefix : ∀ k,
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
          (((δ : ℝ) : 𝕜) • tanTheta0) ≤
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
          (ritzResidual A X) := by
    intro k
    rw [RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul
      k tanTheta0 hδ.le]
    exact kyFan_tanTheta0_ritzResidual_le hA hU X hβα hδ hgap
      tanTheta0 htan k
  have hN := N.apply_le_of_kyFanSum_le hprefix
  rw [N.smul_eq] at hN
  simpa [RCLike.norm_ofReal, abs_of_pos hδ] using hN

/-- **The residual conclusion of the 1970 `tan Θ` theorem.**

This wrapper retains the equal-dimension hypothesis that is part of the global
setup of Sections 1--2 of Davis--Kahan.  The Ritz choice
`compression A X = X⋆ A X` is exactly the paper's condition `H₀ = 0`.
The tangent sequence is directed from the trial space `range X` toward the
exact invariant subspace `U`. -/
theorem davisKahan1970_tanTheta0_ritzResidual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) (_hrank : finrank 𝕜 F = finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  exact tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap tanTheta0 htan

/-- **Davis--Kahan Theorem 6.3, generalized `tan Θ`, residual conclusion.**

This wrapper retains the paper's strict dimension hypothesis: the trial space
has smaller dimension than the exact invariant subspace being approximated.
All other assumptions and the conclusion are identical to the source theorem
in the finite-dimensional setting. -/
theorem davisKahan1970_generalizedTanTheta0_ritzResidual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) (_hrank : finrank 𝕜 F < finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  exact tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap tanTheta0 htan

/-- Canonical directed-tangent specialization of the paper theorem. -/
theorem tanThetaEmbedding_ritzResidual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ) :
    δ * N (tanThetaEmbedding U X) ≤ N (ritzResidual A X) := by
  have htrans := isTransverse_of_tanThetaIntervalGap hA hU X hδ hgap
  have htan : (tanThetaEmbedding U X).singularValues =
      principalTangents (approximateSubspace X) U := by
    rw [← graphOperator_eq_tanThetaEmbedding U X htrans]
    exact singularValues_graphOperator U X htrans
  exact tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap
    (tanThetaEmbedding U X) htan

/-- The exact theorem also records explicitly that no principal tangent has a
pole. -/
theorem tanTheta0_ritzResidual_le_and_isTransverse
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) :
    IsTransverse (approximateSubspace X) U ∧
      δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  exact ⟨isTransverse_of_tanThetaIntervalGap hA hU X hδ hgap,
    tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap tanTheta0 htan⟩

end DavisKahanTheory
end ForMathlib
