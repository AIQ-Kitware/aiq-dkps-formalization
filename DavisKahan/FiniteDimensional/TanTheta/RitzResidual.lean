/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz
public import ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding
public import TauCeti.Analysis.InnerProductSpace.SingularValues
public import ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.RitzTangent

/-!
# The paper-exact finite Davis--Kahan `tan Θ` theorem

This module records the finite residual theorem in the exact orientation used
in Davis--Kahan (1970), Section 2 and equation (6.6): the Ritz compression lies
in a finite interval, while the unwanted exact spectrum lies above that
interval by `δ`.  The conclusion controls every unitarily invariant norm.

The accepted TauCeti Ritz-residual bound is applied on the range of the
trial isometry. Isometric coordinate transport recovers the paper's
formulation with an arbitrary operator having the principal tangents as
its singular values.
-/

public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional

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
@[expose] def TanThetaIntervalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (β α δ : ℝ) : Prop :=
  Module.End.PointSpectrumIn (compression A X) ⊤ (Set.Icc β α) ∧
    Module.End.PointSpectrumIn A Uᗮ (Set.Ici (α + δ))

private theorem pointSpectrumIn_ritz_on_range
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ}
    (hgap : TanThetaIntervalGap A U X β α δ) :
    Module.End.PointSpectrumIn
      (X.toLinearMap.range.subtype.adjoint ∘ₗ A ∘ₗ X.toLinearMap.range.subtype)
      ⊤ (Set.Iic α) := by
  have hM : Module.End.PointSpectrumIn (compression A X) ⊤ (Set.Iic α) :=
    hgap.1.mono le_rfl Set.Icc_subset_Iic_self
  apply Module.End.pointSpectrumIn_Iic_of_re_inner_apply_self_le
  intro z _
  let e := X.equivRange
  have hz : X (e.symm z) = (z : E) := congrArg Subtype.val (e.apply_symm_apply z)
  have h := hA.re_inner_ritz_le_of_pointSpectrumIn X.toLinearMap hM (e.symm z)
  have hnorm : ‖e.symm z‖ = ‖z‖ := e.symm.norm_map z
  rw [hnorm] at h
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, Submodule.subtype_apply]
  simpa only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearIsometry.coe_toLinearMap,
    hz] using h

/-- The paper's interval hypotheses force the trial and exact subspaces to be
transverse. Thus the tangent has no `π/2` pole. -/
theorem isTransverse_of_tanThetaIntervalGap
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : U ∈ Module.End.invtSubmodule A)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ) :
    Disjoint X.toLinearMap.range Uᗮ :=
  X.toLinearMap.range.disjoint_orthogonal_of_directedProjectionGap_lt_one U
    (X.toLinearMap.range.directedProjectionGap_lt_one_of_pointSpectrumIn_compression
      U hA hU hδ (pointSpectrumIn_ritz_on_range hA X hgap) hgap.2)

/-- The principal tangent at an index is `tan (arcsin σ)` for the directed sine block. -/
theorem principalTangents_approximateSubspace_apply
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) (i : ℕ) :
    X.toLinearMap.range.principalTangents U i =
      Real.tan (Real.arcsin ((sinThetaEmbedding U X).singularValues i)) := by
  rw [Submodule.principalTangents_apply, Submodule.principalAngles_apply]
  exact congrArg (fun s : ℕ →₀ ℝ => Real.tan (Real.arcsin (s i)))
    (U.principalSines_range_eq_singularValues (X := X.toContinuousLinearMap) X.isometry)

/-- **Paper-exact Davis--Kahan `tan Θ`, residual form, every UI norm.**

This is the first conclusion in the 1970 theorem:

`δ * N (tan Θ₀) ≤ N R`.

As in the paper, `tanTheta0` may be any rectangular operator whose singular
values are the principal tangents.  The spectral assumptions themselves force
transversality. -/
theorem tanTheta0_ritzResidual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A))
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (_hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      X.toLinearMap.range.principalTangents U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  let Z := X.toLinearMap.range
  let e : F ≃ₗᵢ[𝕜] Z := X.equivRange
  have hM := pointSpectrumIn_ritz_on_range hA X hgap
  have hgapZ := Z.directedProjectionGap_lt_one_of_pointSpectrumIn_compression
    U hA hU hδ hM hgap.2
  have hN := UnitarilyInvariantSeminorm.mul_map_tanThetaMap_le_map_ritzResidual
    (UnitarilyInvariantSeminorm.arrowCongr e (LinearIsometryEquiv.refl 𝕜 E) N)
    hA hU hδ hM hgap.2
  have hX : Z.subtype ∘ₗ (e : F →ₗ[𝕜] Z) = X.toLinearMap := rfl
  have hadj : (e : F →ₗ[𝕜] Z) ∘ₗ X.toLinearMap.adjoint = Z.subtype.adjoint := by
    have h := congrArg LinearMap.adjoint hX
    rw [LinearMap.adjoint_comp, e.adjoint_coe_eq_symm] at h
    rw [← h, ← LinearMap.comp_assoc]
    have he : (e : F →ₗ[𝕜] Z) ∘ₗ (e.symm : Z →ₗ[𝕜] F) = LinearMap.id := by
      apply LinearMap.ext
      intro y
      exact e.apply_symm_apply y
    rw [he, LinearMap.id_comp]
  have hR :
      (A ∘ₗ Z.subtype - Z.subtype ∘ₗ (Z.subtype.adjoint ∘ₗ A ∘ₗ Z.subtype)) ∘ₗ
        (e : F →ₗ[𝕜] Z) = ritzResidual A X := by
    rw [LinearMap.sub_comp, LinearMap.comp_assoc, hX, ← hadj]
    simp only [ritzResidual, residual, compression, LinearMap.comp_assoc, hX]
    rw [← LinearMap.comp_assoc _ (e : F →ₗ[𝕜] Z) Z.subtype, hX]
  have htan' : tanTheta0.singularValues =
      (Z.tanThetaMap U ∘ₗ (e : F →ₗ[𝕜] Z)).singularValues := by
    rw [LinearMap.singularValues_comp_linearIsometryEquiv, Z.singularValues_tanThetaMap U hgapZ]
    exact htan
  have hrefl : ((LinearIsometryEquiv.refl 𝕜 E).symm : E →ₗ[𝕜] E) = LinearMap.id := rfl
  simpa only [UnitarilyInvariantSeminorm.arrowCongr_apply, hrefl, LinearMap.id_comp,
    hR, ← N.map_eq_of_singularValues_eq htan'] using hN

/-- The Ritz-residual bound for each Ky Fan prefix. -/
theorem kyFan_tanTheta0_ritzResidual_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : U ∈ Module.End.invtSubmodule A)
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues = X.toLinearMap.range.principalTangents U) (k : ℕ) :
    δ * tanTheta0.kyFanSum k ≤ (ritzResidual A X).kyFanSum k := by
  simpa only [UnitarilyInvariantSeminorm.kyFan_apply] using
    tanTheta0_ritzResidual_le (UnitarilyInvariantSeminorm.kyFan 𝕜 F E k)
      hA hU X hβα hδ hgap tanTheta0 htan

/-- **The residual conclusion of the 1970 `tan Θ` theorem.**

This wrapper retains the equal-dimension hypothesis that is part of the global
setup of Sections 1--2 of Davis--Kahan.  The Ritz choice
`compression A X = X⋆ A X` is exactly the paper's condition `H₀ = 0`.
The tangent sequence is directed from the trial space `range X` toward the
exact invariant subspace `U`. -/
theorem davisKahan1970_tanTheta0_ritzResidual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A))
    (X : F →ₗᵢ[𝕜] E) (_hrank : finrank 𝕜 F = finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      X.toLinearMap.range.principalTangents U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  exact tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap tanTheta0 htan

/-- **Davis--Kahan Theorem 6.3, generalized `tan Θ`, residual conclusion.**

This wrapper retains the paper's strict dimension hypothesis: the trial space
has smaller dimension than the exact invariant subspace being approximated.
All other assumptions and the conclusion are identical to the source theorem
in the finite-dimensional setting. -/
theorem davisKahan1970_generalizedTanTheta0_ritzResidual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A))
    (X : F →ₗᵢ[𝕜] E) (_hrank : finrank 𝕜 F < finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      X.toLinearMap.range.principalTangents U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  exact tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap tanTheta0 htan

/-- The exact theorem also records explicitly that no principal tangent has a
pole. -/
theorem tanTheta0_ritzResidual_le_and_isTransverse
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A))
    (X : F →ₗᵢ[𝕜] E) {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : TanThetaIntervalGap A U X β α δ)
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      X.toLinearMap.range.principalTangents U) :
    Disjoint X.toLinearMap.range Uᗮ ∧
      δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  exact ⟨isTransverse_of_tanThetaIntervalGap hA hU X hδ hgap,
    tanTheta0_ritzResidual_le N hA hU X hβα hδ hgap tanTheta0 htan⟩

end DavisKahan.FiniteDimensional
end TauCeti
