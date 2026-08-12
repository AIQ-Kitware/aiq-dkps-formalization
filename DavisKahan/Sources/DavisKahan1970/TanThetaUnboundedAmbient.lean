/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.TanThetaWholeSpace
import DavisKahan.TanTheta.Theorem63UnboundedInfiniteTrial

/-!
# Unbounded ambient single-angle tangent assembly

This file isolates the missing ambient half of the Section 2 `tan Theta`
theorem from the already-proved unbounded directed Theorem 6.3 estimate.

The unbounded/domain-sensitive mathematics stays entirely inside
`Theorem63TrialData`: once the trial block has a bounded residual, the ambient
step is bounded operator geometry.  The lower tangent corner is dominated by
the directed tangent singular-value sequence, the upper corner is its adjoint,
and Davis--Kahan Lemmas 6.1 and 6.2 assemble the two corners without loss.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.ExactTanTheta
open TauCeti.DavisKahan.TanTheta
open TauCeti.ApproximationNumber

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

local instance instCompleteSpaceCoeOfHasOrthogonalProjectionTanThetaUnboundedAmbient
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

omit [CompleteSpace E] in
private theorem comp_eq_mul_unboundedTanThetaAmbient
    (f g : E →L[ℂ] E) : f ∘L g = f * g := rfl

omit [CompleteSpace E] in
private theorem projectionBlock_lower_unboundedTanThetaAmbient
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    paperProjectionBlock Uᗮ U K =
      (1 - U.starProjection) * K * U.starProjection := by
  rw [paperProjectionBlock, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedTanThetaAmbient,
    comp_eq_mul_unboundedTanThetaAmbient, mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_upper_unboundedTanThetaAmbient
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    paperProjectionBlock Uᗮᗮ Uᗮ K =
      U.starProjection * K * (1 - U.starProjection) := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  rw [paperProjectionBlock]
  simp only [hUperp, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedTanThetaAmbient]
  rw [mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_smul_unboundedTanThetaAmbient
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (c : ℂ) (K : E →L[ℂ] E) :
    paperProjectionBlock Ω Γ (c • K) = c • paperProjectionBlock Ω Γ K := by
  ext x
  simp [paperProjectionBlock]

private theorem subtypeL_comp_adjoint_subtypeL_unboundedTanThetaAmbient
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection := by
  rw [Submodule.adjoint_subtypeL]
  rfl

/-- Pure bounded-operator assembly for the ambient tangent theorem.

The hypothesis `hlower` is the only place the unbounded Theorem 6.3 argument
enters: it supplies the sharp lower-corner estimate.  Everything after that is
the same two-corner Lemma-6.1/Lemma-6.2 argument as the bounded source theorem. -/
theorem tanTheta_ambient_all_kyFan_of_lowerCorner
    {H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hH : IsSelfAdjoint H)
    {delta : ℝ} (hdelta : 0 < delta)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (paperProjectionBlock Uᗮ U
            (paperProjectorDifference U V * paperSecantSquared U V)) ≤
        kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H)) :
    ∀ k : ℕ,
      delta * kyFanApproximationGauge k (paperTanAngleOperatorC U V) ≤
        kyFanApproximationGauge k H := by
  intro k
  have hdeltac : ‖((delta : ℝ) : ℂ)‖ = delta := by
    simp [abs_of_pos hdelta]
  set K := paperProjectorDifference U V * paperSecantSquared U V
  have h₀ : ∀ j : ℕ,
      kyFanApproximationGauge j
          (paperProjectionBlock Uᗮ U (((delta : ℝ) : ℂ) • K)) ≤
        kyFanApproximationGauge j (paperProjectionBlock Uᗮ U H) := by
    intro j
    rw [projectionBlock_smul_unboundedTanThetaAmbient,
      kyFanApproximationGauge_smul, hdeltac]
    exact hlower j
  have h₁ : ∀ j : ℕ,
      kyFanApproximationGauge j
          (paperProjectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K)) ≤
        kyFanApproximationGauge j (paperProjectionBlock Uᗮᗮ Uᗮ H) := by
    intro j
    have hleft :
        paperProjectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K) =
          (((delta : ℝ) : ℂ) • paperProjectionBlock Uᗮ U K).adjoint := by
      rw [projectionBlock_smul_unboundedTanThetaAmbient,
        upperCorner_eq_adjoint_lowerCorner htr]
      show ((delta : ℝ) : ℂ) • star (paperProjectionBlock Uᗮ U K) =
        star (((delta : ℝ) : ℂ) • paperProjectionBlock Uᗮ U K)
      rw [star_smul, RCLike.star_def, Complex.conj_ofReal]
    have hright :
        paperProjectionBlock Uᗮᗮ Uᗮ H =
          (paperProjectionBlock Uᗮ U H).adjoint := by
      have hp := isSelfAdjoint_starProjection U
      rw [projectionBlock_upper_unboundedTanThetaAmbient,
        projectionBlock_lower_unboundedTanThetaAmbient]
      show _ = star _
      simp only [star_mul, star_sub, star_one, hp.star_eq, hH.star_eq]
      noncomm_ring
    rw [hleft, hright, kyFanApproximationGauge_adjoint,
      kyFanApproximationGauge_adjoint, kyFanApproximationGauge_smul, hdeltac]
    exact hlower j
  have hcombine := paperLemma61_all_kyFan Uᗮ U
    (((delta : ℝ) : ℂ) • K) (((delta : ℝ) : ℂ) • K) H H h₀ h₁ k
  have hsum :
      paperProjectionBlock Uᗮ U (((delta : ℝ) : ℂ) • K) +
          paperProjectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K) =
        ((delta : ℝ) : ℂ) • paperTanBlockRepresentative U V := by
    rw [paperTanBlockRepresentative, paperDiagonalPair,
      projectionBlock_smul_unboundedTanThetaAmbient,
      projectionBlock_smul_unboundedTanThetaAmbient, ← smul_add]
    rfl
  have hsumH :
      paperProjectionBlock Uᗮ U H + paperProjectionBlock Uᗮᗮ Uᗮ H =
        paperDiagonalPair Uᗮ U H := rfl
  rw [hsum, hsumH, kyFanApproximationGauge_smul, hdeltac] at hcombine
  have hpinch := paperDiagonalPair_all_kyFan_le Uᗮ U H k
  have hmodulus :
      kyFanApproximationGauge k (paperTanAngleOperatorC U V) =
        kyFanApproximationGauge k (paperTanBlockRepresentative U V) := by
    rw [paperTanAngleOperatorC_eq_modulus_blockRepresentative htr]
    exact (ContinuousLinearMap.modulus_hasSameApproximationNumbers
      (paperTanBlockRepresentative U V)).kyFanGauge_eq k
  rw [hmodulus]
  exact hcombine.trans hpinch

/-- Paper-norm form of `tanTheta_ambient_all_kyFan_of_lowerCorner`. -/
theorem tanTheta_ambient_paperUINorm_of_lowerCorner
    (N : PaperUnitaryInvariantNorm)
    {H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hH : IsSelfAdjoint H)
    {delta : ℝ} (hdelta : 0 < delta)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (paperProjectionBlock Uᗮ U
            (paperProjectorDifference U V * paperSecantSquared U V)) ≤
        kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H))
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H :=
  N.mul_gauge_le_of_all_mul_kyFan_le hdelta hMem
    (tanTheta_ambient_all_kyFan_of_lowerCorner hH hdelta htr hlower)

/-- **Unbounded-data ambient `tan Theta` theorem, complex form.**

`data` is the bounded trial-block data extracted from an unbounded self-adjoint
problem.  Its residual is assumed to be exactly the lower `U -> U-perp` block of
the bounded perturbation `H`; this is the operator form of the printed
Rayleigh--Ritz condition `H_0 = 0`.  The form bounds are precisely the two
inputs already consumed by the unbounded arbitrary-trial Theorem 6.3 chain.

The conclusion is the missing sharp ambient inequality
`delta * N(tan Theta) <= N(H)` for every paper unitary-invariant norm. -/
theorem tanTheta_unbounded_ambient_paperUINorm_of_data
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (data : Theorem63TrialData U V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompression : ∀ z : U,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : U,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : U) : E)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : U) : E),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (h35 : DavisKahan.Frontier.CrossedDefectsEquivalent U V)
    (hResidual :
      data.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H := by
  have hdirected :
      approximationSingularValue 0 (theorem63DirectedSineBlock U V) < 1 :=
    data.approximationSingularValue_sineBlock_lt_one_infiniteData
      hdelta hCompression hcross 0
  have hambient : ‖paperDirectedSineAmbient U V‖ < 1 := by
    have h := approximationNumber_paperDirectedSineAmbient_le (U := U) (V := V) 0
    rw [(paperDirectedSineAmbient U V).approximationNumber_index_zero] at h
    exact lt_of_le_of_lt h hdirected
  have htr : ‖sinAngleOperatorC U V‖ < 1 := by
    rw [norm_sinAngleOperatorC U V,
      DavisKahan.Frontier.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent
        U V h35]
    exact hambient
  have hblock :
      paperProjectionBlock Uᗮ U H =
        data.residual ∘L U.subtypeL.adjoint := by
    rw [hResidual, paperProjectionBlock]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    have hproj :
        U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection :=
      subtypeL_comp_adjoint_subtypeL_unboundedTanThetaAmbient U
    have happ := congrArg (fun L : E →L[ℂ] E => L x) hproj
    simpa only [ContinuousLinearMap.comp_apply] using
      (congrArg (fun y : E => Uᗮ.starProjection (H y)) happ).symm
  have hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (paperProjectionBlock Uᗮ U
            (paperProjectorDifference U V * paperSecantSquared U V)) ≤
        kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H) := by
    intro k
    have hcorner := kyFan_lowerCorner_le (U := U) (V := V) htr k
    have hcore := data.all_kyFan_core_of_formBounds_infinite
      hdelta hCompression hcross k
    have hresKy :
        kyFanApproximationGauge k data.residual =
          kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H) := by
      rw [hblock]
      have hs := sameApproximationSingularValues_extendDomainByZero U data.residual
      exact (hs.kyFanApproximationGauge_eq k).symm
    calc
      delta * kyFanApproximationGauge k
          (paperProjectionBlock Uᗮ U
            (paperProjectorDifference U V * paperSecantSquared U V))
          ≤ delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
              (approximationSingularValue n (theorem63DirectedSineBlock U V))) :=
        mul_le_mul_of_nonneg_left hcorner hdelta.le
      _ ≤ kyFanApproximationGauge k data.residual := hcore
      _ = kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H) := hresKy
  exact tanTheta_ambient_paperUINorm_of_lowerCorner N hH hdelta htr hlower hMem

/-- The same theorem specialized to an actual unbounded trial block and an
arbitrary chosen reducing subspace.  All domain-sensitive crossed-form work is
reused from the already-proved unbounded Theorem 6.3 implementation. -/
theorem tanTheta_unbounded_ambient_paperUINorm_exact
    (N : PaperUnitaryInvariantNorm)
    (A : DKClosedOperator (H := E))
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : UnboundedTrialBlock A U)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A.toLinearMap x) =
        A.toLinearMap ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hCompression : ∀ z : U,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤
        RCLike.re ⟪A.toLinearMap ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.Frontier.CrossedDefectsEquivalent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H := by
  let data := Theorem63TrialData.ofUnbounded D V
  refine tanTheta_unbounded_ambient_paperUINorm_of_data N data H hH hdelta
    hCompression ?_ h35 ?_ hMem
  · intro z
    exact crossed_lower_of_reducing A D V hVdom hVcomm hUnwanted z
  · exact hResidual

end

end DavisKahan1970
end TauCeti
