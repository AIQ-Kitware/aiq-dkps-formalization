/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSpectralCost
public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierGradientHilbert

/-!
# Actual first variations of Charbonnier displacement

The literal singular-value objective has a self-adjoint phase gradient
along every Hermitian exponential variation. The proof differentiates
the normal spectral trace, so eigenvalue collisions and zero displacement
singular values need no exclusions.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The literal singular-value Charbonnier cost is a normal spectral trace. -/
theorem smoothedDisplacementCost_eq_re_trace_cfc
    (tau : ℝ) (W : E →L[ℂ] E) [IsStarNormal W] :
    smoothedDisplacementCost tau W.toLinearMap =
      (LinearMap.trace ℂ E
        (cfc (fun z => (charbonnierDisplacementSymbol tau z : ℂ)) W).toLinearMap).re := by
  let := ContinuousLinearMap.isStarNormal_toLinearMap W
  obtain ⟨e, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal W.toLinearMap
      (ι := Fin (Module.finrank ℂ E)) (by simp)
  have hD (i) : ((LinearMap.id : E →ₗ[ℂ] E) - W.toLinearMap) (e i) =
      (1 - mu i) • e i := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, hmu, sub_smul, one_smul]
  rw [smoothedDisplacementCost, sum_singularValues_eq_sum_norm_eigenvalues e _ _ hD
    (fun s : ℝ => Real.sqrt (tau ^ 2 + s ^ 2) - tau),
    ContinuousLinearMap.re_trace_cfc_eq_sum (charbonnierDisplacementSymbol tau) W e mu hmu]
  apply Finset.sum_congr rfl
  intro i _
  simp only [charbonnierDisplacementSymbol, norm_sub_rev]

/-- Every Hermitian right variation has the actual Charbonnier phase-gradient
derivative at every time, including at zero displacement. -/
theorem hasDerivAt_smoothed_unitary_right_variation_at
    (tau : ℝ) (htau : 0 < tau)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => smoothedDisplacementCost tau
        ((U : E →L[ℂ] E) * NormedSpace.exp (s • (Complex.I • H))).toLinearMap)
      (LinearMap.trace ℂ E
        (smoothedUnitaryGradient tau ((U : E →L[ℂ] E) *
          NormedSpace.exp (t • (Complex.I • H))) * H).toLinearMap).re t := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  have hd := hasDerivAt_unitary_spectral_right_variation_at
    (charbonnierDisplacementSymbol tau) (charbonnierDisplacementGradient tau)
    (continuous_charbonnierDisplacementGradient tau htau).continuousOn
    (fun z _ w _ => charbonnierDisplacement_support tau htau z w) U H hH t
  apply hd.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro s
  have hu : (U : E →L[ℂ] E) * NormedSpace.exp (s • (Complex.I • H)) ∈
      unitary (E →L[ℂ] E) := by
    apply mul_mem U.2
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  let := isStarNormal_of_mem_unitary hu
  exact smoothedDisplacementCost_eq_re_trace_cfc tau _

/-- The first variation at the initial unitary. -/
theorem hasDerivAt_smoothed_unitary_right_variation
    (tau : ℝ) (htau : 0 < tau)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) :
    HasDerivAt
      (fun t : ℝ => smoothedDisplacementCost tau
        ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))).toLinearMap)
      (LinearMap.trace ℂ E
        (smoothedUnitaryGradient tau (U : E →L[ℂ] E) * H).toLinearMap).re 0 := by
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one] using
    hasDerivAt_smoothed_unitary_right_variation_at tau htau U H hH 0

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
