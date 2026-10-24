/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPhaseMinimum
public import ForTauCeti.Analysis.InnerProductSpace.NuclearTrace
public import Mathlib.Analysis.CStarAlgebra.Unitary.Maps

/-!
# Smoothed displacement as a weighted nuclear norm

The literal Charbonnier sum over displacement singular values agrees with
a weighted nuclear norm whenever the transported operator is unitary.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

private theorem weighted_unit_circle_norm_sq (a b : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(a : ℂ) * z - b‖ ^ 2 = (a - b) ^ 2 + a * b * ‖z - 1‖ ^ 2 := by
  have hzsq := congrArg (fun x : ℝ => x ^ 2) hz
  simp only [Complex.sq_norm, Complex.normSq_apply, one_pow] at hzsq
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, zero_mul, sub_zero]
  nlinarith [congrArg (fun x : ℝ => a * (a - b) * x) hzsq]

/-- The smoothing-radius change of variables is an exact identity on the
unit circle, including at the identity. -/
theorem smoothingRadius_norm_identity (tau : ℝ) (hτ : 0 < tau) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(smoothingRadius tau : ℂ) * z - ((smoothingRadius tau)⁻¹ : ℝ)‖ =
      Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2) := by
  have ha : 0 < smoothingRadius tau := lt_trans zero_lt_one (one_lt_smoothingRadius tau hτ)
  have hprod : smoothingRadius tau * (smoothingRadius tau)⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  rw [← Real.sqrt_sq (norm_nonneg
    ((smoothingRadius tau : ℂ) * z - ((smoothingRadius tau)⁻¹ : ℝ)))]
  congr 1
  rw [weighted_unit_circle_norm_sq _ _ z hz, smoothingRadius_sub_inv tau hτ, hprod, one_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The literal Charbonnier sum of the displacement singular values. -/
@[expose]
def smoothedDisplacementCost (tau : ℝ) (W : E →ₗ[ℂ] E) : ℝ :=
  ∑ i : Fin (Module.finrank ℂ E),
    (Real.sqrt (tau ^ 2 + ((LinearMap.id - W).singularValues i) ^ 2) - tau)

/-- On the full unitary group, the literal smoothed displacement cost is
exactly a weighted nuclear distance, including all zero singular values. -/
theorem smoothedDisplacementCost_eq_weightedNuclear [CompleteSpace E]
    (tau : ℝ) (hτ : 0 < tau) (W : unitary (E →L[ℂ] E)) :
    smoothedDisplacementCost tau (W : E →L[ℂ] E).toLinearMap =
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((smoothingRadius tau : ℂ) • (W : E →L[ℂ] E).toLinearMap -
          (((smoothingRadius tau)⁻¹ : ℝ) : ℂ) • LinearMap.id) -
        Module.finrank ℂ E * tau := by
  let := ContinuousLinearMap.isStarNormal_toLinearMap (W : E →L[ℂ] E)
  obtain ⟨e, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal
      (W : E →L[ℂ] E).toLinearMap (ι := Fin (Module.finrank ℂ E)) (by simp)
  have hnorm (i) : ‖mu i‖ = 1 := by
    have h := _root_.ContinuousLinearMap.norm_map_of_mem_unitary W.2 (e i)
    have hWi : (W : E →L[ℂ] E) (e i) = mu i • e i := hmu i
    rw [hWi, norm_smul, e.norm_eq_one, mul_one] at h
    exact h
  have hD (i) : ((LinearMap.id : E →ₗ[ℂ] E) - (W : E →L[ℂ] E).toLinearMap) (e i) =
      (1 - mu i) • e i := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, hmu, sub_smul, one_smul]
  have hA (i) :
      ((smoothingRadius tau : ℂ) • (W : E →L[ℂ] E).toLinearMap -
          (((smoothingRadius tau)⁻¹ : ℝ) : ℂ) • (LinearMap.id : E →ₗ[ℂ] E)) (e i) =
        ((smoothingRadius tau : ℂ) * mu i - (((smoothingRadius tau)⁻¹ : ℝ) : ℂ)) • e i := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      hmu, smul_smul, sub_smul]
  rw [smoothedDisplacementCost,
    sum_singularValues_eq_sum_norm_eigenvalues e _ (fun i => 1 - mu i) hD
      (fun s : ℝ => Real.sqrt (tau ^ 2 + s ^ 2) - tau),
    nuclear_eq_sum_norm_eigenvalues e _ _ hA]
  calc
    _ = ∑ i, (‖(smoothingRadius tau : ℂ) * mu i -
        (((smoothingRadius tau)⁻¹ : ℝ) : ℂ)‖ - tau) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_sub_rev, ← smoothingRadius_norm_identity tau hτ (mu i) (hnorm i)]
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
