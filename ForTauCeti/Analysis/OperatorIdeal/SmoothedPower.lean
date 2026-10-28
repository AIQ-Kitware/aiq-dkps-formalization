/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.SmoothedPowerScalar
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence
public import ForTauCeti.Analysis.OperatorIdeal.OrthogonalExtension
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# The extended smoothed-power spectral cost and its native ideal

The baseline is subtracted inside each summand. Positive smoothing and any
positive subquadratic power give finite cost exactly on the accepted
Hilbert--Schmidt ideal. At zero smoothing the cost is the accepted Schatten
power. These are cost identities and feasibility ingredients, not new norms
or optimizer classifications. The scalar comparison and ideal ingredients
are classical; transport applications are tracked separately in the
unification/provenance note.
-/

public section
noncomputable section

namespace TauCeti

open scoped ENNReal NNReal

/-- The common scalar penalty is increasing on nonnegative singular values. -/
theorem monotone_smoothedPower_scalar (p tau : ℝ) (hp : 0 ≤ p) :
    Monotone (fun s : ℝ≥0 => ENNReal.ofReal ((tau ^ 2 + (s : ℝ) ^ 2) ^ (p / 2) - tau ^ p)) := by
  intro s t hst
  apply ENNReal.ofReal_le_ofReal
  apply sub_le_sub_right
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  nlinarith [s.coe_nonneg, t.coe_nonneg]

/-- Nonnegativity includes the exact zero singular value. -/
theorem smoothedPower_scalar_nonneg (p tau s : ℝ)
    (hp : 0 ≤ p) (htau : 0 ≤ tau) :
    0 ≤ (tau ^ 2 + s ^ 2) ^ (p / 2) - tau ^ p := by
  have hnorm : (tau ^ 2) ^ (p / 2) = tau ^ p := by
    have h := smoothedPower_scalar_zero p tau htau
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, sub_eq_zero] using h
  rw [← hnorm, sub_nonneg]
  exact Real.rpow_le_rpow (sq_nonneg tau) (by nlinarith [sq_nonneg s]) (by linarith)

end TauCeti

namespace ContinuousLinearMap

open scoped ENNReal NNReal

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The literal extended family spectral sum. Renormalization occurs
inside each summand, so no subtraction of infinite traces is used. -/
@[expose] def smoothedPowerCost (p tau : ℝ) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal ((tau ^ 2 + (T.singularValue n : ℝ) ^ 2) ^ (p / 2) - tau ^ p)

/-- Orthogonal zero extensions preserve the extended spectral cost. -/
theorem smoothedPowerCost_orthogonal_extension (p tau : ℝ)
    (M : Submodule 𝕜 E) (N : Submodule 𝕜 F)
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection] (T : M →L[𝕜] N) :
    (N.subtypeL ∘L T ∘L M.orthogonalProjectionOnto).smoothedPowerCost p tau =
      T.smoothedPowerCost p tau := by
  simp only [smoothedPowerCost, singularValue_orthogonal_extension]

/-- The literal finite spectral sum agrees with the extended cost. -/
theorem smoothedPowerCost_eq_ofReal_sum (p tau : ℝ) (hp : 0 ≤ p) (htau : 0 ≤ tau)
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (T : E →L[𝕜] F) :
    T.smoothedPowerCost p tau = ENNReal.ofReal
      (∑ i : Fin (Module.finrank 𝕜 E),
        ((tau ^ 2 + (T.toLinearMap.singularValues i) ^ 2) ^ (p / 2) - tau ^ p)) := by
  rw [smoothedPowerCost, TauCeti.OperatorIdealFamily.tsum_singularValue_penalty_eq_sum T
    (fun s => ENNReal.ofReal ((tau ^ 2 + (s : ℝ) ^ 2) ^ (p / 2) - tau ^ p))
    (by rw [NNReal.coe_zero, TauCeti.smoothedPower_scalar_zero p tau htau, ENNReal.ofReal_zero])]
  simp_rw [singularValue_eq_linearMap_singularValues]
  exact (ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    TauCeti.smoothedPower_scalar_nonneg p tau _ hp htau)).symm

/-- The extended cost is lower semicontinuous in operator norm,
including divergent values. No ideal-topology convergence is asserted. -/
theorem lowerSemicontinuous_smoothedPowerCost (p tau : ℝ) (hp : 0 ≤ p) :
    LowerSemicontinuous (fun T : E →L[𝕜] F => T.smoothedPowerCost p tau) := by
  apply lowerSemicontinuous_tsum
  intro n
  have hs : Continuous (fun T : E →L[𝕜] F => (T.singularValue n : ℝ)) :=
    NNReal.continuous_coe.comp (continuous_singularValue n)
  exact (ENNReal.continuous_ofReal.comp
    (((continuous_const.add (hs.pow 2)).rpow_const
      (fun _ => Or.inr (by linarith : 0 ≤ p / 2))).sub continuous_const)).lowerSemicontinuous

variable [CompleteSpace E] [CompleteSpace F]

/-- A finite multiple of the extended family cost bounds native
Hilbert--Schmidt energy, without compactness or finite-cost assumptions. -/
theorem schatten_two_sq_le_mul_smoothedPowerCost (p tau : ℝ)
    (hp : 0 < p) (hp2 : p ≤ 2) (htau : 0 < tau) (T : E →L[𝕜] F) :
    (TauCeti.OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge T ^ (2 : ℝ) ≤
      ENNReal.ofReal (((p / 2) * (tau ^ 2 + ‖T‖ ^ 2) ^ (p / 2 - 1))⁻¹) *
        T.smoothedPowerCost p tau := by
  let a := (p / 2) * (tau ^ 2 + ‖T‖ ^ 2) ^ (p / 2 - 1)
  have ha : 0 < a := mul_pos (by linarith)
    (Real.rpow_pos_of_pos (by nlinarith [sq_pos_of_pos htau, sq_nonneg ‖T‖]) _)
  rw [TauCeti.OperatorIdealFamily.gauge_schatten_rpow, smoothedPowerCost,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  have hs : 0 ≤ (T.singularValue n : ℝ) := NNReal.coe_nonneg _
  have hsM : (T.singularValue n : ℝ) ≤ ‖T‖ := by exact_mod_cast T.singularValue_le_nnnorm n
  have hlow := (TauCeti.smoothedPower_quadratic_bounds p tau _ ‖T‖ hp hp2 htau hs hsM).1
  have hscaled : (T.singularValue n : ℝ) ^ 2 ≤
      a⁻¹ * ((tau ^ 2 + (T.singularValue n : ℝ) ^ 2) ^ (p / 2) - tau ^ p) := by
    calc
      _ = a⁻¹ * (a * (T.singularValue n : ℝ) ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr ha.le)
  have h := ENNReal.ofReal_le_ofReal hscaled
  rw [ENNReal.ofReal_pow hs, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)] at h
  simpa only [ENNReal.rpow_two] using h

/-- The native Hilbert--Schmidt energy bounds the family cost from above. -/
theorem smoothedPowerCost_le_mul_schatten_two_sq (p tau : ℝ)
    (hp : 0 < p) (hp2 : p ≤ 2) (htau : 0 < tau) (T : E →L[𝕜] F) :
    T.smoothedPowerCost p tau ≤ ENNReal.ofReal ((p / 2) * (tau ^ 2) ^ (p / 2 - 1)) *
      (TauCeti.OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge T ^ (2 : ℝ) := by
  rw [TauCeti.OperatorIdealFamily.gauge_schatten_rpow, smoothedPowerCost,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  have hs : 0 ≤ (T.singularValue n : ℝ) := NNReal.coe_nonneg _
  have hsM : (T.singularValue n : ℝ) ≤ ‖T‖ := by exact_mod_cast T.singularValue_le_nnnorm n
  have h := ENNReal.ofReal_le_ofReal
    (TauCeti.smoothedPower_quadratic_bounds p tau _ ‖T‖ hp hp2 htau hs hsM).2
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hs, ENNReal.ofReal_coe_nnreal] at h
  simpa only [ENNReal.rpow_two] using h

/-- **The exact ideal domain of the positively smoothed family.** Both
fields, arbitrary Hilbert dimension and infinite-rank operators are included. -/
theorem smoothedPowerCost_ne_top_iff_schatten_two (p tau : ℝ)
    (hp : 0 < p) (hp2 : p ≤ 2) (htau : 0 < tau) (T : E →L[𝕜] F) :
    T.smoothedPowerCost p tau ≠ ∞ ↔
      (TauCeti.OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge T ≠ ∞ := by
  constructor
  · intro hcost htop
    have h := T.schatten_two_sq_le_mul_smoothedPowerCost p tau hp hp2 htau
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcost) (top_unique h)
  · intro hT
    have hsquare :
        (TauCeti.OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge T ^ (2 : ℝ) ≠ ∞ := by
      rw [ENNReal.rpow_two, pow_two]
      exact ENNReal.mul_ne_top hT hT
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsquare)
      (T.smoothedPowerCost_le_mul_schatten_two_sq p tau hp hp2 htau)

/-- Zero smoothing is exactly the accepted Schatten power, including
nuclear and quadratic endpoints. This is an extended-cost identity. -/
theorem smoothedPowerCost_zero_smoothing (p : ℝ) (hp : 1 ≤ p) (T : E →L[𝕜] F) :
    T.smoothedPowerCost p 0 = (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge T ^ p := by
  rw [TauCeti.OperatorIdealFamily.gauge_schatten_rpow, smoothedPowerCost]
  apply tsum_congr
  intro n
  have hs : 0 ≤ (T.singularValue n : ℝ) := NNReal.coe_nonneg _
  have hpow : ((T.singularValue n : ℝ) ^ 2) ^ (p / 2) = (T.singularValue n : ℝ) ^ p := by
    rw [← Real.rpow_natCast_mul hs]
    congr 1
    norm_num
    ring
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    Real.zero_rpow (by linarith : p ≠ 0), sub_zero, hpow]
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg hs (by linarith)]
/-- Finite family cost forces compactness at every closed parameter,
using the native Schatten ideal at zero smoothing and S2 otherwise. -/
theorem isCompactOperator_of_smoothedPowerCost_ne_top (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau) (T : E →L[𝕜] F)
    (hfinite : T.smoothedPowerCost p tau ≠ ∞) : IsCompactOperator T := by
  by_cases hz : tau = 0
  · subst tau
    rw [smoothedPowerCost_zero_smoothing p hp] at hfinite
    have hgauge : (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge T ≠ ∞ := by
      intro htop
      rw [htop, ENNReal.top_rpow_of_pos (by linarith : 0 < p)] at hfinite
      exact hfinite rfl
    exact TauCeti.OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p hp T hgauge
  · have hSp := (smoothedPowerCost_ne_top_iff_schatten_two p tau
      (by linarith) hp2 (lt_of_le_of_ne htau (Ne.symm hz)) T).mp hfinite
    exact TauCeti.OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
      2 (by norm_num) T hSp


end ContinuousLinearMap
