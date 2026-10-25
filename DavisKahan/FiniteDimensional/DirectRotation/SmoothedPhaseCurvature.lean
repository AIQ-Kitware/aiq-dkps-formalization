/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedUnitaryVariation
public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierPhaseSymbol

/-!
# Curvature of the Charbonnier phase cost

The phase gradient is differentiable at every real phase for positive
smoothing. Its curvature changes sign at the exact critical real part,
and it remains finite at both the identity and reflection endpoints.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

/-- The phase gradient in angular coordinates. -/
theorem smoothedPhaseDerivative_exp (tau theta : ℝ) :
    smoothedPhaseDerivative tau (Complex.exp ((theta : ℂ) * Complex.I)) =
      Real.sin theta / Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta) := by
  rw [smoothedPhaseDerivative_eq, Complex.norm_sub_one_sq_eq_of_norm_eq_one
    (Complex.norm_exp_ofReal_mul_I theta), Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  congr 2
  ring

/-- The angular gradient is odd. -/
theorem smoothedPhaseDerivative_exp_neg (tau theta : ℝ) :
    smoothedPhaseDerivative tau (Complex.exp (((-theta : ℝ) : ℂ) * Complex.I)) =
      -smoothedPhaseDerivative tau (Complex.exp ((theta : ℂ) * Complex.I)) := by
  simp only [smoothedPhaseDerivative_exp, Real.sin_neg, Real.cos_neg, neg_div]

/-- Curvature of the scalar smoothed displacement phase cost. -/
@[expose] def smoothedPhaseCurvature (tau theta : ℝ) : ℝ :=
  ((tau ^ 2 + 2) * Real.cos theta - (Real.cos theta) ^ 2 - 1) /
    ((tau ^ 2 + 2 - 2 * Real.cos theta) *
      Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta))

/-- The scalar gradient derivative exists at every phase, including zero. -/
theorem hasDerivAt_smoothedPhaseDerivative_exp
    (tau theta : ℝ) (htau : 0 < tau) :
    HasDerivAt
      (fun t : ℝ => smoothedPhaseDerivative tau (Complex.exp ((t : ℂ) * Complex.I)))
      (smoothedPhaseCurvature tau theta) theta := by
  have hrad : 0 < tau ^ 2 + 2 - 2 * Real.cos theta := by
    nlinarith [Real.cos_le_one theta, sq_pos_of_pos htau]
  have hr : 0 < Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta) := Real.sqrt_pos.mpr hrad
  have hder : HasDerivAt (fun t => tau ^ 2 + 2 - 2 * Real.cos t)
      (2 * Real.sin theta) theta := by
    convert (hasDerivAt_const theta (tau ^ 2 + 2)).sub
      ((Real.hasDerivAt_cos theta).const_mul 2) using 1
    ring
  have hd := (Real.hasDerivAt_sin theta).div (hder.sqrt hrad.ne') hr.ne'
  have hcoeff :
      (Real.cos theta * Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta) -
        Real.sin theta * (2 * Real.sin theta /
          (2 * Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta)))) /
        Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta) ^ 2 =
      smoothedPhaseCurvature tau theta := by
    let r := Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta)
    have hrsq : r ^ 2 = tau ^ 2 + 2 - 2 * Real.cos theta := Real.sq_sqrt hrad.le
    have hr0 : r ≠ 0 := hr.ne'
    have hnum : Real.cos theta * r ^ 2 - Real.sin theta ^ 2 =
        (tau ^ 2 + 2) * Real.cos theta - Real.cos theta ^ 2 - 1 := by
      rw [hrsq]
      nlinarith [Real.sin_sq_add_cos_sq theta]
    change (Real.cos theta * r - Real.sin theta * (2 * Real.sin theta / (2 * r))) /
      r ^ 2 = _
    calc
      _ = (Real.cos theta * r ^ 2 - Real.sin theta ^ 2) / (r ^ 2 * r) := by
        field_simp [hr0]
      _ = _ := by rw [hnum, hrsq]; rfl
  exact (hd.congr_deriv hcoeff).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => smoothedPhaseDerivative_exp tau t)

/-- Changing the sign of the phase leaves curvature unchanged. -/
theorem smoothedPhaseCurvature_neg (tau theta : ℝ) :
    smoothedPhaseCurvature tau (-theta) = smoothedPhaseCurvature tau theta := by
  simp only [smoothedPhaseCurvature, Real.cos_neg]

/-- Identity has strictly positive phase curvature. -/
theorem smoothedPhaseCurvature_zero (tau : ℝ) (htau : 0 < tau) :
    smoothedPhaseCurvature tau 0 = tau⁻¹ := by
  simp only [smoothedPhaseCurvature, Real.cos_zero, one_pow, mul_one]
  rw [show tau ^ 2 + 2 - 2 = tau ^ 2 by ring,
    show tau ^ 2 + 2 - 1 - 1 = tau ^ 2 by ring, Real.sqrt_sq htau.le]
  field_simp

/-- Reflection has strictly negative phase curvature. -/
theorem smoothedPhaseCurvature_pi (tau : ℝ) :
    smoothedPhaseCurvature tau Real.pi = -(Real.sqrt (tau ^ 2 + 4))⁻¹ := by
  simp only [smoothedPhaseCurvature, Real.cos_pi]
  have hden : tau ^ 2 + 2 - 2 * (-1) = tau ^ 2 + 4 := by ring
  rw [hden]
  field_simp
  ring

/-- The scalar curvature has the same sign as the real-part displacement
from the critical threshold. -/
theorem smoothedPhaseCurvature_factor (tau theta : ℝ) (htau : 0 < tau) :
    smoothedPhaseCurvature tau theta =
      (((smoothingRadius tau) ^ 2 - Real.cos theta) *
        (Real.cos theta - ((smoothingRadius tau)⁻¹) ^ 2)) /
      ((tau ^ 2 + 2 - 2 * Real.cos theta) *
        Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta)) := by
  have ha : 0 < smoothingRadius tau := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hprod : (smoothingRadius tau) ^ 2 * ((smoothingRadius tau)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ha.ne', one_pow]
  have hsum := smoothingRadius_sq_add_inv_sq tau htau
  unfold smoothedPhaseCurvature
  congr 1
  nlinarith only [hprod, congrArg (fun r : ℝ => r * Real.cos theta) hsum]

/-- Exact sign of the phase curvature, including the critical level. -/
theorem smoothedPhaseCurvature_pos_iff (tau theta : ℝ) (htau : 0 < tau) :
    0 < smoothedPhaseCurvature tau theta ↔
      ((smoothingRadius tau)⁻¹) ^ 2 < Real.cos theta := by
  have hrad : 0 < tau ^ 2 + 2 - 2 * Real.cos theta := by
    nlinarith [Real.cos_le_one theta, sq_pos_of_pos htau]
  have ha := one_lt_smoothingRadius tau htau
  have hfirst : 0 < (smoothingRadius tau) ^ 2 - Real.cos theta := by
    nlinarith [Real.cos_le_one theta]
  rw [smoothedPhaseCurvature_factor tau theta htau,
    div_pos_iff_of_pos_right (mul_pos hrad (Real.sqrt_pos.mpr hrad)),
    mul_pos_iff_of_pos_left hfirst, sub_pos]

/-- Negative curvature occurs precisely beyond the critical real part. -/
theorem smoothedPhaseCurvature_neg_iff (tau theta : ℝ) (htau : 0 < tau) :
    smoothedPhaseCurvature tau theta < 0 ↔
      Real.cos theta < ((smoothingRadius tau)⁻¹) ^ 2 := by
  have hrad : 0 < tau ^ 2 + 2 - 2 * Real.cos theta := by
    nlinarith [Real.cos_le_one theta, sq_pos_of_pos htau]
  have ha := one_lt_smoothingRadius tau htau
  have hfirst : 0 < (smoothingRadius tau) ^ 2 - Real.cos theta := by
    nlinarith [Real.cos_le_one theta]
  rw [smoothedPhaseCurvature_factor tau theta htau,
    div_lt_iff₀ (mul_pos hrad (Real.sqrt_pos.mpr hrad)), zero_mul]
  constructor
  · intro h
    by_contra hnot
    exact (not_lt_of_ge (mul_nonneg hfirst.le (sub_nonneg.mpr (le_of_not_gt hnot)))) h
  · intro h
    exact mul_neg_of_pos_of_neg hfirst (sub_neg.mpr h)

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
