/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedGradientBranches

/-!
# Optimality of distinct balanced Charbonnier phases

Two distinct positive principal phases with equal scalar gradient give
an optimal scalar-phase transporter at their mean angle. The proof uses
the quadratic level equation and the independently proved circle minimum.
It does not infer optimality from stationarity alone.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

/-- Opposite phases have the same literal smoothed displacement. -/
theorem smoothed_eigenphase_cost_neg (tau t : ℝ) :
    Real.sqrt (tau ^ 2 + ‖Complex.exp (((-t : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2) - tau =
      Real.sqrt (tau ^ 2 + ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2) - tau := by
  rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one (Complex.norm_exp_ofReal_mul_I (-t)),
    Complex.norm_sub_one_sq_eq_of_norm_eq_one (Complex.norm_exp_ofReal_mul_I t),
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The canonical phase attains the exact scalar minimum up to and
including the critical angle, with the literal eigenvalue cost. -/
theorem smoothedPhaseMinimum_eq_canonical_of_le_critical
    (tau t : ℝ) (htau : 0 < tau) (ht0 : 0 ≤ t) (ht : t ≤ smoothedCriticalAngle tau) :
    smoothedPhaseMinimum tau t =
      2 * (Real.sqrt (tau ^ 2 + ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2) - tau) := by
  have hc := smoothedCriticalAngle_mem tau htau
  have heta0 : 0 < smoothingRadius tau :=
    zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hcos : ((smoothingRadius tau)⁻¹) ^ 2 ≤ Real.cos t := by
    rw [← cos_smoothedCriticalAngle tau htau]
    exact Real.antitoneOn_cos ⟨ht0, by linarith [hc.2]⟩
      ⟨hc.1.le, by linarith [hc.2]⟩ ht
  have hcanon : (smoothingRadius tau)⁻¹ ≤ smoothingRadius tau * Real.cos t := by
    calc
      _ = smoothingRadius tau * ((smoothingRadius tau)⁻¹) ^ 2 := by
        rw [pow_two, ← mul_assoc, mul_inv_cancel₀ heta0.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcos heta0.le
  rw [smoothedPhaseMinimum, ite_eq_left hcanon,
    Complex.norm_sub_one_sq_eq_of_norm_eq_one (Complex.norm_exp_ofReal_mul_I t),
    Complex.exp_ofReal_mul_I_re]
  congr 3
  ring

private theorem norm_weighted_phase_difference (a b t delta : ℝ) :
    ‖(a : ℂ) * Complex.exp ((t : ℂ) * Complex.I) -
        (b : ℂ) * Complex.exp ((delta : ℂ) * Complex.I)‖ =
      ‖(a : ℂ) * Complex.exp (((t - delta : ℝ) : ℂ) * Complex.I) - b‖ := by
  have hmul (s t : ℝ) :
      Complex.exp ((s : ℂ) * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) =
        Complex.exp (((s + t : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hrot :
      Complex.exp (((-delta : ℝ) : ℂ) * Complex.I) *
        ((a : ℂ) * Complex.exp ((t : ℂ) * Complex.I) -
          (b : ℂ) * Complex.exp ((delta : ℂ) * Complex.I)) =
        (a : ℂ) * (Complex.exp (((-delta : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((t : ℂ) * Complex.I)) -
        (b : ℂ) * (Complex.exp (((-delta : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((delta : ℂ) * Complex.I)) := by ring
  calc
    _ = ‖Complex.exp (((-delta : ℝ) : ℂ) * Complex.I) *
        ((a : ℂ) * Complex.exp ((t : ℂ) * Complex.I) -
          (b : ℂ) * Complex.exp ((delta : ℂ) * Complex.I))‖ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    _ = _ := by
      rw [hrot, hmul, hmul, neg_add_cancel, Complex.ofReal_zero,
        zero_mul, Complex.exp_zero, mul_one]
      rw [show -delta + t = t - delta by ring]

/-- The circle-geometry phase cost is exactly the sum of the two literal
smoothed eigenvalue displacements, for every pair of real phases. -/
theorem smoothedPhaseCost_eq_displacement_sum (tau theta delta : ℝ) (htau : 0 < tau) :
    smoothedPhaseCost tau theta delta =
      (Real.sqrt (tau ^ 2 +
        ‖Complex.exp (((theta - delta : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2) - tau) +
      (Real.sqrt (tau ^ 2 +
        ‖Complex.exp (((-theta - delta : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2) - tau) := by
  have hp :
      ((smoothingRadius tau * Real.cos theta : ℝ) : ℂ) +
        ((smoothingRadius tau * Real.sin theta : ℝ) : ℂ) * Complex.I =
        (smoothingRadius tau : ℂ) * Complex.exp ((theta : ℂ) * Complex.I) := by
    rw [Complex.exp_ofReal_mul_I]
    push_cast
    ring
  have hm :
      ((smoothingRadius tau * Real.cos theta : ℝ) : ℂ) -
        ((smoothingRadius tau * Real.sin theta : ℝ) : ℂ) * Complex.I =
        (smoothingRadius tau : ℂ) * Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [smoothedPhaseCost, weightedPhaseCost, twoFocusCost, hp, hm, circlePhase,
    norm_weighted_phase_difference, norm_weighted_phase_difference,
    smoothingRadius_norm_identity tau htau _ (Complex.norm_exp_ofReal_mul_I _),
    smoothingRadius_norm_identity tau htau _ (Complex.norm_exp_ofReal_mul_I _)]
  ring

/-- Distinct balanced positive phases have an acute mean angle, and half
their difference is exactly its attaining Charbonnier phase. -/
theorem balanced_roots_optimalSmoothedPhase
    (tau a b : ℝ) (htau : 0 < tau) (ha : 0 < a) (hab : a < b)
    (hb : b < Real.pi)
    (hlevel : smoothedPhaseDerivative tau (Complex.exp ((a : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((b : ℂ) * Complex.I))) :
    (a + b) / 2 ∈ Set.Ioo 0 (Real.pi / 2) ∧
      (b - a) / 2 = optimalSmoothedPhase tau ((a + b) / 2) := by
  let g := smoothedPhaseDerivative tau (Complex.exp ((a : ℂ) * Complex.I))
  have hg : 0 < g := by
    dsimp only [g]
    rw [smoothedPhaseDerivative_exp]
    apply div_pos (Real.sin_pos_of_pos_of_lt_pi ha (hab.trans hb))
    apply Real.sqrt_pos.mpr
    nlinarith [Real.cos_le_one a, sq_pos_of_pos htau]
  have hqa := smoothedPhaseDerivative_level_quadratic tau htau g
    (Complex.exp ((a : ℂ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I a) rfl
  have hqb := smoothedPhaseDerivative_level_quadratic tau htau g
    (Complex.exp ((b : ℂ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I b) hlevel.symm
  rw [Complex.exp_ofReal_mul_I_re] at hqa hqb
  have hcos : Real.cos b < Real.cos a := Real.strictAntiOn_cos
    ⟨ha.le, (hab.trans hb).le⟩ ⟨(ha.trans hab).le, hb.le⟩ hab
  have hvieta : (Real.cos a - Real.cos b) *
      (Real.cos a + Real.cos b - 2 * g ^ 2) = 0 := by
    linear_combination hqa - hqb
  have hsum : Real.cos a + Real.cos b = 2 * g ^ 2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hvieta).resolve_left (sub_pos.mpr hcos).ne')
  have hprod : Real.cos a * Real.cos b = (tau ^ 2 + 2) * g ^ 2 - 1 := by
    linear_combination Real.cos a * hsum - hqa
  let theta := (a + b) / 2
  let delta := (b - a) / 2
  have ha' : a = theta - delta := by dsimp [theta, delta]; ring
  have hb' : b = theta + delta := by dsimp [theta, delta]; ring
  have htheta0 : 0 < theta := by dsimp [theta]; linarith
  have hthetaPi : theta < Real.pi := by dsimp [theta]; linarith
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdeltaHalfPi : delta < Real.pi / 2 := by dsimp [delta]; linarith
  have hdeltaTheta : delta < theta := by dsimp [delta, theta]; linarith
  have hctcd : Real.cos theta * Real.cos delta = g ^ 2 := by
    rw [ha', hb', Real.cos_sub, Real.cos_add] at hsum
    linarith
  have hct : 0 < Real.cos theta :=
    (mul_pos_iff_of_pos_right (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], hdeltaHalfPi⟩)).mp
        (by rw [hctcd]; exact sq_pos_of_pos hg)
  have hthetaHalfPi : theta < Real.pi / 2 := by
    by_contra hnot
    have hle := Real.antitoneOn_cos
      (show Real.pi / 2 ∈ Set.Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos])
      ⟨htheta0.le, hthetaPi.le⟩ (le_of_not_gt hnot)
    rw [Real.cos_pi_div_two] at hle
    exact (not_le_of_gt hct) hle
  have htrig : Real.cos a * Real.cos b =
      Real.cos theta ^ 2 + Real.cos delta ^ 2 - 1 := by
    rw [ha', hb', Real.cos_sub, Real.cos_add]
    linear_combination (Real.cos delta ^ 2 - 1) * Real.sin_sq_add_cos_sq theta -
      Real.sin theta ^ 2 * Real.sin_sq_add_cos_sq delta
  have hsumtrig : Real.cos theta ^ 2 + Real.cos delta ^ 2 =
      (tau ^ 2 + 2) * (Real.cos theta * Real.cos delta) := by
    rw [hctcd]
    linarith
  have heta := one_lt_smoothingRadius tau htau
  have heta0 : 0 < smoothingRadius tau := zero_lt_one.trans heta
  have hradius := smoothingRadius_sq_add_inv_sq tau htau
  have hradiusProd : smoothingRadius tau ^ 2 * ((smoothingRadius tau)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ heta0.ne', one_pow]
  have hfactor :
      (Real.cos delta - smoothingRadius tau ^ 2 * Real.cos theta) *
        (Real.cos delta - ((smoothingRadius tau)⁻¹) ^ 2 * Real.cos theta) = 0 := by
    linear_combination hsumtrig - (Real.cos theta * Real.cos delta) * hradius +
      Real.cos theta ^ 2 * hradiusProd
  have hcoslt : Real.cos theta < Real.cos delta := Real.strictAntiOn_cos
    ⟨hdelta0.le, (hdeltaHalfPi.trans (by linarith [Real.pi_pos])).le⟩
    ⟨htheta0.le, hthetaPi.le⟩ hdeltaTheta
  have hinv : (smoothingRadius tau)⁻¹ < 1 := (inv_lt_one₀ heta0).mpr heta
  have hinv0 : 0 < (smoothingRadius tau)⁻¹ := inv_pos.mpr heta0
  have hcosdelta : Real.cos delta = smoothingRadius tau ^ 2 * Real.cos theta := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact sub_eq_zero.mp h
    · have heq := sub_eq_zero.mp h
      have hsmall : ((smoothingRadius tau)⁻¹) ^ 2 < 1 := by nlinarith
      nlinarith
  have hcosdelta1 : Real.cos delta < 1 := by
    simpa only [Real.cos_zero] using Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
      ⟨hdelta0.le, (hdeltaHalfPi.trans (by linarith [Real.pi_pos])).le⟩ hdelta0
  have hsuper : smoothingRadius tau * Real.cos theta < (smoothingRadius tau)⁻¹ := by
    apply (mul_lt_mul_iff_right₀ heta0).mp
    calc
      smoothingRadius tau * (smoothingRadius tau * Real.cos theta) =
          Real.cos delta := by nlinarith only [hcosdelta]
      _ < 1 := hcosdelta1
      _ = smoothingRadius tau * (smoothingRadius tau)⁻¹ := (mul_inv_cancel₀ heta0.ne').symm
  refine ⟨⟨htheta0, hthetaHalfPi⟩, ?_⟩
  change delta = optimalWeightedPhase (smoothingRadius tau) (smoothingRadius tau)⁻¹ theta
  rw [optimalWeightedPhase, ite_eq_right (not_le_of_gt hsuper)]
  have hr : smoothingRadius tau * Real.cos theta / (smoothingRadius tau)⁻¹ =
      Real.cos delta := by
    rw [div_inv_eq_mul, hcosdelta]
    ring
  rw [hr, Real.arccos_cos hdelta0.le (hdeltaHalfPi.trans (by linarith [Real.pi_pos])).le]

/-- Distinct balanced positive phases attain the exact global scalar
minimum at their mean principal angle. -/
theorem balanced_roots_smoothedPhaseMinimum
    (tau a b : ℝ) (htau : 0 < tau) (ha : 0 < a) (hab : a < b)
    (hb : b < Real.pi)
    (hlevel : smoothedPhaseDerivative tau (Complex.exp ((a : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((b : ℂ) * Complex.I))) :
    (a + b) / 2 ∈ Set.Ioo 0 (Real.pi / 2) ∧
      (Real.sqrt (tau ^ 2 + ‖Complex.exp ((a : ℂ) * Complex.I) - 1‖ ^ 2) - tau) +
        (Real.sqrt (tau ^ 2 + ‖Complex.exp (((-b : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2) - tau) =
          smoothedPhaseMinimum tau ((a + b) / 2) := by
  obtain ⟨htheta, hphase⟩ := balanced_roots_optimalSmoothedPhase tau a b htau ha hab hb hlevel
  refine ⟨htheta, ?_⟩
  have hcost := smoothedPhaseCost_optimal tau ((a + b) / 2) htau
    ⟨htheta.1.le, htheta.2.le⟩
  rw [← hphase, smoothedPhaseCost_eq_displacement_sum tau _ _ htau,
    show (a + b) / 2 - (b - a) / 2 = a by ring,
    show -((a + b) / 2) - (b - a) / 2 = -b by ring] at hcost
  exact hcost

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
