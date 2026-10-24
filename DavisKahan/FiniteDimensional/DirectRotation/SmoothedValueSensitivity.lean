/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedQuarticStability
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Sharp sensitivity of the exact smoothed transport value

The scalar minimum is Lipschitz on the full principal-angle interval with
least constant `2 / smoothingRadius tau`. Its derivative at the transition
attains this constant. The finite-sum estimate controls the error in the
exact global value from errors in a list of principal angles.

This is the value-sensitivity corollary in the Davis--Kahan journal paper,
a quantitative consequence of the exact minimum formula.
-/

noncomputable section
open scoped NNReal
namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

private def canonicalValueBranch (tau theta : ℝ) : ℝ :=
  2 * (Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta) - tau)

private theorem canonicalValueBranch_hasDerivAt (tau theta : ℝ) (htau : 0 < tau) :
    HasDerivAt (canonicalValueBranch tau)
      (2 * Real.sin theta / Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta)) theta := by
  have hq : 0 < tau ^ 2 + 2 - 2 * Real.cos theta := by
    nlinarith [Real.cos_le_one theta, sq_pos_of_pos htau]
  have hder : HasDerivAt (fun x => tau ^ 2 + 2 - 2 * Real.cos x) (2 * Real.sin theta) theta := by
    convert (hasDerivAt_const theta (tau ^ 2 + 2)).sub ((Real.hasDerivAt_cos theta).const_mul 2) using 1; ring
  convert ((hder.sqrt hq.ne').sub_const tau).const_mul 2 using 1
  · rfl
  · ring

private theorem canonicalValueBranch_deriv_bound (tau theta : ℝ) (htau : 0 < tau)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    ‖2 * Real.sin theta / Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta)‖ ≤
      2 * (smoothingRadius tau)⁻¹ := by
  let a := smoothingRadius tau
  let b := a⁻¹
  let d := Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta)
  have ha : 0 < a := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hb : 0 < b := inv_pos.mpr ha
  have hd : 0 < d := Real.sqrt_pos.mpr (by nlinarith [Real.cos_le_one theta, sq_pos_of_pos htau])
  have hdsq : d ^ 2 = tau ^ 2 + 2 - 2 * Real.cos theta := Real.sq_sqrt (by nlinarith [Real.cos_le_one theta, sq_nonneg tau])
  have hrad : a ^ 2 + b ^ 2 = tau ^ 2 + 2 := smoothingRadius_sq_add_inv_sq tau htau
  have hab : a * b = 1 := mul_inv_cancel₀ ha.ne'
  have hs : 0 ≤ Real.sin theta := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hsq : Real.sin theta ^ 2 ≤ b ^ 2 * d ^ 2 := by
    have hprod : a ^ 2 * b ^ 2 = 1 := by nlinarith [congrArg (fun x : ℝ => x ^ 2) hab]
    have h := congrArg (fun x : ℝ => b ^ 2 * x) hrad
    nlinarith [sq_nonneg (Real.cos theta - b ^ 2), Real.sin_sq_add_cos_sq theta]
  have hsd : Real.sin theta ≤ b * d :=
    (sq_le_sq₀ hs (mul_nonneg hb.le hd.le)).mp (by nlinarith only [hsq])
  change ‖2 * Real.sin theta / d‖ ≤ 2 * b
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hd]
  linarith

private theorem canonicalValueBranch_lipschitz (tau : ℝ) (htau : 0 < tau)
    (x y : ℝ) (hx : x ∈ Set.Icc 0 (Real.pi / 2)) (hy : y ∈ Set.Icc 0 (Real.pi / 2)) :
    ‖canonicalValueBranch tau y - canonicalValueBranch tau x‖ ≤
      2 * (smoothingRadius tau)⁻¹ * ‖y - x‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (canonicalValueBranch_hasDerivAt tau t htau).hasDerivWithinAt)
    (fun t ht => canonicalValueBranch_deriv_bound tau t htau ht)
    (convex_Icc _ _) hx hy

private theorem supercriticalValueBranch_lipschitz (tau : ℝ) (htau : 0 < tau)
    (x y : ℝ) (hx : x ∈ Set.Icc (smoothedCriticalAngle tau) (Real.pi / 2))
    (hy : y ∈ Set.Icc (smoothedCriticalAngle tau) (Real.pi / 2)) :
    ‖(2 * smoothingRadius tau * Real.sin y - 2 * tau) -
        (2 * smoothingRadius tau * Real.sin x - 2 * tau)‖ ≤
      2 * (smoothingRadius tau)⁻¹ * ‖y - x‖ := by
  let a := smoothingRadius tau
  have ha : 0 < a := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hb : 0 < a⁻¹ := inv_pos.mpr ha
  have hc := smoothedCriticalAngle_mem_Icc tau
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (((Real.hasDerivAt_sin t).const_mul (2 * a)).sub_const (2 * tau)).hasDerivWithinAt)
    (fun t ht => ?_) (convex_Icc _ _) hx hy
  have hnonneg : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hc.1, ht.1, Real.pi_pos], ht.2⟩
  have hcos : Real.cos t ≤ a⁻¹ ^ 2 := by
    rw [← cos_smoothedCriticalAngle tau htau]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hc.1 (by linarith [ht.2, Real.pi_pos]) ht.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hnonneg)]
  have hh := mul_le_mul_of_nonneg_left hcos (by positivity : 0 ≤ 2 * a)
  have hid : 2 * a * (a⁻¹ ^ 2) = 2 * a⁻¹ := by field_simp
  simpa only [hid] using hh


private theorem smoothedPhaseMinimum_eq_canonical_of_le
    (tau theta : ℝ) (htau : 0 < tau) (hθ : theta ∈ Set.Icc 0 (Real.pi / 2))
    (hle : theta ≤ smoothedCriticalAngle tau) :
    smoothedPhaseMinimum tau theta = canonicalValueBranch tau theta := by
  let a := smoothingRadius tau
  have ha : 0 < a := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hc := smoothedCriticalAngle_mem_Icc tau
  have hcos : a⁻¹ ^ 2 ≤ Real.cos theta := by
    rw [← cos_smoothedCriticalAngle tau htau]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hθ.1 (by linarith [hc.2, Real.pi_pos]) hle
  have hmul := mul_le_mul_of_nonneg_left hcos ha.le
  have hid : a * (a⁻¹ ^ 2) = a⁻¹ := by field_simp
  rw [hid] at hmul
  rw [smoothedPhaseMinimum, ite_eq_left hmul]
  rfl

private theorem smoothedPhaseMinimum_critical_eq_super (tau : ℝ) (htau : 0 < tau) :
    smoothedPhaseMinimum tau (smoothedCriticalAngle tau) =
      2 * smoothingRadius tau * Real.sin (smoothedCriticalAngle tau) - 2 * tau := by
  let a := smoothingRadius tau
  let b := a⁻¹
  let t := smoothedCriticalAngle tau
  have ha : 0 < a := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hb : 0 < b := inv_pos.mpr ha
  have hab : b ≤ a := (inv_le_one_of_one_le₀ (one_lt_smoothingRadius tau htau).le).trans
    (one_lt_smoothingRadius tau htau).le
  have ht : t ∈ Set.Icc 0 (Real.pi / 2) := smoothedCriticalAngle_mem_Icc tau
  have hreal : a * Real.cos t = b := by
    rw [cos_smoothedCriticalAngle tau htau]
    dsimp only [a, b]
    field_simp
  have hopt : optimalWeightedPhase a b t = 0 := by rw [optimalWeightedPhase, ite_eq_left (le_of_eq hreal.symm)]
  have heq := weightedPhaseCost_optimal a b t hb hab ht
  rw [hopt] at heq
  rw [smoothedPhaseMinimum_eq_weighted tau t htau, ← heq]
  change twoFocusCost (a * Real.cos t) (a * Real.sin t) (circlePhase b 0) - 2 * tau = _
  rw [hreal]
  have hcircle : circlePhase b 0 = (b : ℂ) := by simp [circlePhase]
  rw [hcircle]
  have hp : (b : ℂ) + (((a * Real.sin t : ℝ) : ℂ)) * Complex.I - (b : ℂ) =
      (((a * Real.sin t : ℝ) : ℂ)) * Complex.I := by ring
  have hm : (b : ℂ) - (((a * Real.sin t : ℝ) : ℂ)) * Complex.I - (b : ℂ) =
      -((((a * Real.sin t : ℝ) : ℂ)) * Complex.I) := by ring
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1
    (by linarith [ht.2, Real.pi_pos])
  unfold twoFocusCost
  rw [hp, hm, norm_neg]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, abs_of_nonneg hs,
    Complex.norm_I, mul_one]
  ring

private theorem smoothedPhaseMinimum_eq_super_of_ge
    (tau theta : ℝ) (htau : 0 < tau) (hθ : theta ∈ Set.Icc 0 (Real.pi / 2))
    (hle : smoothedCriticalAngle tau ≤ theta) :
    smoothedPhaseMinimum tau theta = 2 * smoothingRadius tau * Real.sin theta - 2 * tau := by
  by_cases heq : theta = smoothedCriticalAngle tau
  · subst theta
    exact smoothedPhaseMinimum_critical_eq_super tau htau
  let a := smoothingRadius tau
  have ha : 0 < a := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hc := smoothedCriticalAngle_mem_Icc tau
  have hcos : Real.cos theta < a⁻¹ ^ 2 := by
    rw [← cos_smoothedCriticalAngle tau htau]
    exact Real.strictAntiOn_cos ⟨hc.1, by linarith [hc.2, Real.pi_pos]⟩
      ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩ (lt_of_le_of_ne hle (Ne.symm heq))
  have hmul := mul_lt_mul_of_pos_left hcos ha
  have hid : a * (a⁻¹ ^ 2) = a⁻¹ := by field_simp
  rw [hid] at hmul
  rw [smoothedPhaseMinimum, ite_eq_right (not_le.mpr hmul)]


private theorem smoothedPhaseMinimum_lipschitz_ordered
    (tau x y : ℝ) (htau : 0 < tau)
    (hx : x ∈ Set.Icc 0 (Real.pi / 2)) (hy : y ∈ Set.Icc 0 (Real.pi / 2)) (hxy : x ≤ y) :
    ‖smoothedPhaseMinimum tau y - smoothedPhaseMinimum tau x‖ ≤
      2 * (smoothingRadius tau)⁻¹ * ‖y - x‖ := by
  let t := smoothedCriticalAngle tau
  have ht : t ∈ Set.Icc 0 (Real.pi / 2) := smoothedCriticalAngle_mem_Icc tau
  by_cases hyt : y ≤ t
  · rw [smoothedPhaseMinimum_eq_canonical_of_le tau y htau hy hyt,
      smoothedPhaseMinimum_eq_canonical_of_le tau x htau hx (hxy.trans hyt)]
    exact canonicalValueBranch_lipschitz tau htau x y hx hy
  by_cases htx : t ≤ x
  · rw [smoothedPhaseMinimum_eq_super_of_ge tau y htau hy (htx.trans hxy),
      smoothedPhaseMinimum_eq_super_of_ge tau x htau hx htx]
    exact supercriticalValueBranch_lipschitz tau htau x y ⟨htx, hx.2⟩ ⟨htx.trans hxy, hy.2⟩
  have hxt : x ≤ t := (lt_of_not_ge htx).le
  have hty : t ≤ y := (lt_of_not_ge hyt).le
  have hleft : ‖smoothedPhaseMinimum tau t - smoothedPhaseMinimum tau x‖ ≤
      2 * (smoothingRadius tau)⁻¹ * ‖t - x‖ := by
    rw [smoothedPhaseMinimum_eq_canonical_of_le tau t htau ht le_rfl,
      smoothedPhaseMinimum_eq_canonical_of_le tau x htau hx hxt]
    exact canonicalValueBranch_lipschitz tau htau x t hx ht
  have hright : ‖smoothedPhaseMinimum tau y - smoothedPhaseMinimum tau t‖ ≤
      2 * (smoothingRadius tau)⁻¹ * ‖y - t‖ := by
    rw [smoothedPhaseMinimum_eq_super_of_ge tau y htau hy hty,
      smoothedPhaseMinimum_eq_super_of_ge tau t htau ht le_rfl]
    exact supercriticalValueBranch_lipschitz tau htau t y ⟨le_rfl, ht.2⟩ ⟨hty, hy.2⟩
  calc
    _ ≤ ‖smoothedPhaseMinimum tau y - smoothedPhaseMinimum tau t‖ +
        ‖smoothedPhaseMinimum tau t - smoothedPhaseMinimum tau x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (smoothingRadius tau)⁻¹ * ‖y - t‖ +
        2 * (smoothingRadius tau)⁻¹ * ‖t - x‖ := add_le_add hright hleft
    _ = _ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hty), abs_of_nonneg (sub_nonneg.mpr hxt),
        abs_of_nonneg (sub_nonneg.mpr hxy)]
      ring

/-- The exact angle value is Lipschitz with the explicit scale `2 / eta`. -/
theorem smoothedPhaseMinimum_lipschitz
    (tau x y : ℝ) (htau : 0 < tau)
    (hx : x ∈ Set.Icc 0 (Real.pi / 2)) (hy : y ∈ Set.Icc 0 (Real.pi / 2)) :
    |smoothedPhaseMinimum tau x - smoothedPhaseMinimum tau y| ≤
      2 * (smoothingRadius tau)⁻¹ * |x - y| := by
  rcases le_total x y with hxy | hyx
  · have h := smoothedPhaseMinimum_lipschitz_ordered tau x y htau hx hy hxy
    simpa only [Real.norm_eq_abs, abs_sub_comm] using h
  · exact smoothedPhaseMinimum_lipschitz_ordered tau y x htau hy hx hyx

/-- Errors in a finite list of principal angles bound the error in the
exact global value by the sum of the individual angle errors. -/
theorem sum_smoothedPhaseMinimum_lipschitz {ι : Type*} [Fintype ι]
    (tau : ℝ) (htau : 0 < tau) (theta phi : ι → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Icc 0 (Real.pi / 2))
    (hφ : ∀ i, phi i ∈ Set.Icc 0 (Real.pi / 2)) :
    |(∑ i, smoothedPhaseMinimum tau (theta i)) - (∑ i, smoothedPhaseMinimum tau (phi i))| ≤
      2 * (smoothingRadius tau)⁻¹ * ∑ i, |theta i - phi i| := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |smoothedPhaseMinimum tau (theta i) - smoothedPhaseMinimum tau (phi i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * (smoothingRadius tau)⁻¹ * |theta i - phi i| :=
      Finset.sum_le_sum fun i _ => smoothedPhaseMinimum_lipschitz tau _ _ htau (hθ i) (hφ i)
    _ = _ := (Finset.mul_sum _ _ _).symm


private theorem criticalAngle_interior (tau : ℝ) (htau : 0 < tau) :
    smoothedCriticalAngle tau ∈ Set.Ioo 0 (Real.pi / 2) := by
  have ha : 1 < smoothingRadius tau := one_lt_smoothingRadius tau htau
  have ha0 := zero_lt_one.trans ha
  have hb : 0 < (smoothingRadius tau)⁻¹ := inv_pos.mpr ha0
  have hb1 : (smoothingRadius tau)⁻¹ < 1 := (inv_lt_one₀ ha0).mpr ha
  constructor
  · exact Real.arccos_pos.mpr (by nlinarith)
  · exact Real.arccos_lt_pi_div_two.mpr (sq_pos_of_pos hb)

/-- The optimal angle value is differentiable at the transition, with
slope exactly `2 / eta`. -/
theorem smoothedPhaseMinimum_hasDerivAt_critical (tau : ℝ) (htau : 0 < tau) :
    HasDerivAt (smoothedPhaseMinimum tau) (2 * (smoothingRadius tau)⁻¹)
      (smoothedCriticalAngle tau) := by
  let a := smoothingRadius tau
  let t := smoothedCriticalAngle tau
  have ha : 0 < a := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have ht : t ∈ Set.Ioo 0 (Real.pi / 2) := criticalAngle_interior tau htau
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, Real.pi_pos])
  have hcanon := smoothedPhaseMinimum_eq_canonical_of_le tau t htau ⟨ht.1.le, ht.2.le⟩ le_rfl
  have hsuper := smoothedPhaseMinimum_critical_eq_super tau htau
  have hsqrt : Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos t) = a * Real.sin t := by
    change smoothedPhaseMinimum tau t = 2 * a * Real.sin t - 2 * tau at hsuper
    dsimp only [canonicalValueBranch] at hcanon
    linarith only [hcanon, hsuper]
  have hdcanon : HasDerivAt (canonicalValueBranch tau) (2 * a⁻¹) t := by
    convert canonicalValueBranch_hasDerivAt tau t htau using 1
    rw [hsqrt]
    field_simp
  have hdsuper : HasDerivAt (fun x => 2 * a * Real.sin x - 2 * tau) (2 * a⁻¹) t := by
    convert ((Real.hasDerivAt_sin t).const_mul (2 * a)).sub_const (2 * tau) using 1
    rw [cos_smoothedCriticalAngle tau htau]
    dsimp only [a]
    field_simp
  have hleft : HasDerivWithinAt (smoothedPhaseMinimum tau) (2 * a⁻¹) (Set.Icc 0 t) t := by
    apply hdcanon.hasDerivWithinAt.congr_of_mem
    · intro x hx
      exact smoothedPhaseMinimum_eq_canonical_of_le tau x htau
        ⟨hx.1, hx.2.trans ht.2.le⟩ hx.2
    · exact ⟨ht.1.le, le_rfl⟩
  have hright : HasDerivWithinAt (smoothedPhaseMinimum tau) (2 * a⁻¹)
      (Set.Icc t (Real.pi / 2)) t := by
    apply hdsuper.hasDerivWithinAt.congr_of_mem
    · intro x hx
      exact smoothedPhaseMinimum_eq_super_of_ge tau x htau
        ⟨ht.1.le.trans hx.1, hx.2⟩ hx.1
    · exact ⟨le_rfl, ht.2.le⟩
  have hboth := hleft.union hright
  rw [Set.Icc_union_Icc_eq_Icc ht.1.le ht.2.le] at hboth
  exact hboth.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- No smaller Lipschitz constant works for the exact angle value on the
full principal-angle interval. -/
theorem smoothedPhaseMinimum_lipschitz_constant_necessary
    (tau : ℝ) (htau : 0 < tau) (C : ℝ≥0)
    (hC : LipschitzOnWith C (smoothedPhaseMinimum tau) (Set.Icc 0 (Real.pi / 2))) :
    2 * (smoothingRadius tau)⁻¹ ≤ C := by
  have ht := criticalAngle_interior tau htau
  have hbound := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) hC
  rw [(smoothedPhaseMinimum_hasDerivAt_critical tau htau).deriv] at hbound
  have ha : 0 < smoothingRadius tau := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hb : 0 ≤ 2 * (smoothingRadius tau)⁻¹ := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb] using hbound


/-- The least Lipschitz constant of the exact scalar minimum is `2 / eta`. -/
theorem lipschitzOnWith_smoothedPhaseMinimum_iff
    (tau : ℝ) (htau : 0 < tau) (C : ℝ≥0) :
    LipschitzOnWith C (smoothedPhaseMinimum tau) (Set.Icc 0 (Real.pi / 2)) ↔
      2 * (smoothingRadius tau)⁻¹ ≤ C := by
  constructor
  · exact smoothedPhaseMinimum_lipschitz_constant_necessary tau htau C
  · intro hC
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [Real.dist_eq]
    exact (smoothedPhaseMinimum_lipschitz tau x y htau hx hy).trans
      (mul_le_mul_of_nonneg_right hC (abs_nonneg _))

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
