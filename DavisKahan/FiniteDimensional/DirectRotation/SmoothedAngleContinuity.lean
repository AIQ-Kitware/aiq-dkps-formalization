/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPhaseMinimum
public import Mathlib.Topology.Order.Compact

/-!
# Continuity of the exact smoothed scalar value

An optimal scalar phase lies in the fixed compact interval `[0, pi/2]`.
The compact minimum theorem therefore proves continuity at every
principal angle, including the critical transition and both endpoints.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

/-- The two scalar distances are each bounded below by the difference
of the radii. This includes every phase and every real angle. -/
theorem weightedPhaseCost_ge_radial_gap (a b theta delta : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (a - b) ≤ weightedPhaseCost a b theta delta := by
  have hn (t : ℝ) :
      ‖((a * Real.cos t : ℝ) : ℂ) + (a * Real.sin t : ℝ) * Complex.I‖ = a := by
    have heq : ((a * Real.cos t : ℝ) : ℂ) + (a * Real.sin t : ℝ) * Complex.I =
        (a : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ha]
  have hnminus :
      ‖((a * Real.cos theta : ℝ) : ℂ) - (a * Real.sin theta : ℝ) * Complex.I‖ = a := by
    simpa only [Real.cos_neg, Real.sin_neg, mul_neg, Complex.ofReal_neg,
      neg_mul, add_neg_cancel, sub_eq_add_neg] using hn (-theta)
  have hleft := norm_sub_norm_le
    (((a * Real.cos theta : ℝ) : ℂ) + (a * Real.sin theta : ℝ) * Complex.I)
    (circlePhase b delta)
  have hright := norm_sub_norm_le
    (((a * Real.cos theta : ℝ) : ℂ) - (a * Real.sin theta : ℝ) * Complex.I)
    (circlePhase b delta)
  rw [hn, norm_circlePhase b delta hb] at hleft
  rw [hnminus, norm_circlePhase b delta hb] at hright
  unfold weightedPhaseCost twoFocusCost
  linarith

/-- Every literal smoothed scalar-phase cost is nonnegative. -/
theorem smoothedPhaseCost_nonneg (tau theta delta : ℝ) (hτ : 0 < tau) :
    0 ≤ smoothedPhaseCost tau theta delta := by
  have ha : 0 < smoothingRadius tau := zero_lt_one.trans (one_lt_smoothingRadius tau hτ)
  have h := weightedPhaseCost_ge_radial_gap _ _ theta delta ha.le (inv_nonneg.mpr ha.le)
  rw [smoothingRadius_sub_inv tau hτ] at h
  exact sub_nonneg.mpr h

/-- Nonnegativity of the exact smoothed angle minimum, including the
zero and right-angle endpoints. -/
theorem smoothedPhaseMinimum_nonneg (tau theta : ℝ) (hτ : 0 < tau)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ smoothedPhaseMinimum tau theta := by
  rw [← smoothedPhaseCost_optimal tau theta hτ hθ]
  exact smoothedPhaseCost_nonneg tau theta _ hτ

/-- Use a fixed compact phase interval for the explicit smoothed value. -/
theorem smoothedPhaseMinimum_eq_sInf (tau theta : ℝ) (hτ : 0 < tau)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    smoothedPhaseMinimum tau theta =
      sInf (smoothedPhaseCost tau theta '' Set.Icc 0 (Real.pi / 2)) := by
  have ha := one_lt_smoothingRadius tau hτ
  have ha0 : 0 < smoothingRadius tau := zero_lt_one.trans ha
  have hab : (smoothingRadius tau)⁻¹ ≤ smoothingRadius tau :=
    (inv_le_one_of_one_le₀ ha.le).trans ha.le
  have hmem := optimalWeightedPhase_mem _ _ theta (inv_pos.mpr ha0) hab hθ
  have heq := smoothedPhaseCost_optimal tau theta hτ hθ
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨optimalSmoothedPhase tau theta, ⟨hmem.1, hmem.2.trans hθ.2⟩, heq⟩, ?_⟩
  rintro _ ⟨delta, _, rfl⟩
  exact smoothedPhaseMinimum_le_cost tau theta hτ hθ delta

/-- The exact smoothed scalar value is continuous on the closed range
of principal angles, including critical, zero and right angles. -/
theorem continuousOn_smoothedPhaseMinimum_angle (tau : ℝ) (hτ : 0 < tau) :
    ContinuousOn (smoothedPhaseMinimum tau) (Set.Icc 0 (Real.pi / 2)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : Continuous (fun x : Set.Icc (0 : ℝ) (Real.pi / 2) × ℝ =>
      smoothedPhaseCost tau x.1 x.2) := by
    unfold smoothedPhaseCost weightedPhaseCost twoFocusCost circlePhase
    fun_prop
  have h := isCompact_Icc.continuous_sInf (K := Set.Icc (0 : ℝ) (Real.pi / 2))
    (f := fun (theta : Set.Icc (0 : ℝ) (Real.pi / 2)) (t : ℝ) =>
      smoothedPhaseCost tau theta t) hfun
  apply h.congr
  intro theta
  exact (smoothedPhaseMinimum_eq_sInf tau theta hτ theta.property).symm

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
