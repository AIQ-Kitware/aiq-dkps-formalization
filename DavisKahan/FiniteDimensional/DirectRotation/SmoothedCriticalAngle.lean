/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPhaseMinimum

/-!
# The common Charbonnier critical angle

The canonical cutoff is shared by the quartic stability theory and the
local spectral-gradient analysis. Positive smoothing places it strictly
between zero and a right angle.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

/-- The exact Charbonnier critical principal angle. -/
@[expose] def smoothedCriticalAngle (tau : ℝ) : ℝ :=
  Real.arccos (((smoothingRadius tau)⁻¹) ^ 2)

theorem smoothedCriticalAngle_mem_Icc (tau : ℝ) :
    smoothedCriticalAngle tau ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (sq_nonneg _)⟩

theorem cos_smoothedCriticalAngle (tau : ℝ) (hτ : 0 < tau) :
    Real.cos (smoothedCriticalAngle tau) = ((smoothingRadius tau)⁻¹) ^ 2 := by
  have ha := one_lt_smoothingRadius tau hτ
  have ha0 : 0 < smoothingRadius tau := lt_trans zero_lt_one ha
  have hb : (smoothingRadius tau)⁻¹ ≤ 1 := (inv_le_one₀ ha0).mpr ha.le
  have hb0 : 0 ≤ (smoothingRadius tau)⁻¹ := (inv_pos.mpr ha0).le
  apply Real.cos_arccos (by nlinarith [sq_nonneg ((smoothingRadius tau)⁻¹)])
  nlinarith

/-- The critical angle lies strictly between zero and a right angle. -/
theorem smoothedCriticalAngle_mem (tau : ℝ) (htau : 0 < tau) :
    smoothedCriticalAngle tau ∈ Set.Ioo 0 (Real.pi / 2) := by
  have ha := one_lt_smoothingRadius tau htau
  have ha0 : 0 < smoothingRadius tau := zero_lt_one.trans ha
  have hb : 0 < (smoothingRadius tau)⁻¹ := inv_pos.mpr ha0
  have hb1 : (smoothingRadius tau)⁻¹ < 1 := (inv_lt_one₀ ha0).mpr ha
  exact ⟨Real.arccos_pos.mpr (by nlinarith), Real.arccos_lt_pi_div_two.mpr (by positivity)⟩

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
