/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseMinimum
public import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Continuity of the exact scalar phase value in the principal angle

Rescale the phase interval to a fixed unit interval. Compact minimum
continuity then applies even at zero angle and at the phase transition,
without differentiating the minimizing phase.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

/-- Normalize the variable phase interval, including the zero-angle
case, to one fixed compact interval. -/
theorem phaseMinimum_eq_sInf_unitInterval (p theta : ℝ) (hθ : 0 ≤ theta) :
    phaseMinimum p theta = sInf ((fun t => phasePower p theta (theta * t)) '' Set.Icc 0 1) := by
  have himage : (fun t : ℝ => theta * t) '' Set.Icc 0 1 = Set.Icc 0 theta := by
    simpa only [mul_zero, mul_one] using
      Set.image_mul_left_Icc hθ (show (0 : ℝ) ≤ 1 by norm_num)
  unfold phaseMinimum
  rw [← himage, Set.image_image]

/-- The exact scalar phase value is continuous in the nonnegative
principal angle, including zero and all critical angles. -/
theorem continuousOn_phaseMinimum_angle (p : ℝ) (hp : 0 ≤ p) :
    ContinuousOn (phaseMinimum p) (Set.Ici 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : Continuous (fun x : Set.Ici (0 : ℝ) × ℝ =>
      phasePower p x.1 (x.1.val * x.2)) := by
    unfold phasePower phaseChord
    apply Continuous.add
    · exact (Real.continuous_rpow_const hp).comp (by fun_prop)
    · exact (Real.continuous_rpow_const hp).comp (by fun_prop)
  have h := isCompact_Icc.continuous_sInf (K := Set.Icc (0 : ℝ) 1)
    (f := fun (theta : Set.Ici (0 : ℝ)) (t : ℝ) => phasePower p theta (theta.val * t)) hfun
  apply h.congr
  intro theta
  exact (phaseMinimum_eq_sInf_unitInterval p theta theta.property).symm

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
