/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# The real inverse Cayley coordinate

The real part of `i (1 + w) / (1 - w)` is measurable on the whole complex plane,
with value zero at `w = 1`. It recovers the real part of every complex Cayley
parameter, including the totalized pole, and inverts the Cayley transform on
the unit circle away from `1`.

Adapted from the DKPS spectral-measure construction (Jon Crall and Claude Opus 5,
Kitware 2026, Apache-2.0). The complex inverse identities and closed-half-plane
bijection are reused from Tau Ceti rather than reproved by denominator algebra.
-/

public section

open MeasureTheory
open scoped ComplexOrder

namespace Complex

/-- The real inverse Cayley coordinate, with value zero at its singular point `1`. -/
noncomputable def inverseCayleyCoord (w : ℂ) : ℝ := (I * (1 + w) / (1 - w)).re

/-- Formula for the real inverse Cayley coordinate. -/
theorem inverseCayleyCoord_def (w : ℂ) :
    inverseCayleyCoord w = (I * (1 + w) / (1 - w)).re := (rfl)

/-- The inverse Cayley coordinate is measurable. -/
@[fun_prop] theorem measurable_inverseCayleyCoord : Measurable inverseCayleyCoord := by
  unfold inverseCayleyCoord
  fun_prop

/-- The inverse Cayley coordinate has value zero at `1`. -/
@[simp] theorem inverseCayleyCoord_one : inverseCayleyCoord 1 = 0 := by
  simp [inverseCayleyCoord]

/-- Applying the inverse coordinate to a complex Cayley parameter recovers its real part. -/
@[simp] theorem inverseCayleyCoord_cayley (z : ℂ) :
    inverseCayleyCoord ((z - I) / (z + I)) = z.re := by
  by_cases hz : z + I = 0
  · rw [eq_neg_of_add_eq_zero_left hz]
    simp [inverseCayleyCoord]
  · rw [inverseCayleyCoord_def, TauCeti.I_mul_one_add_sub_I_div_add_I_div_one_sub hz]

/-- The Cayley transform recovers every unit-circle point other than `1`. -/
theorem cayley_inverseCayleyCoord {w : ℂ} (hw : ‖w‖ = 1) (h1 : w ≠ 1) :
    ((inverseCayleyCoord w : ℂ) - I) / ((inverseCayleyCoord w : ℂ) + I) = w := by
  -- Expose `surjOn`'s target set so the pair elaborates as set-difference membership:
  -- closed-ball membership is `‖w‖ ≤ 1`, and exclusion from `{1}` reduces to `w ≠ 1`.
  obtain ⟨z, hz, hzw⟩ := TauCeti.bijOn_sub_I_div_add_I_im_nonneg.surjOn
    (show w ∈ Metric.closedBall 0 1 \ {1} from
      ⟨mem_closedBall_zero_iff.mpr hw.le, h1⟩)
  dsimp only at hzw
  have him : z.im = 0 := by
    have hnot : ¬ 0 < z.im := by
      intro hpos
      have hlt := (TauCeti.norm_sub_I_div_add_I_lt_one_iff
        (TauCeti.add_I_ne_zero_of_im_nonneg hz)).mpr hpos
      rw [hzw, hw] at hlt
      exact (lt_irrefl 1) hlt
    exact le_antisymm (not_lt.mp hnot) hz
  have hreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  rw [← hzw, inverseCayleyCoord_cayley, hreal]

end Complex
