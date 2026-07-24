/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.BoundedOperator.Basic

/-!
# Quantitative bounded left inverses

A lower norm bound alone does not produce a bounded left inverse between
arbitrary Banach spaces: the range may fail to be complemented.  The correct
reusable hypothesis for the Banach-space compatible-norm Sylvester argument is
therefore an explicit bounded left inverse.  Hilbert-space and invertible
specializations can construct this data separately.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace SharedFoundations

universe u v

variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- A bounded left inverse with a quantitative operator-norm estimate. -/
structure BoundedLeftInverseData (A : Y →L[ℂ] Y) (c : ℝ) where
  leftInverse : Y →L[ℂ] Y
  comp_eq_id : leftInverse ∘L A = ContinuousLinearMap.id ℂ Y
  norm_le : ‖leftInverse‖ ≤ c

namespace BoundedLeftInverseData

/-- Pointwise cancellation. -/
theorem apply_apply_eq
    {A : Y →L[ℂ] Y} {c : ℝ} (h : BoundedLeftInverseData A c) (y : Y) :
    h.leftInverse (A y) = y := by
  have hpoint := congrArg (fun T : Y →L[ℂ] Y => T y) h.comp_eq_id
  simpa using hpoint

/-- An inverse bounded by `c` forces the lower norm bound `c⁻¹`. -/
theorem lower_bound_of_nonnegative
    {A : Y →L[ℂ] Y} {c : ℝ} (h : BoundedLeftInverseData A c)
    (hc : 0 ≤ c) (y : Y) :
    ‖y‖ ≤ c * ‖A y‖ := by
  calc
    ‖y‖ = ‖h.leftInverse (A y)‖ := by rw [h.apply_apply_eq y]
    _ ≤ ‖h.leftInverse‖ * ‖A y‖ := h.leftInverse.le_opNorm _
    _ ≤ c * ‖A y‖ := mul_le_mul_of_nonneg_right h.norm_le (norm_nonneg _)

/-- Scaling a left inverse estimate. -/
def weaken {A : Y →L[ℂ] Y} {c d : ℝ}
    (h : BoundedLeftInverseData A c) (hcd : c ≤ d) :
    BoundedLeftInverseData A d where
  leftInverse := h.leftInverse
  comp_eq_id := h.comp_eq_id
  norm_le := h.norm_le.trans hcd

end BoundedLeftInverseData

/-- A bounded linear equivalence provides bounded left-inverse data. -/
noncomputable def boundedLeftInverseDataOfEquiv
    (A : Y ≃L[ℂ] Y) :
    BoundedLeftInverseData A.toContinuousLinearMap ‖A.symm.toContinuousLinearMap‖ where
  leftInverse := A.symm.toContinuousLinearMap
  comp_eq_id := by
    ext y
    simp
  norm_le := le_rfl

end SharedFoundations
end Scratch
end Experimental
end DavisKahan
end ForMathlib
