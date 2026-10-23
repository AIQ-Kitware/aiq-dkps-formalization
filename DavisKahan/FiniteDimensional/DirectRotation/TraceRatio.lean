/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.ProjectionDisplacement
import DavisKahan.FiniteDimensional.DirectRotation.SmallAngleCounterexample

/-!
# Exact chord-to-sine displacement ratio for the real four-plane witness

This result combines the already proved trace-displacement formulas with the
trigonometric half-angle identity.  It supplies an exact equality witness for
the proposed factor `sec (theta / 2)`.  By itself it does not assert that the
competitor is a global minimizer, nor does it prove the universal upper bound.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace SmallAngleCounterexample

open scoped InnerProductSpace
open ShortRotationCounterexample (U4)

/-- In the real four-dimensional parameterized example, the competitor's
trace displacement is `cos (theta / 2)` times the direct rotation's trace
displacement.  This is the precise, denominator-free sharpness identity. -/
theorem cos_half_mul_directTrace_eq_competitorTrace
    (theta : ℝ) (h0 : 0 < theta) (h1 : theta < Real.pi / 2) :
    Real.cos (theta / 2) *
        kyFanSum 4 (LinearMap.id -
          (directRotation U4 (V4 theta)
            (acute theta (cos_pos theta h0 h1))).toLinearMap) =
      kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) := by
  have hc : 0 < Real.cos theta := cos_pos theta h0 h1
  have hs : 0 ≤ Real.sin theta :=
    (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])).le
  have hchord :
      Real.sqrt (2 - 2 * Real.cos theta) = 2 * Real.sin (theta / 2) := by
    rw [Real.sin_half_eq_sqrt h0.le (by linarith [Real.pi_pos])]
    rw [show (2 : ℝ) - 2 * Real.cos theta =
        (2 : ℝ) ^ 2 * ((1 - Real.cos theta) / 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hdouble :
      Real.sin theta = 2 * Real.sin (theta / 2) * Real.cos (theta / 2) := by
    convert Real.sin_two_mul (theta / 2) using 1 <;> ring
  rw [kyFanSum_displacement_R theta hc, kyFanSum_displacement_W theta hs,
    hchord, hdouble]
  ring

end SmallAngleCounterexample
end DavisKahan.FiniteDimensional
end TauCeti
