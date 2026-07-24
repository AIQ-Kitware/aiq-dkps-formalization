/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.BoundedRiccatiEstimate

/-!
# The limiting step in the sharp bounded Riccati estimate

This leaf isolates the scalar limit used after evaluating the Riccati equation
on near norm-attaining singular pairs.  The finite-error estimate has the form

`d * (t - eps) <= b * (1 - (t - eps) * t)
  + (a + t * b) * sqrt (2 * t * eps)`.

Sending `eps` to zero gives the sharp contractive inequality

`d * t <= b * (1 - t^2)`.

Keeping this argument separate makes the subsequent operator leaf responsible
only for constructing the approximate singular pairs and supplying the finite
error inequality.
-/

namespace TauCeti
namespace DavisKahanExt

/-- Close the finite-error near-singular-pair estimates at the operator norm.

The parameters `a` and `b` represent the diagonal and off-diagonal operator
norms occurring in the error term.  Their signs are immaterial in the positive
`t` branch because the whole right-hand side is passed to the limit; `b >= 0`
is used only to discharge the degenerate case `t = 0`.
-/
theorem sharp_riccati_bound_of_epsilon
    {d a b t : ℝ}
    (hb0 : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hε : ∀ ε ∈ Set.Ioo (0 : ℝ) t,
      d * (t - ε) ≤
        b * (1 - (t - ε) * t) +
          (a + t * b) * Real.sqrt (2 * t * ε)) :
    d * t ≤ b * (1 - t ^ 2) := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · simpa using hb0
  · have hev : ∀ ε ∈ Set.Ioo (0 : ℝ) t,
        d * t ≤ d * ε +
          (b * (1 - (t - ε) * t) +
            (a + t * b) * Real.sqrt (2 * t * ε)) := by
      intro ε hεmem
      have hstep := hε ε hεmem
      linarith
    have hcont : ContinuousWithinAt
        (fun ε : ℝ =>
          d * ε +
            (b * (1 - (t - ε) * t) +
              (a + t * b) * Real.sqrt (2 * t * ε)))
        (Set.Ioo 0 t) 0 := by
      apply Continuous.continuousWithinAt
      exact (continuous_const.mul continuous_id).add
        ((continuous_const.mul
          (continuous_const.sub
            ((continuous_const.sub continuous_id).mul continuous_const))).add
          (continuous_const.mul
            (Real.continuous_sqrt.comp
              ((continuous_const.mul continuous_const).mul continuous_id))))
    haveI hne : (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo htpos.ne]
      exact ⟨le_refl 0, htpos.le⟩
    have hlim := ge_of_tendsto hcont
      (by filter_upwards [self_mem_nhdsWithin] with ε hεmem using hev ε hεmem)
    simpa [pow_two] using hlim

end DavisKahanExt
end TauCeti