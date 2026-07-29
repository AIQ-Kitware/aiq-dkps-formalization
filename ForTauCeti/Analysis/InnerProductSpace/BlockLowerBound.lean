/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity

/-!
# A lower bound proved blockwise

If a family of bounded operators splits vector norms — `∑ ‖blocks i f‖² = ‖f‖²`
— then a lower bound holding on every block holds globally.

This is the reassembly step of a block-diagonal argument, stated with nothing
about where the blocks come from: no projections, no spectral theory, no
countability, no convergence of `∑ blocks i` in any operator topology.  The only
hypothesis is the norm split, which is what a projection-valued measure supplies
along a partition (`ProjValMeasure.tsum_enorm_sq_proj`).

Working in `ℝ≥0∞` keeps it free of summability side conditions: the sums are
unconditional and no term has to be shown finite.

## Provenance

*New.*
-/

open scoped ENNReal NNReal

namespace TauCeti

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **A lower bound that holds blockwise holds globally.** -/
theorem enorm_ge_of_blocks {S : H →ₗ.[ℂ] H} {c : ℝ≥0∞} {ι : Type*}
    (blocks : ι → (H →L[ℂ] H))
    (hsplit : ∀ f : H, ∑' i, ‖blocks i f‖ₑ ^ 2 = ‖f‖ₑ ^ 2)
    (x : S.domain)
    (hblock : ∀ i, c * ‖blocks i (x : H)‖ₑ ≤ ‖blocks i (S x)‖ₑ) :
    c * ‖(x : H)‖ₑ ≤ ‖S x‖ₑ := by
  have hsq : (c * ‖(x : H)‖ₑ) ^ 2 ≤ ‖S x‖ₑ ^ 2 := by
    calc (c * ‖(x : H)‖ₑ) ^ 2
        = c ^ 2 * ∑' i, ‖blocks i (x : H)‖ₑ ^ 2 := by rw [mul_pow, hsplit]
      _ = ∑' i, (c * ‖blocks i (x : H)‖ₑ) ^ 2 := by
          simp_rw [mul_pow]
          exact (ENNReal.tsum_mul_left).symm
      _ ≤ ∑' i, ‖blocks i (S x)‖ₑ ^ 2 :=
          ENNReal.tsum_le_tsum fun i => by gcongr; exact hblock i
      _ = ‖S x‖ₑ ^ 2 := hsplit _
  by_contra hcon
  push Not at hcon
  exact absurd ((ENNReal.pow_lt_pow_left_iff (n := 2) two_ne_zero).mpr hcon) (not_lt.mpr hsq)

end TauCeti
