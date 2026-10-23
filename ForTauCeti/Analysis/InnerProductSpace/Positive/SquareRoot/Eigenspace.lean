/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot

/-! # Positive square-root eigenspace lemma

The positive square-root API is provided by TauCeti. This module retains only
the additional pointwise eigenspace fact needed by local polar-angle consumers:
if a positive operator squares to `μ²` on a vector and `μ ≥ 0`, then the
operator acts there by `μ`. -/

public section

open scoped InnerProductSpace

namespace LinearMap.IsPositive

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- If `S ≥ 0` and `S² v = μ² v` with `μ ≥ 0`, then `S v = μ v`. -/
theorem apply_eq_smul_of_apply_apply_eq_smul {S : E →ₗ[𝕜] E} (hS : S.IsPositive)
    {v : E} {μ : ℝ} (hμ : 0 ≤ μ)
    (hv : S (S v) = ((μ : 𝕜) * (μ : 𝕜)) • v) :
    S v = (μ : 𝕜) • v := by
  rcases hμ.eq_or_lt with hμ0 | hμpos
  · have hμz : (μ : 𝕜) = 0 := by rw [← hμ0]; simp
    rw [hμz, zero_smul]
    have hSSv : S (S v) = 0 := by rw [hv, hμz]; simp
    have h2 : ‖S v‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner (𝕜 := 𝕜), hS.isSymmetric v (S v), hSSv]
      simp
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2)
  · set w := S v - (μ : 𝕜) • v with hwdef
    have hkey : S w + (μ : 𝕜) • w = 0 := by
      rw [hwdef, map_sub, map_smul, hv, smul_sub, smul_smul]
      abel
    have hSw : S w = (-(μ : 𝕜)) • w := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact hkey
    have h1 := hS.re_inner_nonneg_left w
    rw [hSw, inner_smul_left, map_neg, RCLike.conj_ofReal,
      ← RCLike.ofReal_neg, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner] at h1
    have hw0 : w = 0 := by
      by_contra hne
      have hpos : 0 < ‖w‖ ^ 2 :=
        pow_pos (lt_of_le_of_ne (norm_nonneg _) (fun hq => hne (norm_eq_zero.mp hq.symm))) 2
      nlinarith [h1, hμpos, hpos]
    rw [hwdef, sub_eq_zero] at hw0
    exact hw0

end LinearMap.IsPositive
