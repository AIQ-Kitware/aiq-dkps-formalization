/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.Scratch.SharedFoundations.Sylvester.BoundedLeftInverse
import DavisKahan.Experimental.Frontier.RemainingSourceSurface

/-!
# Compatible cross-operator norms and Banach Sylvester estimates

The source-facing Theorem 5.1 currently assumes only that `A` is bounded below.
For arbitrary Banach spaces that does not supply a bounded projection onto the
range and therefore does not furnish the left inverse used by the elementary
proof.  This file proves the quantitative theorem under the exact missing
operator hypothesis.  It also develops full two-sided scaling from the
contraction property.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace SharedFoundations

open Frontier.RemainingSourceSurface

universe u v

variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

namespace CompatibleCrossOperatorNorm

/-- The compatible norm vanishes at the zero operator. -/
theorem map_zero
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y)) :
    N (0 : X →L[ℂ] Y) = 0 := by
  have h := N.smul 0 (0 : X →L[ℂ] Y)
  simpa using h

/-- Negation preserves the compatible norm. -/
theorem map_neg
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (T : X →L[ℂ] Y) : N (-T) = N T := by
  simpa using N.smul (-1) T

/-- Subadditivity for differences. -/
theorem sub_le
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (S T : X →L[ℂ] Y) : N (S - T) ≤ N S + N T := by
  simpa only [sub_eq_add_neg, map_neg N T] using N.triangle S (-T)

/-- Full two-sided ideal estimate obtained by normalizing the left and right
multipliers. -/
theorem comp_le_mul
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (L : Y →L[ℂ] Y) (T : X →L[ℂ] Y) (R : X →L[ℂ] X) :
    N (L ∘L T ∘L R) ≤ ‖L‖ * N T * ‖R‖ := by
  by_cases hL : L = 0
  · subst L
    simp [map_zero N]
  by_cases hR : R = 0
  · subst R
    simp [map_zero N]
  let Ln : Y →L[ℂ] Y := (‖L‖ : ℂ)⁻¹ • L
  let Rn : X →L[ℂ] X := (‖R‖ : ℂ)⁻¹ • R
  have hLnorm : ‖L‖ ≠ 0 := norm_ne_zero_iff.mpr hL
  have hRnorm : ‖R‖ ≠ 0 := norm_ne_zero_iff.mpr hR
  have hLcomplex : (‖L‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLnorm
  have hRcomplex : (‖R‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRnorm
  have hLn : ‖Ln‖ ≤ 1 := by
    change ‖(‖L‖ : ℂ)⁻¹ • L‖ ≤ 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg L), inv_mul_cancel₀ hLnorm]
  have hRn : ‖Rn‖ ≤ 1 := by
    change ‖(‖R‖ : ℂ)⁻¹ • R‖ ≤ 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg R), inv_mul_cancel₀ hRnorm]
  have hcompat := N.compatible Ln T Rn hLn hRn
  have hfactor :
      L ∘L T ∘L R = ((‖L‖ * ‖R‖ : ℝ) : ℂ) • (Ln ∘L T ∘L Rn) := by
    ext x
    simp [Ln, Rn, hLcomplex, hRcomplex, smul_smul,
      mul_assoc, mul_left_comm, mul_comm]
  rw [hfactor, N.smul]
  calc
    ‖((‖L‖ * ‖R‖ : ℝ) : ℂ)‖ * N (Ln ∘L T ∘L Rn)
        ≤ (‖L‖ * ‖R‖) * N T := by
          simpa using mul_le_mul_of_nonneg_left hcompat
            (mul_nonneg (norm_nonneg L) (norm_nonneg R))
    _ = ‖L‖ * N T * ‖R‖ := by ring

/-- One-sided left estimate. -/
theorem comp_left_le_mul
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (L : Y →L[ℂ] Y) (T : X →L[ℂ] Y) :
    N (L ∘L T) ≤ ‖L‖ * N T := by
  have h := comp_le_mul N L T (ContinuousLinearMap.id ℂ X)
  rw [ContinuousLinearMap.comp_id] at h
  calc
    N (L ∘L T) ≤ ‖L‖ * N T * ‖ContinuousLinearMap.id ℂ X‖ := h
    _ ≤ ‖L‖ * N T * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
        (mul_nonneg (norm_nonneg L) (N.nonneg T))
    _ = ‖L‖ * N T := by ring

/-- One-sided right estimate. -/
theorem comp_right_le_mul
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (T : X →L[ℂ] Y) (R : X →L[ℂ] X) :
    N (T ∘L R) ≤ N T * ‖R‖ := by
  have h := comp_le_mul N (ContinuousLinearMap.id ℂ Y) T R
  rw [ContinuousLinearMap.id_comp] at h
  calc
    N (T ∘L R) ≤ ‖ContinuousLinearMap.id ℂ Y‖ * N T * ‖R‖ := h
    _ ≤ 1 * N T * ‖R‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le
          (N.nonneg T))
        (norm_nonneg R)
    _ = N T * ‖R‖ := by ring

end CompatibleCrossOperatorNorm

/-- Corrected Banach-space Theorem 5.1 under an explicit bounded left inverse
of `A`. -/
theorem theorem5_1_of_boundedLeftInverse
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (A : Y →L[ℂ] Y) (B : X →L[ℂ] X)
    (T C : X →L[ℂ] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hB : ‖B‖ ≤ gamma)
    (hleft : BoundedLeftInverseData A (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
  let L := hleft.leftInverse
  have hgd : 0 < gamma + delta := add_pos_of_nonneg_of_pos hgamma hdelta
  have hLT : T = L ∘L C + L ∘L T ∘L B := by
    have hcancel : L ∘L A = ContinuousLinearMap.id ℂ Y := hleft.comp_eq_id
    apply ContinuousLinearMap.ext
    intro x
    have heqpoint := congrArg (fun S : X →L[ℂ] Y => S x) hEq
    simp only [sub_apply, ContinuousLinearMap.comp_apply] at heqpoint
    change T x = L (C x) + L (T (B x))
    have hLA : L (A (T x)) = T x := by
      have hp := congrArg (fun S : Y →L[ℂ] Y => S (T x)) hcancel
      simpa using hp
    rw [← heqpoint, map_sub, hLA]
    abel
  have htri : N T ≤ N (L ∘L C) + N (L ∘L T ∘L B) := by
    calc
      N T = N (L ∘L C + L ∘L T ∘L B) := congrArg N.toFun hLT
      _ ≤ N (L ∘L C) + N (L ∘L T ∘L B) := N.triangle _ _
  have hLC : N (L ∘L C) ≤ (gamma + delta)⁻¹ * N C := by
    exact (CompatibleCrossOperatorNorm.comp_left_le_mul N L C).trans
      (mul_le_mul_of_nonneg_right hleft.norm_le (N.nonneg C))
  have hLTB : N (L ∘L T ∘L B) ≤
      (gamma + delta)⁻¹ * N T * gamma := by
    exact (CompatibleCrossOperatorNorm.comp_le_mul N L T B).trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_right hleft.norm_le (N.nonneg T))
        hB (norm_nonneg B)
        (mul_nonneg (inv_nonneg.mpr hgd.le) (N.nonneg T)))
  have hsum : N T ≤ (gamma + delta)⁻¹ * N C +
      (gamma + delta)⁻¹ * N T * gamma :=
    htri.trans (add_le_add hLC hLTB)
  have hscaled := mul_le_mul_of_nonneg_left hsum hgd.le
  have hnormalize :
      (gamma + delta) *
          ((gamma + delta)⁻¹ * N C + (gamma + delta)⁻¹ * N T * gamma) =
        N C + N T * gamma := by
    calc
      (gamma + delta) *
          ((gamma + delta)⁻¹ * N C + (gamma + delta)⁻¹ * N T * gamma) =
          ((gamma + delta) * (gamma + delta)⁻¹) * N C +
            ((gamma + delta) * (gamma + delta)⁻¹) * N T * gamma := by ring
      _ = N C + N T * gamma := by
        rw [mul_inv_cancel₀ hgd.ne']
        ring
  rw [hnormalize] at hscaled
  nlinarith

end SharedFoundations
end Scratch
end Experimental
end DavisKahan
end ForMathlib
