/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.InnerProductSpace.Modulus
public import TauCeti.Analysis.Normed.Operator.RealAlgebra
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Coercivity of an operator modulus

A lower bound for the norm of an operator gives the same lower bound
for the quadratic form of its positive modulus. Operator monotonicity
of the square root transfers the Gram lower bound, in arbitrary Hilbert
dimension and without a compactness hypothesis.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A squared norm lower bound becomes the sharp quadratic-form lower
bound for the modulus. Neither invertibility nor surjectivity is assumed. -/
theorem mul_norm_sq_le_re_inner_modulus_of_sq_mul_norm_sq_le
    (T : E →L[ℂ] E) (m : ℝ) (hm : 0 ≤ m)
    (hT : ∀ x, m ^ 2 * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2) (x : E) :
    m * ‖x‖ ^ 2 ≤ RCLike.re ⟪T.modulus x, x⟫_ℂ := by
  let A : E →L[ℂ] E := (m : ℂ) • 1
  have hApos : A.IsPositive := isPositive_one.smul_of_nonneg (Complex.zero_le_real.mpr hm)
  have hAself := hApos.isSelfAdjoint
  have hAform (u v : E) : RCLike.re ⟪A u, v⟫_ℂ = m * RCLike.re ⟪u, v⟫_ℂ := by
    change RCLike.re ⟪(m : ℂ) • u, v⟫_ℂ = _
    rw [inner_smul_left]
    change ((starRingEnd ℂ) (m : ℂ) * ⟪u, v⟫_ℂ).re = m * (⟪u, v⟫_ℂ).re
    rw [show (starRingEnd ℂ) (m : ℂ) = (m : ℂ) from Complex.conj_ofReal m]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hAA (y : E) : RCLike.re ⟪(A * A) y, y⟫_ℂ = m ^ 2 * ‖y‖ ^ 2 := by
    change RCLike.re ⟪A (A y), y⟫_ℂ = _
    rw [hAform, hAform, ← norm_sq_eq_re_inner]
    ring
  have hGram (y : E) : RCLike.re ⟪(T.adjoint ∘L T) y, y⟫_ℂ = ‖T y‖ ^ 2 := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (T y)).symm
  have hle : A * A ≤ T.adjoint ∘L T := by
    apply le_def.mpr
    refine isPositive_def'.mpr ⟨?_, ?_⟩
    · apply IsSelfAdjoint.sub (isPositive_adjoint_comp_self T).isSelfAdjoint
      change star (A * A) = A * A
      rw [star_mul, hAself.star_eq]
    · intro y
      rw [ContinuousLinearMap.reApplyInnerSelf_apply,
        sub_apply, inner_sub_left, map_sub, hGram, hAA]
      exact sub_nonneg.mpr (hT y)
  have hroot := CFC.sqrt_le_sqrt (A * A) (T.adjoint ∘L T) hle
  rw [CFC.sqrt_mul_self A (nonneg_iff_isPositive.mpr hApos), ← T.modulus_eq_sqrt] at hroot
  have hform := (le_def.mp hroot).re_inner_nonneg_left x
  have hAx : RCLike.re ⟪A x, x⟫_ℂ = m * ‖x‖ ^ 2 := by
    rw [hAform, ← norm_sq_eq_re_inner]
  rw [sub_apply, inner_sub_left, map_sub, hAx] at hform
  linarith

end ContinuousLinearMap
