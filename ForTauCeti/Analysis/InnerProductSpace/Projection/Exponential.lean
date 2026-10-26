/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Exponentiating a scalar multiple of an orthogonal projection

The exponential multiplies the projected sector by the scalar
exponential and fixes its orthogonal complement. No eigenbasis or
dimension assumption is needed.
-/

public section

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Closed formula for exponentiating an orthogonal projection. -/
theorem exp_smul_starProjection (M : Submodule ℂ E) [M.HasOrthogonalProjection] (a : ℂ) :
    NormedSpace.exp (a • M.starProjection) =
      1 + (Complex.exp a - 1) • M.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  have hP : M.starProjection (M.starProjection x) = (1 : ℂ) • M.starProjection x := by
    rw [one_smul, M.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem x)]
  have hPc : M.starProjection (Mᗮ.starProjection x) = (0 : ℂ) • Mᗮ.starProjection x := by
    rw [zero_smul, M.starProjection_apply_eq_zero_iff.mpr (Mᗮ.starProjection_apply_mem x)]
  change NormedSpace.exp (a • M.starProjection) x = x + (Complex.exp a - 1) • M.starProjection x
  calc
    _ = NormedSpace.exp (a • M.starProjection)
        (M.starProjection x + Mᗮ.starProjection x) :=
      congrArg (fun y : E => (NormedSpace.exp (a • M.starProjection)) y)
        (M.starProjection_add_starProjection_orthogonal x).symm
    _ = Complex.exp a • M.starProjection x + Mᗮ.starProjection x := by
      rw [map_add, ContinuousLinearMap.exp_smul_apply_of_apply_eq_smul M.starProjection hP,
        ContinuousLinearMap.exp_smul_apply_of_apply_eq_smul M.starProjection hPc,
        mul_one, mul_zero, NormedSpace.exp_zero, one_smul, ← Complex.exp_eq_exp_ℂ]
    _ = (M.starProjection x + Mᗮ.starProjection x) +
        (Complex.exp a - 1) • M.starProjection x := by rw [sub_smul, one_smul]; abel
    _ = _ := by rw [M.starProjection_add_starProjection_orthogonal]

end Submodule
