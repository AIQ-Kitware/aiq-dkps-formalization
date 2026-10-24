/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus

/-!
# Schatten displacement of self-adjoint unitaries

The displacement of an orthogonal reflection has only singular values zero
and two. Its finite Schatten power is consequently `2^(p-1)` times its
nuclear norm. The statement works over real and complex scalars.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal
open UnitarilyInvariantSeminorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- Every finite Schatten displacement power of a self-adjoint unitary
is a fixed scalar multiple of its nuclear displacement. -/
theorem schatten_displacement_rpow_of_isSelfAdjoint
    (U : unitary (E →L[𝕜] E)) (hU : IsSelfAdjoint (U : E →L[𝕜] E))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    schatten 𝕜 E E p (LinearMap.id - (U : E →L[𝕜] E).toLinearMap) ^ p.toReal =
      (2 : ℝ) ^ (p.toReal - 1) *
        nuclear 𝕜 E E (LinearMap.id - (U : E →L[𝕜] E).toLinearMap) := by
  let b := hU.isSymmetric.eigenvectorBasis rfl
  let mu := hU.isSymmetric.eigenvalues rfl
  let lam (i : Fin (Module.finrank 𝕜 E)) : 𝕜 := 1 - (mu i : 𝕜)
  have heigen (i : Fin (Module.finrank 𝕜 E)) :
      (U : E →L[𝕜] E) (b i) = (mu i : 𝕜) • b i :=
    hU.isSymmetric.apply_eigenvectorBasis rfl i
  have hnorm (i : Fin (Module.finrank 𝕜 E)) : |mu i| = 1 := by
    have h := _root_.ContinuousLinearMap.norm_map_of_mem_unitary U.2 (b i)
    rw [heigen, norm_smul, b.orthonormal.1 i, mul_one] at h
    simpa only [RCLike.norm_ofReal] using h
  have hlam (i : Fin (Module.finrank 𝕜 E)) : ‖lam i‖ = 0 ∨ ‖lam i‖ = 2 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 (hnorm i) with hi | hi
    · left
      simp [lam, hi]
    · right
      have hi' : lam i = (2 : 𝕜) := by norm_num [lam, hi]
      rw [hi', RCLike.norm_ofNat]
  have hdisp (i : Fin (Module.finrank 𝕜 E)) :
      ((LinearMap.id : E →ₗ[𝕜] E) - (U : E →L[𝕜] E).toLinearMap) (b i) = lam i • b i := by
    change b i - (U : E →L[𝕜] E) (b i) = (1 - (mu i : 𝕜)) • b i
    rw [heigen, sub_smul, one_smul]
  have htrace : nuclear 𝕜 E E (LinearMap.id - (U : E →L[𝕜] E).toLinearMap) =
      ∑ i, ‖lam i‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, schatten_one] using
      schatten_rpow_eq_sum_norm_eigenvalues b _ lam hdisp 1 ENNReal.one_ne_top
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  rw [schatten_rpow_eq_sum_norm_eigenvalues b _ lam hdisp p hp, htrace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases hlam i with hi | hi
  · simp only [hi, Real.zero_rpow hp0.ne', mul_zero]
  · rw [hi, ← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring

end TauCeti
