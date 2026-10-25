/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenInvolution

/-!
# Frobenius lower certificates for bounded Schatten powers

On singular values in `[0,M]`, the scalar inequality
`M^(p-2) s² ≤ s^p` transfers a Frobenius lower bound to a Schatten
power lower bound when `1 ≤ p ≤ 2`. Unitary displacements have `M=2`,
and self-adjoint unitaries attain equality. The comparison is classical
and uses the accepted singular values and Schatten seminorms.
## Provenance

The scalar comparison is the classical pointwise power inequality on
`[0,M]`. The Lean proofs are independently written here using accepted
Tau Ceti singular values and Schatten seminorms; the reflection endpoint
uses the existing local Schatten-involution formula.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal
open UnitarilyInvariantSeminorm

private theorem bounded_sq_le_rpow (p M s : ℝ) (hp : 0 < p) (hp2 : p ≤ 2)
    (hM : 0 < M) (hs : 0 ≤ s) (hsM : s ≤ M) : M ^ (p - 2) * s ^ 2 ≤ s ^ p := by
  by_cases hs0 : s = 0
  · simp [hs0, Real.zero_rpow hp.ne']
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hbound := Real.rpow_le_rpow hs hsM (sub_nonneg.mpr hp2)
  have hsplit : s ^ p * s ^ (2 - p) = s ^ 2 := by
    rw [← Real.rpow_add hspos, add_sub_cancel, Real.rpow_two]
  have hcancel : M ^ (p - 2) * M ^ (2 - p) = 1 := by
    rw [← Real.rpow_add hM, show p - 2 + (2 - p) = 0 by ring, Real.rpow_zero]
  calc
    _ = M ^ (p - 2) * (s ^ p * s ^ (2 - p)) := by rw [hsplit]
    _ ≤ M ^ (p - 2) * (s ^ p * M ^ (2 - p)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hs _))
        (Real.rpow_nonneg hM.le _)
    _ = s ^ p := by calc
      _ = s ^ p * (M ^ (p - 2) * M ^ (2 - p)) := by ring
      _ = _ := by rw [hcancel, mul_one]

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A uniform singular-value bound gives a dimension-free Frobenius
lower certificate for every finite Schatten exponent at most two. -/
theorem mul_sq_frobenius_le_schatten_rpow_of_norm_apply_le
    (A : E →ₗ[𝕜] F) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp2 : p.toReal ≤ 2) (M : ℝ) (hM : 0 < M) (hA : ∀ x, ‖A x‖ ≤ M * ‖x‖) :
    M ^ (p.toReal - 2) * frobenius 𝕜 E F A ^ 2 ≤ schatten 𝕜 E F p A ^ p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  have hF : frobenius 𝕜 E F A ^ 2 =
      ∑ i : Fin (Module.finrank 𝕜 E), A.singularValues i ^ 2 := by
    rw [frobenius_apply_eq_sqrt_sum_sq_singularValues,
      ← A.sum_fin_singularValues (fun s : ℝ => s ^ 2) (by norm_num),
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  rw [hF, schatten_rpow_eq_sum_singularValues A p hp, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => bounded_sq_le_rpow p.toReal M _ hp0 hp2 hM
    (A.singularValues_nonneg i) (LinearMap.singularValues_le_of_norm_apply_le hM.le hA i))

/-- Every real or complex unitary displacement has the sharp Frobenius
lower certificate with singular-value cutoff two. -/
theorem two_rpow_mul_frobenius_displacement_sq_le_schatten_rpow
    (T : E ≃ₗᵢ[𝕜] E) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp2 : p.toReal ≤ 2) :
    (2 : ℝ) ^ (p.toReal - 2) * frobenius 𝕜 E E (LinearMap.id - T.toLinearMap) ^ 2 ≤
      schatten 𝕜 E E p (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  apply mul_sq_frobenius_le_schatten_rpow_of_norm_apply_le _ p hp hp2 2 (by norm_num)
  intro x
  change ‖x - T x‖ ≤ 2 * ‖x‖
  calc
    _ ≤ ‖x‖ + ‖T x‖ := norm_sub_le _ _
    _ = _ := by rw [T.norm_map]; ring

variable [CompleteSpace E]

/-- A self-adjoint unitary saturates the Frobenius comparison at every
finite Schatten exponent. Its displacement singular values are zero or two. -/
theorem schatten_displacement_rpow_eq_two_rpow_mul_frobenius_sq_of_isSelfAdjoint
    (U : unitary (E →L[𝕜] E)) (hU : IsSelfAdjoint (U : E →L[𝕜] E))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    schatten 𝕜 E E p (LinearMap.id - (U : E →L[𝕜] E).toLinearMap) ^ p.toReal =
      (2 : ℝ) ^ (p.toReal - 2) *
        frobenius 𝕜 E E (LinearMap.id - (U : E →L[𝕜] E).toLinearMap) ^ (2 : ℕ) := by
  have htwo := schatten_displacement_rpow_of_isSelfAdjoint U hU 2 (by norm_num)
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_natCast, schatten_two,
    sub_self, sub_zero, Real.rpow_one, Nat.cast_ofNat] at htwo
  have hpow : (2 : ℝ) ^ (p.toReal - 1) = (2 : ℝ) ^ (p.toReal - 2) * 2 := by
    rw [← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  calc
    _ = (2 : ℝ) ^ (p.toReal - 1) *
        nuclear 𝕜 E E (LinearMap.id - (U : E →L[𝕜] E).toLinearMap) :=
      schatten_displacement_rpow_of_isSelfAdjoint U hU p hp
    _ = (2 : ℝ) ^ (p.toReal - 2) *
        (2 * nuclear 𝕜 E E (LinearMap.id - (U : E →L[𝕜] E).toLinearMap)) := by rw [hpow]; ring
    _ = _ := congrArg (fun r : ℝ => (2 : ℝ) ^ (p.toReal - 2) * r) htwo.symm
  norm_num only [Real.rpow_two]

end TauCeti
