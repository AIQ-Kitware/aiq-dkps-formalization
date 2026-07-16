/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Rectangular
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Bound/inverse Sylvester estimates

This module isolates the exact dimension-free form of Davis--Kahan Theorem 5.1.
The Neumann construction and ideal-norm convergence are separated so that the
analytic difficulty is visible in the dependency graph.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Explicit bounded two-sided inverse data for an endomorphism. -/
structure BoundedInverseData (A : E →L[𝕜] E) where
  inv : E →L[𝕜] E
  left_inv : inv ∘L A = ContinuousLinearMap.id 𝕜 E
  right_inv : A ∘L inv = ContinuousLinearMap.id 𝕜 E

namespace BoundedInverseData

omit [CompleteSpace E] in
/-- An operator carrying two-sided bounded inverse data is injective. -/
theorem injective {A : E →L[𝕜] E} (hA : BoundedInverseData A) :
    Function.Injective A := by
  intro x y hxy
  calc
    x = (ContinuousLinearMap.id 𝕜 E) x := by simp
    _ = (hA.inv ∘L A) x := by rw [hA.left_inv]
    _ = hA.inv (A x) := rfl
    _ = hA.inv (A y) := congrArg hA.inv hxy
    _ = (hA.inv ∘L A) y := rfl
    _ = (ContinuousLinearMap.id 𝕜 E) y := by rw [hA.left_inv]
    _ = y := by simp

omit [CompleteSpace E] in
/-- An operator carrying two-sided bounded inverse data is surjective. -/
theorem surjective {A : E →L[𝕜] E} (hA : BoundedInverseData A) :
    Function.Surjective A := by
  intro y
  refine ⟨hA.inv y, ?_⟩
  change (A ∘L hA.inv) y = y
  rw [hA.right_inv]
  simp

omit [CompleteSpace E] in
/-- A two-sided bounded inverse is unique. -/
theorem inv_eq {A B : E →L[𝕜] E} (hA : BoundedInverseData A)
    (hBleft : B ∘L A = ContinuousLinearMap.id 𝕜 E) :
    B = hA.inv := by
  calc
    B = B ∘L ContinuousLinearMap.id 𝕜 E := by simp
    _ = B ∘L (A ∘L hA.inv) := by rw [hA.right_inv]
    _ = (B ∘L A) ∘L hA.inv := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = ContinuousLinearMap.id 𝕜 E ∘L hA.inv := by rw [hBleft]
    _ = hA.inv := by simp

end BoundedInverseData

omit [CompleteSpace E] in
/-- Powers of a continuous endomorphism satisfy the expected operator-norm bound. -/
theorem opNorm_pow_le (T : E →L[𝕜] E) (n : ℕ) :
    ‖T ^ n‖ ≤ ‖T‖ ^ n := by
  induction n with
  | zero =>
      change ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (ContinuousLinearMap.opNorm_comp_le (T ^ n) T).trans
        (mul_le_mul_of_nonneg_right ih (norm_nonneg T))

/-- The `n`th term in the Neumann construction for `A X - X B = C`. -/
noncomputable def sylvesterNeumannTerm
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) (n : ℕ) : F →L[𝕜] E :=
  (hA.inv ^ (n + 1)) ∘L C ∘L (B ^ n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The first Neumann term cancels the left block. -/
theorem comp_sylvesterNeumannTerm_zero
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) :
    A ∘L sylvesterNeumannTerm hA B C 0 = C := by
  unfold sylvesterNeumannTerm
  simp only [zero_add, pow_one, pow_zero]
  rw [← ContinuousLinearMap.comp_assoc A hA.inv, hA.right_inv]
  change C ∘L ContinuousLinearMap.id 𝕜 F = C
  exact ContinuousLinearMap.comp_id C

omit [CompleteSpace E] [CompleteSpace F] in
/-- Consecutive Neumann terms telescope through the two diagonal blocks. -/
theorem comp_sylvesterNeumannTerm_succ
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) (n : ℕ) :
    A ∘L sylvesterNeumannTerm hA B C (n + 1) =
      sylvesterNeumannTerm hA B C n ∘L B := by
  have hright_apply (x : E) : A (hA.inv x) = x := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) hA.right_inv
    simpa using h
  ext x
  change
    A ((hA.inv ^ ((n + 1) + 1)) (C ((B ^ (n + 1)) x))) =
      (hA.inv ^ (n + 1)) (C ((B ^ n) (B x)))
  rw [pow_succ' hA.inv (n + 1), pow_succ B n]
  change
    A (hA.inv ((hA.inv ^ (n + 1)) (C ((B ^ n) (B x))))) =
      (hA.inv ^ (n + 1)) (C ((B ^ n) (B x)))
  exact hright_apply _

omit [CompleteSpace E] [CompleteSpace F] in
/-- Operator-norm geometric bound for one Neumann term. -/
theorem norm_sylvesterNeumannTerm_le
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) (n : ℕ) :
    ‖sylvesterNeumannTerm hA B C n‖ ≤
      ‖hA.inv‖ * ‖C‖ * (‖hA.inv‖ * ‖B‖) ^ n := by
  change
    ‖((hA.inv ^ (n + 1)) ∘L C) ∘L (B ^ n)‖ ≤
      ‖hA.inv‖ * ‖C‖ * (‖hA.inv‖ * ‖B‖) ^ n
  have hleft :
      ‖(hA.inv ^ (n + 1)) ∘L C‖ ≤ ‖hA.inv ^ (n + 1)‖ * ‖C‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have houter :
      ‖((hA.inv ^ (n + 1)) ∘L C) ∘L (B ^ n)‖ ≤
        ‖(hA.inv ^ (n + 1)) ∘L C‖ * ‖B ^ n‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  calc
    ‖((hA.inv ^ (n + 1)) ∘L C) ∘L (B ^ n)‖
        ≤ ‖(hA.inv ^ (n + 1)) ∘L C‖ * ‖B ^ n‖ := houter
    _ ≤ (‖hA.inv ^ (n + 1)‖ * ‖C‖) * ‖B ^ n‖ :=
      mul_le_mul_of_nonneg_right hleft (norm_nonneg (B ^ n))
    _ ≤ (‖hA.inv‖ ^ (n + 1) * ‖C‖) * ‖B‖ ^ n := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (opNorm_pow_le hA.inv (n + 1))
          (norm_nonneg C))
        (opNorm_pow_le B n)
        (norm_nonneg (B ^ n))
        (mul_nonneg (pow_nonneg (norm_nonneg hA.inv) _) (norm_nonneg C))
    _ = ‖hA.inv‖ * ‖C‖ * (‖hA.inv‖ * ‖B‖) ^ n := by
      rw [pow_succ', mul_pow]
      ring

/-- Each Neumann term belongs to the same rectangular ideal as `C`. -/
theorem sylvesterNeumannTerm_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C) (n : ℕ) :
    N.Mem (sylvesterNeumannTerm hA B C n) := by
  unfold sylvesterNeumannTerm
  exact N.comp_mem (hA.inv ^ (n + 1)) (B ^ n) hC

/-- Geometric bound for one Neumann term. -/
theorem gauge_sylvesterNeumannTerm_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C) (n : ℕ) :
    N.gauge (sylvesterNeumannTerm hA B C n)
      ≤ ‖hA.inv‖ ^ (n + 1) * N.gauge C * ‖B‖ ^ n := by
  unfold sylvesterNeumannTerm
  have hcomp := N.gauge_comp_le (hA.inv ^ (n + 1)) (B ^ n) hC
  have hinv := opNorm_pow_le hA.inv (n + 1)
  have hBpow := opNorm_pow_le B n
  have hgauge := N.gauge_nonneg hC
  calc
    N.gauge ((hA.inv ^ (n + 1)) ∘L C ∘L (B ^ n))
        ≤ ‖hA.inv ^ (n + 1)‖ * N.gauge C * ‖B ^ n‖ := hcomp
    _ ≤ (‖hA.inv‖ ^ (n + 1) * N.gauge C) * ‖B ^ n‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinv hgauge) (norm_nonneg (B ^ n))
    _ ≤ (‖hA.inv‖ ^ (n + 1) * N.gauge C) * ‖B‖ ^ n := by
      exact mul_le_mul_of_nonneg_left hBpow
        (mul_nonneg (pow_nonneg (norm_nonneg hA.inv) _) hgauge)

/-- Ideal-norm Cauchy control for partial Neumann sums under the strict ratio. -/
theorem sylvesterNeumannPartialSum_cauchy
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C)
    (hratio : ‖hA.inv‖ * ‖B‖ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m n, M ≤ m → M ≤ n →
      N.gauge
        ((∑ j ∈ Finset.range m, sylvesterNeumannTerm hA B C j) -
         (∑ j ∈ Finset.range n, sylvesterNeumannTerm hA B C j)) < ε := by
  sorry

/-- The ideal-norm limit of the Neumann series. -/
noncomputable def sylvesterNeumannSolution
    (_N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) : F →L[𝕜] E :=
  ∑' n : ℕ, sylvesterNeumannTerm hA B C n

/-- The selected Neumann solution belongs to the ideal. -/
theorem sylvesterNeumannSolution_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C)
    (hratio : ‖hA.inv‖ * ‖B‖ < 1) :
    N.Mem (sylvesterNeumannSolution N hA B C) := by
  sorry

/-- The Neumann solution satisfies the Sylvester equation. -/
theorem sylvesterNeumannSolution_eq
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E)
    (hratio : ‖hA.inv‖ * ‖B‖ < 1) :
    A ∘L sylvesterNeumannSolution N hA B C -
      sylvesterNeumannSolution N hA B C ∘L B = C := by
  sorry

omit [CompleteSpace E] [CompleteSpace F] in
/-- Uniqueness under the bound/inverse separation. -/
theorem sylvester_unique_of_bound_inverse
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (hratio : ‖hA.inv‖ * ‖B‖ < 1)
    {X Y : F →L[𝕜] E}
    (hXY : A ∘L X - X ∘L B = A ∘L Y - Y ∘L B) :
    X = Y := by
  have hEq' : A ∘L X - A ∘L Y = X ∘L B - Y ∘L B := by
    calc
      A ∘L X - A ∘L Y =
          (A ∘L X - X ∘L B) - (A ∘L Y - Y ∘L B) +
            (X ∘L B - Y ∘L B) := by abel
      _ = X ∘L B - Y ∘L B := by rw [hXY, sub_self, zero_add]
  have hEq : A ∘L (X - Y) = (X - Y) ∘L B := by
    simpa only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp] using hEq'
  have hfixed : X - Y = hA.inv ∘L ((X - Y) ∘L B) := by
    calc
      X - Y = ContinuousLinearMap.id 𝕜 E ∘L (X - Y) := by simp
      _ = (hA.inv ∘L A) ∘L (X - Y) := by rw [hA.left_inv]
      _ = hA.inv ∘L (A ∘L (X - Y)) :=
        ContinuousLinearMap.comp_assoc _ _ _
      _ = hA.inv ∘L ((X - Y) ∘L B) := by rw [hEq]
  have hnormle : ‖X - Y‖ ≤ (‖hA.inv‖ * ‖B‖) * ‖X - Y‖ := by
    calc
      ‖X - Y‖ = ‖hA.inv ∘L ((X - Y) ∘L B)‖ := congrArg norm hfixed
      _ ≤ ‖hA.inv‖ * ‖(X - Y) ∘L B‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖hA.inv‖ * (‖X - Y‖ * ‖B‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg hA.inv)
      _ = (‖hA.inv‖ * ‖B‖) * ‖X - Y‖ := by ring
  have hnorm : ‖X - Y‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖X - Y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hlt : (‖hA.inv‖ * ‖B‖) * ‖X - Y‖ < ‖X - Y‖ := by
      calc
        (‖hA.inv‖ * ‖B‖) * ‖X - Y‖ < 1 * ‖X - Y‖ :=
          mul_lt_mul_of_pos_right hratio hpos
        _ = ‖X - Y‖ := one_mul _
    exact (not_lt_of_ge hnormle) hlt
  rw [← sub_eq_zero]
  exact norm_eq_zero.mp hnorm

/-- Davis--Kahan Theorem 5.1 in a rectangular ideal family. -/
theorem sylvester_mem_and_gauge_le_of_bound_inverse
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hAinv : ‖hA.inv‖ ≤ (ρ + δ)⁻¹)
    (hB : ‖B‖ ≤ ρ)
    (hEq : A ∘L X - X ∘L B = C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  sorry

/-- Reversed orientation of the bound/inverse Sylvester estimate. -/
theorem sylvester_mem_and_gauge_le_of_bound_inverse_swapped
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {B : F →L[𝕜] F}
    (hB : BoundedInverseData B) (A : E →L[𝕜] E)
    {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hBinv : ‖hB.inv‖ ≤ (ρ + δ)⁻¹)
    (hA : ‖A‖ ≤ ρ)
    (hEq : A ∘L X - X ∘L B = C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  sorry

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
