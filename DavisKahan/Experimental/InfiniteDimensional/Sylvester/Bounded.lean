/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Rectangular

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

/-- The `n`th term in the Neumann construction for `A X - X B = C`. -/
noncomputable def sylvesterNeumannTerm
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) (n : ℕ) : F →L[𝕜] E := by
  classical
  exact hA.inv ^ (n + 1) ∘L C ∘L B ^ n

/-- Each Neumann term belongs to the same rectangular ideal as `C`. -/
theorem sylvesterNeumannTerm_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C) (n : ℕ) :
    N.Mem (sylvesterNeumannTerm hA B C n) := by
  classical
  unfold sylvesterNeumannTerm
  exact N.comp_mem (N.comp_mem hC (hA.inv ^ (n+1))) (B ^ n)

/-- Geometric bound for one Neumann term. -/
theorem gauge_sylvesterNeumannTerm_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C) (n : ℕ) :
    N.gauge (sylvesterNeumannTerm hA B C n)
      ≤ ‖hA.inv‖ ^ (n + 1) * N.gauge C * ‖B‖ ^ n := by
  classical
  unfold sylvesterNeumannTerm
  calc
    N.gauge (hA.inv ^ (n+1) ∘L C ∘L B ^ n)
        ≤ ‖hA.inv ^ (n+1)‖ * N.gauge C * ‖B ^ n‖ :=
          N.gauge_comp_comp_le _ _ _ hC
    _ ≤ ‖hA.inv‖ ^ (n+1) * N.gauge C * ‖B‖ ^ n := by
          gcongr <;> exact norm_pow_le _ _

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
  classical
  intro ε hε
  let r := ‖hA.inv‖ * ‖B‖
  have hr0 : 0 ≤ r := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨M, hM⟩ := geometric_tail_lt hr0 hratio hε
  refine ⟨M, ?_⟩
  intro m n hm hn
  wlog hmn : m ≤ n generalizing m n
  · simpa [norm_neg] using this n m hn hm (le_of_not_ge hmn)
  rw [Finset.sum_range_sub_sum_range hmn]
  calc
    N.gauge (-(∑ j ∈ Finset.Ico m n, sylvesterNeumannTerm hA B C j))
        = N.gauge (∑ j ∈ Finset.Ico m n, sylvesterNeumannTerm hA B C j) := by
          rw [N.gauge_neg]
    _ ≤ ∑ j ∈ Finset.Ico m n,
          N.gauge (sylvesterNeumannTerm hA B C j) := N.gauge_sum_le _
    _ ≤ ∑ j ∈ Finset.Ico m n,
          ‖hA.inv‖ ^ (j+1) * N.gauge C * ‖B‖ ^ j := by
          gcongr with j hj
          exact gauge_sylvesterNeumannTerm_le N hA B hC j
    _ < ε := by
          simpa [r, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hM m n hm hmn

/-- The ideal-norm limit of the Neumann series. -/
noncomputable def sylvesterNeumannSolution
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) : F →L[𝕜] E := by
  classical
  exact ∑' n, sylvesterNeumannTerm hA B C n

/-- The selected Neumann solution belongs to the ideal. -/
theorem sylvesterNeumannSolution_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C)
    (hratio : ‖hA.inv‖ * ‖B‖ < 1) :
    N.Mem (sylvesterNeumannSolution N hA B C) := by
  classical
  unfold sylvesterNeumannSolution
  apply N.mem_tsum
  · intro n
    exact sylvesterNeumannTerm_mem N hA B hC n
  · exact summable_of_geometric_gauge_bound
      (gauge_sylvesterNeumannTerm_le N hA B hC) hratio

/-- The Neumann solution satisfies the Sylvester equation. -/
theorem sylvesterNeumannSolution_eq
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E)
    (hratio : ‖hA.inv‖ * ‖B‖ < 1) :
    A ∘L sylvesterNeumannSolution N hA B C -
      sylvesterNeumannSolution N hA B C ∘L B = C := by
  classical
  unfold sylvesterNeumannSolution
  rw [ContinuousLinearMap.comp_tsum, ContinuousLinearMap.tsum_comp]
  have htel : ∀ n,
      A ∘L sylvesterNeumannTerm hA B C n -
        sylvesterNeumannTerm hA B C n ∘L B =
      (hA.inv ^ n ∘L C ∘L B ^ n) -
        (hA.inv ^ (n+1) ∘L C ∘L B ^ (n+1)) := by
    intro n
    unfold sylvesterNeumannTerm
    rw [← ContinuousLinearMap.comp_assoc, hA.right_inv]
    simp [ContinuousLinearMap.comp_assoc, pow_succ]
  rw [tsum_congr htel, tsum_sub]
  exact neumann_telescope_tsum hratio hA.left_inv C

/-- Uniqueness under the bound/inverse separation. -/
theorem sylvester_unique_of_bound_inverse
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (hratio : ‖hA.inv‖ * ‖B‖ < 1)
    {X Y : F →L[𝕜] E}
    (hXY : A ∘L X - X ∘L B = A ∘L Y - Y ∘L B) :
    X = Y := by
  classical
  let Z := X - Y
  have hhom : A ∘L Z = Z ∘L B := by
    dsimp [Z]
    module at hXY ⊢
    exact sub_eq_zero.mp hXY
  have hfixed : Z = hA.inv ∘L Z ∘L B := by
    calc
      Z = hA.inv ∘L (A ∘L Z) := by
        rw [← ContinuousLinearMap.comp_assoc, hA.left_inv]
        simp
      _ = hA.inv ∘L Z ∘L B := by rw [hhom, ContinuousLinearMap.comp_assoc]
  have hnorm : ‖Z‖ ≤ (‖hA.inv‖ * ‖B‖) * ‖Z‖ := by
    rw [hfixed]
    calc
      ‖hA.inv ∘L Z ∘L B‖ ≤ ‖hA.inv‖ * ‖Z‖ * ‖B‖ :=
        opNorm_comp_comp_le _ _ _
      _ = (‖hA.inv‖ * ‖B‖) * ‖Z‖ := by ring
  have hz : ‖Z‖ = 0 := by nlinarith [norm_nonneg Z]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

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
  classical
  have hratio : ‖hA.inv‖ * ‖B‖ < 1 := by
    calc
      ‖hA.inv‖ * ‖B‖ ≤ (ρ+δ)⁻¹ * ρ := mul_le_mul hAinv hB (norm_nonneg _) (by positivity)
      _ < 1 := by
        rw [inv_mul_lt_one₀ (by linarith : 0 < ρ+δ)]
        linarith
  let Y := sylvesterNeumannSolution N hA B C
  have hYmem := sylvesterNeumannSolution_mem N hA B hC hratio
  have hYeq := sylvesterNeumannSolution_eq N hA B C hratio
  have hXY := sylvester_unique_of_bound_inverse hA B hratio (hEq.trans hYeq.symm)
  subst Y
  refine ⟨hYmem, ?_⟩
  have hseries := N.gauge_tsum_le_geometric
    (gauge_sylvesterNeumannTerm_le N hA B hC) hratio
  calc
    δ * N.gauge X
        ≤ δ * (‖hA.inv‖ * N.gauge C / (1 - ‖hA.inv‖ * ‖B‖)) := by gcongr
    _ ≤ N.gauge C := by
      have hden : δ * ‖hA.inv‖ ≤ 1 - ‖hA.inv‖ * ‖B‖ := by
        calc
          δ * ‖hA.inv‖ + ‖hA.inv‖ * ‖B‖
              = ‖hA.inv‖ * (δ + ‖B‖) := by ring
          _ ≤ (ρ+δ)⁻¹ * (δ+ρ) := by gcongr
          _ = 1 := by field_simp [by linarith : ρ+δ ≠ 0]
        linarith
      exact div_le_iff₀ (sub_pos.mpr hratio) |>.2 (by nlinarith [N.gauge_nonneg C])

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
  classical
  let Nadj := N.adjointFamily
  have hstarEq : B.adjoint ∘L X.adjoint - X.adjoint ∘L A.adjoint = C.adjoint := by
    simpa [ContinuousLinearMap.adjoint_comp, adjoint_sub] using congrArg ContinuousLinearMap.adjoint hEq
  have h := sylvester_mem_and_gauge_le_of_bound_inverse Nadj hB A.adjoint
    hρ hδ hBinv (by simpa using hA) hstarEq (N.adjoint_mem hC)
  constructor
  · simpa using N.adjoint_mem h.1
  · simpa [N.gauge_adjoint] using h.2

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
