/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.ExactSinTheta.RectangularIdeals

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
  sorry

/-- Each Neumann term belongs to the same rectangular ideal as `C`. -/
theorem sylvesterNeumannTerm_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C) (n : ℕ) :
    N.Mem (sylvesterNeumannTerm hA B C n) := by
  sorry

/-- Geometric bound for one Neumann term. -/
theorem gauge_sylvesterNeumannTerm_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C) (n : ℕ) :
    N.gauge (sylvesterNeumannTerm hA B C n)
      ≤ ‖hA.inv‖ ^ (n + 1) * N.gauge C * ‖B‖ ^ n := by
  sorry

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
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) : F →L[𝕜] E := by
  sorry

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

/-- Uniqueness under the bound/inverse separation. -/
theorem sylvester_unique_of_bound_inverse
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (hratio : ‖hA.inv‖ * ‖B‖ < 1)
    {X Y : F →L[𝕜] E}
    (hXY : A ∘L X - X ∘L B = A ∘L Y - Y ∘L B) :
    X = Y := by
  sorry

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
