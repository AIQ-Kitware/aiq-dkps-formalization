/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Symmetric
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily

/-!
# Gauge transport through two-way contraction factorizations

Many ideal equalities needed by the paper do not require a unitary extension.
It is enough to factor each operator through the other using contractions.
This applies to polar partial isometries, reflections, inclusions, projections,
and zero-extended rectangular blocks.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace SharedFoundations

open scoped InnerProductSpace
open ExactSinTheta

universe u

section Square

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A square ideal member remains in the ideal after a displayed two-sided
factorization. -/
theorem SymmetricNormIdeal.mem_of_eq_comp_comp
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B L R : E →L[𝕜] E}
    (hB : I.mem B) (hEq : A = L ∘L B ∘L R) : I.mem A := by
  rw [hEq]
  exact I.ideal_mem L R hB

/-- Gauge control from a two-sided factorization. -/
theorem SymmetricNormIdeal.gauge_le_of_eq_comp_comp
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B L R : E →L[𝕜] E}
    (hB : I.mem B) (hEq : A = L ∘L B ∘L R) :
    I.gauge A ≤ ‖L‖ * I.gauge B * ‖R‖ := by
  rw [hEq]
  exact I.ideal_bound L R hB

/-- A contraction factorization does not increase the square ideal gauge. -/
theorem SymmetricNormIdeal.gauge_le_of_contraction_factorization
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B L R : E →L[𝕜] E}
    (hB : I.mem B) (hEq : A = L ∘L B ∘L R)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    I.gauge A ≤ I.gauge B := by
  have hraw := SymmetricNormIdeal.gauge_le_of_eq_comp_comp I hB hEq
  have hnonneg : 0 ≤ I.gauge B := I.nonneg hB
  calc
    I.gauge A ≤ ‖L‖ * I.gauge B * ‖R‖ := hraw
    _ ≤ 1 * I.gauge B * 1 := by gcongr
    _ = I.gauge B := by ring

/-- Two contraction factorizations give equivalent membership. -/
theorem SymmetricNormIdeal.mem_iff_of_twoWayContractions
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B L R L' R' : E →L[𝕜] E}
    (hAB : A = L ∘L B ∘L R)
    (hBA : B = L' ∘L A ∘L R') :
    I.mem A ↔ I.mem B := by
  constructor
  · intro hA
    exact SymmetricNormIdeal.mem_of_eq_comp_comp I hA hBA
  · intro hB
    exact SymmetricNormIdeal.mem_of_eq_comp_comp I hB hAB

/-- Two contraction factorizations give equal gauges. -/
theorem SymmetricNormIdeal.gauge_eq_of_twoWayContractions
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B L R L' R' : E →L[𝕜] E}
    (hAB : A = L ∘L B ∘L R)
    (hBA : B = L' ∘L A ∘L R')
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hL' : ‖L'‖ ≤ 1) (hR' : ‖R'‖ ≤ 1)
    (hA : I.mem A) :
    I.gauge A = I.gauge B := by
  have hB : I.mem B := SymmetricNormIdeal.mem_of_eq_comp_comp I hA hBA
  apply le_antisymm
  · exact SymmetricNormIdeal.gauge_le_of_contraction_factorization I hB hAB hL hR
  · exact SymmetricNormIdeal.gauge_le_of_contraction_factorization I hA hBA hL' hR'

/-- Combined square membership and gauge transport. -/
theorem SymmetricNormIdeal.mem_iff_and_gauge_eq_of_twoWayContractions
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B L R L' R' : E →L[𝕜] E}
    (hAB : A = L ∘L B ∘L R)
    (hBA : B = L' ∘L A ∘L R')
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hL' : ‖L'‖ ≤ 1) (hR' : ‖R'‖ ≤ 1)
    (hA : I.mem A) :
    I.mem B ∧ I.gauge B = I.gauge A := by
  have hB : I.mem B := SymmetricNormIdeal.mem_of_eq_comp_comp I hA hBA
  refine ⟨hB, ?_⟩
  exact (SymmetricNormIdeal.gauge_eq_of_twoWayContractions I hAB hBA hL hR hL' hR' hA).symm

end Square

section Rectangular

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G H : Type u}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Rectangular membership transport through a displayed factorization. -/
theorem RectangularSymmetricIdealFamily.mem_of_eq_comp_comp
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : H →L[𝕜] G} {B : E →L[𝕜] F}
    (L : F →L[𝕜] G) (R : H →L[𝕜] E)
    (hB : N.Mem B) (hEq : A = L ∘L B ∘L R) : N.Mem A := by
  rw [hEq]
  exact N.comp_mem L R hB

/-- Rectangular gauge control through a displayed factorization. -/
theorem RectangularSymmetricIdealFamily.gauge_le_of_eq_comp_comp
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : H →L[𝕜] G} {B : E →L[𝕜] F}
    (L : F →L[𝕜] G) (R : H →L[𝕜] E)
    (hB : N.Mem B) (hEq : A = L ∘L B ∘L R) :
    N.gauge A ≤ ‖L‖ * N.gauge B * ‖R‖ := by
  rw [hEq]
  exact N.gauge_comp_le L R hB

/-- A rectangular contraction factorization does not increase the gauge. -/
theorem RectangularSymmetricIdealFamily.gauge_le_of_contraction_factorization
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : H →L[𝕜] G} {B : E →L[𝕜] F}
    (L : F →L[𝕜] G) (R : H →L[𝕜] E)
    (hB : N.Mem B) (hEq : A = L ∘L B ∘L R)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    N.gauge A ≤ N.gauge B := by
  have hraw := RectangularSymmetricIdealFamily.gauge_le_of_eq_comp_comp N L R hB hEq
  have hnonneg := N.gauge_nonneg hB
  calc
    N.gauge A ≤ ‖L‖ * N.gauge B * ‖R‖ := hraw
    _ ≤ 1 * N.gauge B * 1 := by gcongr
    _ = N.gauge B := by ring

end Rectangular

end SharedFoundations
end Scratch
end Experimental
end DavisKahan
end ForMathlib
