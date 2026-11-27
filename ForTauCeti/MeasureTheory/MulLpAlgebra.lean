/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.MeasureTheory.RadonNikodymL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Algebra of multiplication by bounded representatives

Pointwise identities of the representatives identify their `L∞` classes.
The algebra and adjoint laws for the resulting operators are TauCeti's
native multiplication laws.
-/

public section

open MeasureTheory
open scoped ComplexConjugate ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] (ρ : Measure α)

/-- A bounded symbol equal to `1` almost everywhere acts as the identity. -/
theorem mulLp_eq_one {h : α → ℂ} (hh : Measurable h) {C : ℝ} (hhC : ∀ x, ‖h x‖ ≤ C)
    (heq : ∀ᵐ x ∂ρ, h x = 1) :
    Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ hh hhC) = 1 := by
  have h := Lp.multiplicationOperator_of_ae_eq_const (E := ℂ) (p := 2)
    ((coeFn_boundedSymbolLp ρ hh hhC).trans heq)
  simpa only [one_smul, ContinuousLinearMap.one_def] using h

/-- A bounded symbol equal to zero almost everywhere acts as zero. -/
theorem mulLp_eq_zero {h : α → ℂ} (hh : Measurable h) {C : ℝ} (hhC : ∀ x, ‖h x‖ ≤ C)
    (heq : ∀ᵐ x ∂ρ, h x = 0) :
    Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ hh hhC) = 0 := by
  have heq' : h =ᵐ[ρ] (0 : α → ℂ) := heq
  have h : boundedSymbolLp ρ hh hhC = 0 :=
    Lp.ext ((coeFn_boundedSymbolLp ρ hh hhC).trans (heq'.trans (Lp.coeFn_zero _ _ _).symm))
  rw [h, Lp.multiplicationOperator_zero]

/-- An almost-everywhere sum of bounded representatives gives the sum of the operators. -/
theorem mulLp_eq_add {g₁ g₂ h : α → ℂ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (hh : Measurable h) {C₁ C₂ C : ℝ} (hg₁C : ∀ x, ‖g₁ x‖ ≤ C₁) (hg₂C : ∀ x, ‖g₂ x‖ ≤ C₂)
    (hhC : ∀ x, ‖h x‖ ≤ C) (heq : ∀ᵐ x ∂ρ, h x = g₁ x + g₂ x) :
    Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ hh hhC) =
      Lp.multiplicationOperator (boundedSymbolLp ρ hg₁ hg₁C) +
        Lp.multiplicationOperator (boundedSymbolLp ρ hg₂ hg₂C) := by
  rw [← Lp.multiplicationOperator_add]
  congr 1
  refine Lp.ext ?_
  filter_upwards [coeFn_boundedSymbolLp ρ hh hhC, coeFn_boundedSymbolLp ρ hg₁ hg₁C,
    coeFn_boundedSymbolLp ρ hg₂ hg₂C, Lp.coeFn_add
      (boundedSymbolLp ρ hg₁ hg₁C) (boundedSymbolLp ρ hg₂ hg₂C), heq] with x h₁ h₂ h₃ h₄ hx
  rw [h₁, h₄, Pi.add_apply, h₂, h₃, hx]

/-- A bounded representative of a constant acts by the scalar embedding. -/
theorem mulLp_eq_algebraMap {h : α → ℂ} (hh : Measurable h) {C : ℝ} (hhC : ∀ x, ‖h x‖ ≤ C)
    (c : ℂ) (heq : ∀ᵐ x ∂ρ, h x = c) :
    Lp.multiplicationOperator (boundedSymbolLp ρ hh hhC) =
      algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) c := by
  rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def]
  exact Lp.multiplicationOperator_of_ae_eq_const ((coeFn_boundedSymbolLp ρ hh hhC).trans heq)

/-- An almost-everywhere product of representatives gives composition of the operators. -/
theorem mulLp_eq_comp {g₁ g₂ h : α → ℂ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (hh : Measurable h) {C₁ C₂ C : ℝ} (hg₁C : ∀ x, ‖g₁ x‖ ≤ C₁) (hg₂C : ∀ x, ‖g₂ x‖ ≤ C₂)
    (hhC : ∀ x, ‖h x‖ ≤ C) (heq : ∀ᵐ x ∂ρ, h x = g₁ x * g₂ x) :
    Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ hh hhC) =
      (Lp.multiplicationOperator (boundedSymbolLp ρ hg₁ hg₁C)).comp
        (Lp.multiplicationOperator (boundedSymbolLp ρ hg₂ hg₂C)) := by
  rw [Lp.multiplicationOperator_comp_multiplicationOperator]
  congr 1
  refine Lp.ext ?_
  filter_upwards [coeFn_boundedSymbolLp ρ hh hhC, coeFn_boundedSymbolLp ρ hg₁ hg₁C,
    coeFn_boundedSymbolLp ρ hg₂ hg₂C, Lp.coeFn_mul
      (boundedSymbolLp ρ hg₁ hg₁C) (boundedSymbolLp ρ hg₂ hg₂C), heq] with x h₁ h₂ h₃ h₄ hx
  rw [h₁, h₄, Pi.mul_apply, h₂, h₃, hx]

/-- The operator norm is bounded by the absolute value of a uniform pointwise bound. -/
theorem norm_mulLp_le {g : α → ℂ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    ‖Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ hg hgC)‖ ≤ |C| :=
  (Lp.norm_multiplicationOperator_le _).trans (norm_boundedSymbolLp_le ρ hg hgC)

/-- The adjoint is multiplication by an almost-everywhere conjugate representative. -/
theorem star_mulLp {g h : α → ℂ} (hg : Measurable g) (hh : Measurable h) {Cg C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ Cg) (hhC : ∀ x, ‖h x‖ ≤ C) (heq : ∀ᵐ x ∂ρ, h x = conj (g x)) :
    star (Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ hg hgC)) =
      Lp.multiplicationOperator (boundedSymbolLp ρ hh hhC) := by
  rw [ContinuousLinearMap.star_eq_adjoint, Lp.adjoint_multiplicationOperator]
  congr 1
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (boundedSymbolLp ρ hg hgC), coeFn_boundedSymbolLp ρ hg hgC,
    coeFn_boundedSymbolLp ρ hh hhC, heq] with x h₁ h₂ h₃ hx
  rw [h₁, Pi.star_apply, h₂, h₃, hx, RCLike.star_def]

/-- Conjugation of a product by a symbol conjugates both the symbol and the vector. -/
theorem star_multiplicationOperator_apply (a : Lp ℂ ∞ ρ) (F : Lp ℂ 2 ρ) :
    star (Lp.multiplicationOperator a F) = Lp.multiplicationOperator (star a) (star F) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (Lp.multiplicationOperator a F), Lp.multiplicationOperator_ae a F,
    Lp.multiplicationOperator_ae (star a) (star F), Lp.coeFn_star a, Lp.coeFn_star F]
    with x h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₃, Pi.star_apply, h₂, h₄, h₅, Pi.star_apply, Pi.star_apply, smul_eq_mul,
    smul_eq_mul, star_mul, mul_comm]

/-- Scalar multiplication operators on complex `L²` are normal. -/
theorem isStarNormal_mulLp {g : α → ℂ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    IsStarNormal (Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ hg hgC)) := by
  refine ⟨?_⟩
  rw [ContinuousLinearMap.star_eq_adjoint, Lp.adjoint_multiplicationOperator]
  exact (Lp.commute_multiplicationOperator (star (boundedSymbolLp ρ hg hgC))
    (boundedSymbolLp ρ hg hgC)).eq

end TauCeti
