/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import Mathlib

/-!
# Davis--Kahan 1970, Section 9: Schur-complement reduction

This file formalizes equations (9.9)--(9.11) independently of the numerical
free-beam realization.  The statement is algebraic and works for arbitrary
modules over a field.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

section SchurComplement

variable {𝕜 E F : Type*}
variable [Field 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]

variable (A₀ : E →ₗ[𝕜] E) (A₁ : F →ₗ[𝕜] F)
variable (B : E →ₗ[𝕜] F) (Bstar : F →ₗ[𝕜] E)
variable (C : F →ₗ[𝕜] F) (lam : 𝕜)

/-- The block operator in equation (9.9). -/
def blockOperator : (E × F) →ₗ[𝕜] (E × F) where
  toFun z := (A₀ z.1 + Bstar z.2, B z.1 + A₁ z.2)
  -- `simp` normalizes both sides to sums in a different association order,
  -- so each component needs an abelian-group rearrangement to close
  map_add' x y := by ext <;> simp <;> abel
  map_smul' c x := by ext <;> simp

@[simp] lemma blockOperator_apply (x : E) (y : F) :
    blockOperator A₀ A₁ B Bstar (x, y) =
      (A₀ x + Bstar y, B x + A₁ y) := rfl

/-- Equation (9.9) is equivalent to its upper and lower block equations. -/
theorem block_eigenproblem_iff (x : E) (y : F) :
    blockOperator A₀ A₁ B Bstar (x, y) = lam • (x, y) ↔
      A₀ x + Bstar y = lam • x ∧ B x + A₁ y = lam • y := by
  simp [blockOperator]

/-- The shifted lower block `lam I - A₁`. -/
def lowerShift : F →ₗ[𝕜] F := lam • LinearMap.id - A₁

lemma lowerShift_apply (y : F) :
    lowerShift A₁ lam y = lam • y - A₁ y := by
  rfl

/-- Equation (9.10): the lower block equation determines the complementary
coordinate after applying a left inverse of `lam I - A₁`. -/
theorem lower_coordinate_eq
    (x : E) (y : F)
    (hbottom : B x + A₁ y = lam • y)
    (hleft : Function.LeftInverse C (lowerShift A₁ lam)) :
    y = C (B x) := by
  have hshift : lowerShift A₁ lam y = B x := by
    rw [lowerShift_apply]
    exact (eq_sub_iff_add_eq.mpr hbottom).symm
  calc
    y = C (lowerShift A₁ lam y) := (hleft y).symm
    _ = C (B x) := congrArg C hshift

/-- Equation (9.11): substituting the complementary coordinate into the upper
block equation yields the reduced eigenproblem on the trial space. -/
theorem reduced_eigenproblem
    (x : E) (y : F)
    (htop : A₀ x + Bstar y = lam • x)
    (hbottom : B x + A₁ y = lam • y)
    (hleft : Function.LeftInverse C (lowerShift A₁ lam)) :
    A₀ x + Bstar (C (B x)) = lam • x := by
  have hy := lower_coordinate_eq A₁ B C lam x y hbottom hleft
  simpa [hy] using htop

/-- A bundled version of equations (9.10) and (9.11). -/
theorem schur_complement_reduction
    (x : E) (y : F)
    (htop : A₀ x + Bstar y = lam • x)
    (hbottom : B x + A₁ y = lam • y)
    (hleft : Function.LeftInverse C (lowerShift A₁ lam)) :
    y = C (B x) ∧ A₀ x + Bstar (C (B x)) = lam • x := by
  exact ⟨lower_coordinate_eq A₁ B C lam x y hbottom hleft,
    reduced_eigenproblem A₀ A₁ B Bstar C lam x y htop hbottom hleft⟩

end SchurComplement

end Section9
end DavisKahan1970
end TauCeti