/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Abstract.BoundedInverseRealization
import ForMathlib.Analysis.InnerProductSpace.CoerciveUnit
import Mathlib.Tactic

/-!
# Bounded resolvent produced by a coercive form operator

A convenient Hilbert-space version of the form method is encoded by a dense
continuous embedding `j : V → H` and a bounded positive coercive self-adjoint
operator `A : V → V` representing the form.  The variational solution is

`u = A⁻¹ j* f`,

and the ambient solution operator is

`R = j A⁻¹ j*`.

This file constructs `R`, proves the variational identity, positivity,
self-adjointness, and injectivity, then invokes `BoundedInverseRealization` to
produce the associated positive self-adjoint unbounded operator.

The free-beam specialization takes `V` to be an `H²` form space and `A` to
represent the shifted bending form.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations
namespace FreeBeam
namespace Abstract

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Data for a coercive symmetric form represented by a bounded operator on a
form Hilbert space. -/
structure CoerciveFormData where
  embed : V →L[ℂ] H
  embed_injective : Function.Injective embed
  embed_dense : DenseRange embed
  embed_adjoint_injective : Function.Injective embed.adjoint
  formOperator : V →L[ℂ] V
  form_selfAdjoint : IsSelfAdjoint formOperator
  coercivityConstant : ℝ
  coercivity_pos : 0 < coercivityConstant
  coercive : ∀ u : V,
    coercivityConstant * ‖u‖ ^ 2 ≤
      RCLike.re ⟪formOperator u, u⟫_ℂ

namespace CoerciveFormData

/-- Coercivity makes the form operator invertible in the bounded-operator
algebra. -/
theorem formOperator_isUnit (D : CoerciveFormData (H := H) (V := V)) :
    IsUnit D.formOperator :=
  ContinuousLinearMap.isUnit_of_coercive D.coercivity_pos D.coercive

/-- Bounded inverse of the represented form operator. -/
noncomputable def formInverse (D : CoerciveFormData (H := H) (V := V)) :
    V →L[ℂ] V :=
  Ring.inverse D.formOperator

/-- Variational solution map from ambient forcing to the form space. -/
noncomputable def solutionOperator
    (D : CoerciveFormData (H := H) (V := V)) :
    H →L[ℂ] V :=
  D.formInverse ∘L D.embed.adjoint

/-- Ambient bounded resolvent produced by the form method. -/
noncomputable def resolvent
    (D : CoerciveFormData (H := H) (V := V)) :
    H →L[ℂ] H :=
  D.embed ∘L D.solutionOperator

@[simp] theorem solutionOperator_apply
    (D : CoerciveFormData (H := H) (V := V)) (f : H) :
    D.solutionOperator f = D.formInverse (D.embed.adjoint f) := rfl

@[simp] theorem resolvent_apply
    (D : CoerciveFormData (H := H) (V := V)) (f : H) :
    D.resolvent f = D.embed (D.solutionOperator f) := rfl

/-- Applying the form operator to the variational solution returns the adjoint
embedding of the forcing. -/
theorem formOperator_solutionOperator
    (D : CoerciveFormData (H := H) (V := V)) (f : H) :
    D.formOperator (D.solutionOperator f) = D.embed.adjoint f := by
  have hmul : D.formOperator * Ring.inverse D.formOperator = 1 :=
    Ring.mul_inverse_cancel D.formOperator D.formOperator_isUnit
  have happ := DFunLike.congr_fun hmul (D.embed.adjoint f)
  simpa [solutionOperator, formInverse] using happ

/-- The solution operator is injective because the adjoint embedding is
injective. -/
theorem solutionOperator_injective
    (D : CoerciveFormData (H := H) (V := V)) :
    Function.Injective D.solutionOperator := by
  intro f g hfg
  apply D.embed_adjoint_injective
  rw [← D.formOperator_solutionOperator f,
    ← D.formOperator_solutionOperator g, hfg]

/-- Variational identity in inner-product form. -/
theorem variational_identity
    (D : CoerciveFormData (H := H) (V := V))
    (f : H) (v : V) :
    ⟪D.formOperator (D.solutionOperator f), v⟫_ℂ =
      ⟪f, D.embed v⟫_ℂ := by
  rw [D.formOperator_solutionOperator]
  exact ContinuousLinearMap.adjoint_inner_left D.embed v f

/-- The ambient form resolvent is injective. -/
theorem resolvent_injective
    (D : CoerciveFormData (H := H) (V := V)) :
    Function.Injective D.resolvent := by
  intro f g hfg
  apply D.solutionOperator_injective
  apply D.embed_injective
  exact hfg

/-- The ambient form resolvent is symmetric. -/
theorem resolvent_isSymmetric
    (D : CoerciveFormData (H := H) (V := V)) :
    D.resolvent.IsSymmetric := by
  intro f g
  let u := D.solutionOperator f
  let v := D.solutionOperator g
  calc
    ⟪D.resolvent f, g⟫_ℂ = ⟪u, D.embed.adjoint g⟫_ℂ := by
      rw [resolvent_apply]
      simpa [u] using
        (ContinuousLinearMap.adjoint_inner_right D.embed u g).symm
    _ = ⟪u, D.formOperator v⟫_ℂ := by
      rw [D.formOperator_solutionOperator g]
    _ = ⟪D.formOperator u, v⟫_ℂ := by
      exact D.form_selfAdjoint.isSymmetric u v |>.symm
    _ = ⟪D.embed.adjoint f, v⟫_ℂ := by
      rw [D.formOperator_solutionOperator f]
    _ = ⟪f, D.resolvent g⟫_ℂ := by
      rw [resolvent_apply]
      exact ContinuousLinearMap.adjoint_inner_left D.embed v f

/-- The ambient form resolvent is self-adjoint. -/
theorem resolvent_isSelfAdjoint
    (D : CoerciveFormData (H := H) (V := V)) :
    IsSelfAdjoint D.resolvent :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr D.resolvent_isSymmetric

/-- The resolvent quadratic form is the represented form energy of its
variational solution. -/
theorem resolvent_energy_identity
    (D : CoerciveFormData (H := H) (V := V)) (f : H) :
    ⟪D.resolvent f, f⟫_ℂ =
      ⟪D.formOperator (D.solutionOperator f), D.solutionOperator f⟫_ℂ := by
  calc
    ⟪D.resolvent f, f⟫_ℂ =
        ⟪D.solutionOperator f, D.embed.adjoint f⟫_ℂ := by
      rw [resolvent_apply]
      exact (ContinuousLinearMap.adjoint_inner_right D.embed
        (D.solutionOperator f) f).symm
    _ = ⟪D.solutionOperator f,
        D.formOperator (D.solutionOperator f)⟫_ℂ := by
      rw [D.formOperator_solutionOperator]
    _ = ⟪D.formOperator (D.solutionOperator f),
        D.solutionOperator f⟫_ℂ := by
      exact D.form_selfAdjoint.isSymmetric _ _ |>.symm

/-- The ambient form resolvent is positive. -/
theorem resolvent_nonnegative
    (D : CoerciveFormData (H := H) (V := V)) (f : H) :
    0 ≤ RCLike.re ⟪D.resolvent f, f⟫_ℂ := by
  rw [D.resolvent_energy_identity]
  exact le_trans
    (mul_nonneg D.coercivity_pos.le (sq_nonneg ‖D.solutionOperator f‖))
    (D.coercive (D.solutionOperator f))

/-- Closed positive self-adjoint operator associated to the coercive form. -/
noncomputable def associatedOperator
    (D : CoerciveFormData (H := H) (V := V)) :
    DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H) :=
  inverseClosedOperator D.resolvent D.resolvent_isSelfAdjoint
    D.resolvent_injective

/-- The associated unbounded operator is self-adjoint. -/
theorem associatedOperator_isSelfAdjoint
    (D : CoerciveFormData (H := H) (V := V)) :
    D.associatedOperator.IsSelfAdjoint :=
  inverseClosedOperator_isSelfAdjoint
    D.resolvent D.resolvent_isSelfAdjoint D.resolvent_injective
    D.resolvent_nonnegative

/-- The form resolvent is the inverse of the associated operator on its domain. -/
@[simp] theorem associatedOperator_resolvent
    (D : CoerciveFormData (H := H) (V := V)) (f : H) :
    D.associatedOperator.toLinearMap
      ⟨D.resolvent f,
        LinearMap.mem_range_self D.resolvent.toLinearMap f⟩ = f := by
  exact inverseClosedOperator_apply_R
    D.resolvent D.resolvent_isSelfAdjoint D.resolvent_injective f

end CoerciveFormData

end

end Abstract
end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end ForMathlib
