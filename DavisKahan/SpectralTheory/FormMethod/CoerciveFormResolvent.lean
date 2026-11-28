/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Inverse
public import Mathlib.Tactic

/-!
# Bounded resolvent produced by a coercive form operator

A convenient Hilbert-space version of the form method is encoded by a dense
continuous embedding `j : V → H` and a bounded positive coercive self-adjoint
operator `A : V → V` representing the form.  The variational solution is

`u = A⁻¹ j* f`,

and the ambient solution operator is

`R = j A⁻¹ j*`.

TauCeti’s Lax–Milgram solution maps give `u` and `R`. The associated
operator is the canonical closed-form operator. Its equality with the partial
inverse of `R` supplies the compact-inverse spectrum formula.

The free-beam specialization takes `V` to be an `H²` form space and `A` to
represent the shifted bending form.

The scalar field is an arbitrary `RCLike` `𝕜`, so the whole form method is
available over `ℝ` as well as over `ℂ`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

open TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

/-- Data for a coercive symmetric form represented by a bounded operator on a
form Hilbert space. -/
structure CoerciveFormData where
  embed : V →L[𝕜] H
  embed_injective : Function.Injective embed
  embed_dense : DenseRange embed
  formOperator : V →L[𝕜] V
  form_selfAdjoint : IsSelfAdjoint formOperator
  coercivityConstant : ℝ
  coercivity_pos : 0 < coercivityConstant
  coercive : ∀ u : V,
    coercivityConstant * ‖u‖ ^ 2 ≤
      RCLike.re ⟪formOperator u, u⟫_𝕜

namespace CoerciveFormData

/-- The bounded sesquilinear form represented by the form operator. -/
@[expose]
noncomputable def sesqForm (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    V →L⋆[𝕜] V →L[𝕜] 𝕜 :=
  D.formOperator.adjoint.toSesqForm

omit [CompleteSpace H] in
/-- Evaluation of the form represented by the bounded operator. -/
theorem sesqForm_apply (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (u v : V) :
    D.sesqForm u v = ⟪D.formOperator u, v⟫_𝕜 := by
  rw [sesqForm, ContinuousLinearMap.toSesqForm_apply_coe, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  exact ContinuousLinearMap.adjoint_inner_right D.formOperator u v

omit [CompleteSpace H] in
private theorem sesqForm_hermitian (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (u v : V) :
    D.sesqForm u v = star (D.sesqForm v u) := by
  rw [D.sesqForm_apply, D.sesqForm_apply]
  exact (D.form_selfAdjoint.isSymmetric u v).trans (inner_conj_symm u (D.formOperator v)).symm

omit [CompleteSpace H] in
/-- Coercivity makes the Fréchet–Riesz operator of the form invertible. -/
theorem sesqForm_isUnit (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    IsUnit (InnerProductSpace.continuousLinearMapOfBilin D.sesqForm) :=
  InnerProductSpace.isUnit_continuousLinearMapOfBilin_of_coercive D.sesqForm D.coercivity_pos
    (fun u => (D.sesqForm_apply u u).symm ▸ D.coercive u)

/-- Variational solution map from ambient forcing to the form space. -/
@[expose]
noncomputable def solutionOperator (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    H →L[𝕜] V :=
  InnerProductSpace.formSolutionMap D.sesqForm D.sesqForm_isUnit D.embed

/-- Ambient bounded solution operator of the form problem. -/
@[expose]
noncomputable def resolvent (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    H →L[𝕜] H :=
  InnerProductSpace.formSolutionOperator D.sesqForm D.sesqForm_isUnit D.embed

omit [CompleteSpace H] in
/-- The ambient solution is the embedded form-space solution. -/
@[simp] theorem resolvent_apply (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) :
    D.resolvent f = D.embed (D.solutionOperator f) :=
  InnerProductSpace.formSolutionOperator_apply _ _ _ _

omit [CompleteSpace H] in
/-- Variational identity in inner-product form. -/
theorem variational_identity
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) (v : V) :
    ⟪D.formOperator (D.solutionOperator f), v⟫_𝕜 = ⟪f, D.embed v⟫_𝕜 :=
  (D.sesqForm_apply _ _).symm.trans
    (InnerProductSpace.apply_formSolutionMap D.sesqForm D.sesqForm_isUnit D.embed f v)

/-- Applying the form operator to the variational solution returns the adjoint
embedding of the forcing. -/
theorem formOperator_solutionOperator
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) :
    D.formOperator (D.solutionOperator f) = D.embed.adjoint f :=
  ext_inner_right 𝕜 fun v => (D.variational_identity f v).trans
    (ContinuousLinearMap.adjoint_inner_left D.embed v f).symm

omit [CompleteSpace H] in
/-- The ambient solution operator is injective. -/
theorem resolvent_injective (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    Function.Injective D.resolvent :=
  InnerProductSpace.formSolutionOperator_injective D.sesqForm D.sesqForm_isUnit
    (fun u hu => by
      apply norm_eq_zero.mp
      have h := D.coercive u
      rw [← D.sesqForm_apply, hu, map_zero] at h
      by_contra hn
      exact (not_lt_of_ge h) (mul_pos D.coercivity_pos (sq_pos_of_ne_zero hn)))
    D.embed_dense

/-- The ambient solution operator is self-adjoint. -/
theorem resolvent_isSelfAdjoint (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    IsSelfAdjoint D.resolvent :=
  InnerProductSpace.isSelfAdjoint_formSolutionOperator D.sesqForm D.sesqForm_isUnit
    D.embed D.sesqForm_hermitian

/-- The closed operator represented by the coercive form. -/
@[expose]
noncomputable def associatedOperator (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    H →ₗ.[𝕜] H :=
  D.embed.closedFormOperator D.embed_injective D.embed_dense D.sesqForm

/-- Self-adjointness from TauCeti’s first representation theorem at shift zero. -/
theorem associatedOperator_isSelfAdjoint
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    IsSelfAdjoint D.associatedOperator :=
  D.embed.isSelfAdjoint_closedFormOperator D.embed_injective D.embed_dense D.sesqForm
    D.sesqForm_hermitian (α := 0)
    (by simpa only [ContinuousLinearMap.shiftedForm_zero] using D.sesqForm_isUnit)

omit [CompleteSpace H] in
/-- The coercive-form realization is the partial inverse of its ambient
solution operator. -/
theorem associatedOperator_eq_inverse (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    D.associatedOperator = (D.resolvent.toLinearMap.toPMap ⊤).inverse := by
  symm
  apply D.embed.eq_closedFormOperator_of_mem_graph_iff D.embed_injective D.embed_dense D.sesqForm
  intro x f
  rw [D.resolvent.mem_graph_inverse_toPMap_top_iff D.resolvent_injective]
  constructor
  · intro h
    exact ⟨D.solutionOperator f, (D.resolvent_apply f).symm.trans h,
      InnerProductSpace.apply_formSolutionMap _ _ _ _⟩
  · rintro ⟨u, hu, hf⟩
    exact (D.resolvent_apply f).trans <|
      (congrArg D.embed
        (InnerProductSpace.eq_formSolutionMap D.sesqForm D.sesqForm_isUnit D.embed hf).symm).trans hu

omit [CompleteSpace H] in
/-- The ambient solution lies in the represented operator domain. -/
theorem resolvent_mem_associatedOperator_domain
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) :
    D.resolvent f ∈ D.associatedOperator.domain := by
  rw [D.resolvent_apply f]
  exact D.embed.apply_mem_domain_closedFormOperator D.embed_injective D.embed_dense D.sesqForm
    (InnerProductSpace.apply_formSolutionMap _ _ _ _)

omit [CompleteSpace H] in
/-- The associated operator recovers the forcing. -/
@[simp] theorem associatedOperator_resolvent
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) :
    D.associatedOperator ⟨D.resolvent f, D.resolvent_mem_associatedOperator_domain f⟩ = f :=
  D.embed.closedFormOperator_apply_eq D.embed_injective D.embed_dense D.sesqForm
    (D.resolvent_apply f).symm
    (InnerProductSpace.apply_formSolutionMap _ _ _ _)

omit [CompleteSpace H] in
/-- The ambient solution operator recovers every vector in the operator domain. -/
theorem resolvent_associatedOperator_apply
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (x : D.associatedOperator.domain) :
    D.resolvent (D.associatedOperator x) = (x : H) := by
  let f := D.associatedOperator x
  have h : ((x : H), f) ∈ D.associatedOperator.graph := D.associatedOperator.mem_graph x
  rw [congrArg (fun A : H →ₗ.[𝕜] H => A.graph) D.associatedOperator_eq_inverse,
    D.resolvent.mem_graph_inverse_toPMap_top_iff D.resolvent_injective] at h
  exact h

end CoerciveFormData

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
