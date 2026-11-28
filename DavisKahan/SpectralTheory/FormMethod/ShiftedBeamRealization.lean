/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

module

public import DavisKahan.SpectralTheory.FormMethod.CoerciveFormResolvent
public import DavisKahan.SpectralTheory.FormMethod.FormCompactness
public import DavisKahan.SpectralTheory.FormMethod.BoundedGraphCompactness
public import DavisKahan.SinTheta.BoundedPerturbation
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Shift
public import Mathlib.Tactic

public section

open _root_.LinearPMap (isSelfAdjoint_perturb_bounded)
open _root_.ContinuousLinearMap (isSelfAdjoint_iff_isSymmetric)

open TauCeti.DavisKahan.Sylvester

/-!
# Shifted coercive realization of the free beam

The unshifted bending form has a two-dimensional affine kernel, so the direct
coercive construction uses

`a₁(u,v) = integral u'' * conj(v'') + integral u * conj(v)`.

Its associated operator is `B + I`.  Subtracting the bounded identity produces
the free-beam operator `B` without changing the domain, self-adjointness, or
compactness of the graph embedding.

This file carries out that assembly abstractly.  The only beam-specific input
is the decomposition of the represented shifted form energy into ambient
`L²` norm plus a nonnegative bending energy.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Analytic


noncomputable section

open Abstract

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

/-- Coercive shifted form together with its bending-energy decomposition. -/
structure ShiftedBeamFormData extends
    Abstract.CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V) where
  bendingEnergy : V → ℝ
  bending_nonnegative : ∀ u, 0 ≤ bendingEnergy u
  form_energy_decomposition : ∀ u,
    RCLike.re ⟪formOperator u, u⟫_𝕜 =
      ‖embed u‖ ^ 2 + bendingEnergy u

namespace ShiftedBeamFormData

/-- The positive self-adjoint operator associated to the shifted beam form. -/
@[expose]
noncomputable def shiftedOperator
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    H →ₗ.[𝕜] H :=
  D.toCoerciveFormData.associatedOperator

/-- The free-beam operator is the shifted realization minus the identity. -/
@[expose]
noncomputable def beamOperator
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    H →ₗ.[𝕜] H :=
  ((-(1 : H →L[𝕜] H)).toLinearMap +ᵥ D.shiftedOperator)

/-- The domain of the shifted beam operator is the form domain. -/
@[simp] theorem beamOperator_domain
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    D.beamOperator.domain = D.shiftedOperator.domain := rfl

/-- The shifted beam operator acts as the form operator plus the identity shift. -/
@[simp] theorem beamOperator_apply
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.beamOperator.domain) :
    D.beamOperator x = D.shiftedOperator x - (x : H) := by
  change -(x : H) + D.shiftedOperator x = D.shiftedOperator x - (x : H)
  rw [sub_eq_add_neg, add_comm]

/-- The inverse of the variational resolvent gives the shifted beam action
at every point in its range. -/
theorem exists_beamOperator_apply_of_resolvent_eq
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    {f x : H} (h : D.resolvent f = x) :
    ∃ hx : x ∈ D.beamOperator.domain, D.beamOperator ⟨x, hx⟩ = f - x := by
  subst x
  let v : D.beamOperator.domain := ⟨D.resolvent f, D.resolvent_mem_associatedOperator_domain f⟩
  refine ⟨v.property, (D.beamOperator_apply v).trans ?_⟩
  exact congrArg (fun z => z - D.resolvent f) (D.toCoerciveFormData.associatedOperator_resolvent f)

/-- The beam realization is the scalar shift used by the resolvent API. -/
theorem beamOperator_eq_subScalar
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    D.beamOperator = D.shiftedOperator.subScalar 1 := by
  refine _root_.LinearPMap.ext (by rw [beamOperator_domain, _root_.LinearPMap.subScalar_domain])
    fun x hx hy => ?_
  refine (D.beamOperator_apply ⟨x, hx⟩).trans ?_
  let u : D.shiftedOperator.domain := ⟨x, D.beamOperator_domain ▸ hx⟩
  let v : D.shiftedOperator.domain :=
    ⟨x, _root_.LinearPMap.subScalar_domain D.shiftedOperator 1 ▸ hy⟩
  have huv : u = v := Subtype.ext rfl
  have h := _root_.LinearPMap.subScalar_apply D.shiftedOperator 1 ⟨x, hy⟩
  rw [one_smul] at h
  change D.shiftedOperator u - x = _
  exact (congrArg (fun w : D.shiftedOperator.domain => D.shiftedOperator w - x) huv).trans h.symm

/-- Form-space representative of a vector in the shifted operator domain. -/
@[expose]
noncomputable def formRepresentative
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.shiftedOperator.domain) : V :=
  D.toCoerciveFormData.solutionOperator
    (D.shiftedOperator x)

/-- The form representative embeds to the original ambient domain vector. -/
theorem embed_formRepresentative
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.shiftedOperator.domain) :
    D.embed (D.formRepresentative x) = (x : H) :=
  (D.resolvent_apply (D.shiftedOperator x)).symm.trans
    (D.toCoerciveFormData.resolvent_associatedOperator_apply x)

/-- The shifted operator quadratic form is the represented shifted form
energy. -/
theorem shifted_quadratic_eq_form_energy
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.shiftedOperator.domain) :
    RCLike.re ⟪D.shiftedOperator x, (x : H)⟫_𝕜 =
      RCLike.re
        ⟪D.formOperator (D.formRepresentative x),
          D.formRepresentative x⟫_𝕜 := by
  have h : ⟪D.shiftedOperator x, D.embed (D.formRepresentative x)⟫_𝕜 =
      D.sesqForm (D.formRepresentative x) (D.formRepresentative x) :=
    D.embed.inner_closedFormOperator D.embed_injective D.embed_dense D.sesqForm
      (x := x) (D.embed_formRepresentative x) (D.formRepresentative x)
  rw [D.embed_formRepresentative x] at h
  exact congrArg RCLike.re (h.trans (D.toCoerciveFormData.sesqForm_apply _ _))

/-- The unshifted beam quadratic form is exactly the bending energy. -/
theorem beam_quadratic_eq_bendingEnergy
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.beamOperator.domain) :
    RCLike.re ⟪D.beamOperator x, (x : H)⟫_𝕜 =
      D.bendingEnergy (D.formRepresentative x) := by
  rw [D.beamOperator_apply]
  rw [inner_sub_left, map_sub, inner_self_eq_norm_sq]
  -- Spelled as a closed equation: `x : D.beamOperator.domain` is only definitionally
  -- `D.shiftedOperator.domain`, so `rw` cannot instantiate the lemma's argument itself.
  rw [show RCLike.re ⟪D.shiftedOperator x, (x : H)⟫_𝕜 =
      RCLike.re ⟪D.formOperator (D.formRepresentative x), D.formRepresentative x⟫_𝕜 from
    D.shifted_quadratic_eq_form_energy x]
  rw [D.form_energy_decomposition]
  -- Closed equation again, for the same reason as the rewrite above.
  rw [show D.embed (D.formRepresentative x) = (x : H) from D.embed_formRepresentative x]
  ring

/-- The free-beam realization is nonnegative. -/
theorem beam_nonnegative
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.beamOperator.domain) :
    0 ≤ RCLike.re ⟪D.beamOperator x, (x : H)⟫_𝕜 := by
  rw [D.beam_quadratic_eq_bendingEnergy]
  exact D.bending_nonnegative _

/-- The shifted form realization is self-adjoint. -/
theorem shiftedOperator_isSelfAdjoint [CompleteSpace H]
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    _root_.IsSelfAdjoint D.shiftedOperator :=
  D.toCoerciveFormData.associatedOperator_isSelfAdjoint

/-- The identity perturbation is symmetric. -/
theorem negIdentity_isSelfAdjointOperator :
    (-(1 : H →L[𝕜] H)).IsSymmetric := by
  intro x y
  simp

/-- Subtracting the identity preserves self-adjointness, so the unshifted free
beam is self-adjoint. -/
theorem beamOperator_isSelfAdjoint [CompleteSpace H]
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    _root_.IsSelfAdjoint D.beamOperator := by
  exact isSelfAdjoint_perturb_bounded D.shiftedOperator_isSelfAdjoint
    (isSelfAdjoint_iff_isSymmetric.mpr negIdentity_isSelfAdjointOperator)

/-- Compact form embedding gives compact graph embedding of the shifted
operator. -/
theorem shiftedOperator_graph_compact
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (hcompact : IsCompactOperator D.embed) :
    Abstract.SequentiallyCompactGraphEmbedding D.shiftedOperator :=
  D.toCoerciveFormData.associatedOperator_graph_compact hcompact

/-- Compact form embedding also gives compact graph embedding of the
unshifted free-beam operator. -/
theorem beamOperator_graph_compact
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (hcompact : IsCompactOperator D.embed) :
    Abstract.SequentiallyCompactGraphEmbedding D.beamOperator := by
  exact Abstract.graphCompact_addBounded
    D.shiftedOperator (-(1 : H →L[𝕜] H))
    (D.shiftedOperator_graph_compact hcompact)

end ShiftedBeamFormData

end

end Analytic
end FreeBeam
end DavisKahan
end TauCeti
