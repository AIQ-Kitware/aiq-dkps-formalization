/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.SpectralTheory.FormMethod.CoerciveFormResolvent
import DavisKahan.SpectralTheory.FormMethod.FormCompactness
import DavisKahan.SpectralTheory.FormMethod.BoundedGraphCompactness
import DavisKahan.SinTheta.BoundedPerturbation
import Mathlib.Tactic

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
namespace Experimental
namespace MathAhead
namespace HiddenFoundations
namespace FreeBeam
namespace Analytic

noncomputable section

open Abstract

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Coercive shifted form together with its bending-energy decomposition. -/
structure ShiftedBeamFormData extends
    Abstract.CoerciveFormData (H := H) (V := V) where
  bendingEnergy : V → ℝ
  bending_nonnegative : ∀ u, 0 ≤ bendingEnergy u
  form_energy_decomposition : ∀ u,
    RCLike.re ⟪formOperator u, u⟫_ℂ =
      ‖embed u‖ ^ 2 + bendingEnergy u

namespace ShiftedBeamFormData

/-- The positive self-adjoint operator associated to the shifted beam form. -/
noncomputable def shiftedOperator
    (D : ShiftedBeamFormData (H := H) (V := V)) :
    DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H) :=
  D.toCoerciveFormData.associatedOperator

/-- The free-beam operator is the shifted realization minus the identity. -/
noncomputable def beamOperator
    (D : ShiftedBeamFormData (H := H) (V := V)) :
    DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H) :=
  D.shiftedOperator.addBounded (-(1 : H →L[ℂ] H))

/-- The domain of the shifted beam operator is the form domain. -/
@[simp] theorem beamOperator_domain
    (D : ShiftedBeamFormData (H := H) (V := V)) :
    D.beamOperator.domain = D.shiftedOperator.domain := rfl

/-- The shifted beam operator acts as the form operator plus the identity shift. -/
@[simp] theorem beamOperator_apply
    (D : ShiftedBeamFormData (H := H) (V := V))
    (x : D.beamOperator.domain) :
    D.beamOperator.toLinearMap x =
      D.shiftedOperator.toLinearMap x - (x : H) := by
  change D.shiftedOperator.toLinearMap x + -(x : H) =
    D.shiftedOperator.toLinearMap x - (x : H)
  rw [sub_eq_add_neg]

/-- Form-space representative of a vector in the shifted operator domain. -/
noncomputable def formRepresentative
    (D : ShiftedBeamFormData (H := H) (V := V))
    (x : D.shiftedOperator.domain) : V :=
  D.toCoerciveFormData.solutionOperator
    (D.shiftedOperator.toLinearMap x)

/-- The form representative embeds to the original ambient domain vector. -/
theorem embed_formRepresentative
    (D : ShiftedBeamFormData (H := H) (V := V))
    (x : D.shiftedOperator.domain) :
    D.embed (D.formRepresentative x) = (x : H) := by
  change D.toCoerciveFormData.resolvent
      (D.shiftedOperator.toLinearMap x) = (x : H)
  exact Abstract.R_inverseClosedOperator_apply
    D.toCoerciveFormData.resolvent
    D.toCoerciveFormData.resolvent_isSelfAdjoint
    D.toCoerciveFormData.resolvent_injective x

/-- The shifted operator quadratic form is the represented shifted form
energy. -/
theorem shifted_quadratic_eq_form_energy
    (D : ShiftedBeamFormData (H := H) (V := V))
    (x : D.shiftedOperator.domain) :
    RCLike.re ⟪D.shiftedOperator.toLinearMap x, (x : H)⟫_ℂ =
      RCLike.re
        ⟪D.formOperator (D.formRepresentative x),
          D.formRepresentative x⟫_ℂ := by
  let f := D.shiftedOperator.toLinearMap x
  have henergy := D.toCoerciveFormData.resolvent_energy_identity f
  have hRx : D.toCoerciveFormData.resolvent f = (x : H) :=
    D.embed_formRepresentative x
  calc
    RCLike.re ⟪f, (x : H)⟫_ℂ =
        RCLike.re ⟪(x : H), f⟫_ℂ := inner_re_symm _ _
    _ = RCLike.re ⟪D.toCoerciveFormData.resolvent f, f⟫_ℂ := by rw [hRx]
    _ = RCLike.re
        ⟪D.formOperator (D.toCoerciveFormData.solutionOperator f),
          D.toCoerciveFormData.solutionOperator f⟫_ℂ :=
      congrArg RCLike.re henergy
    _ = RCLike.re
        ⟪D.formOperator (D.formRepresentative x),
          D.formRepresentative x⟫_ℂ := rfl

/-- The unshifted beam quadratic form is exactly the bending energy. -/
theorem beam_quadratic_eq_bendingEnergy
    (D : ShiftedBeamFormData (H := H) (V := V))
    (x : D.beamOperator.domain) :
    RCLike.re ⟪D.beamOperator.toLinearMap x, (x : H)⟫_ℂ =
      D.bendingEnergy (D.formRepresentative x) := by
  rw [D.beamOperator_apply]
  rw [inner_sub_left, map_sub, inner_self_eq_norm_sq]
  -- Spelled as a closed equation: `x : D.beamOperator.domain` is only definitionally
  -- `D.shiftedOperator.domain`, so `rw` cannot instantiate the lemma's argument itself.
  rw [show RCLike.re ⟪D.shiftedOperator.toLinearMap x, (x : H)⟫_ℂ =
      RCLike.re ⟪D.formOperator (D.formRepresentative x), D.formRepresentative x⟫_ℂ from
    D.shifted_quadratic_eq_form_energy x]
  rw [D.form_energy_decomposition]
  -- Closed equation again, for the same reason as the rewrite above.
  rw [show D.embed (D.formRepresentative x) = (x : H) from D.embed_formRepresentative x]
  ring

/-- The free-beam realization is nonnegative. -/
theorem beam_nonnegative
    (D : ShiftedBeamFormData (H := H) (V := V))
    (x : D.beamOperator.domain) :
    0 ≤ RCLike.re ⟪D.beamOperator.toLinearMap x, (x : H)⟫_ℂ := by
  rw [D.beam_quadratic_eq_bendingEnergy]
  exact D.bending_nonnegative _

/-- The shifted form realization is self-adjoint. -/
theorem shiftedOperator_isSelfAdjoint
    (D : ShiftedBeamFormData (H := H) (V := V)) :
    D.shiftedOperator.IsSelfAdjoint :=
  D.toCoerciveFormData.associatedOperator_isSelfAdjoint

omit [CompleteSpace H] in
/-- The identity perturbation is symmetric. -/
theorem negIdentity_isSelfAdjointOperator :
    IsSelfAdjointOperator (-(1 : H →L[ℂ] H)) := by
  intro x y
  simp

/-- Subtracting the identity preserves self-adjointness, so the unshifted free
beam is self-adjoint. -/
theorem beamOperator_isSelfAdjoint
    (D : ShiftedBeamFormData (H := H) (V := V)) :
    D.beamOperator.IsSelfAdjoint := by
  exact addBounded_isSelfAdjoint
    D.shiftedOperator D.shiftedOperator_isSelfAdjoint
    (-(1 : H →L[ℂ] H)) negIdentity_isSelfAdjointOperator

/-- Compact form embedding gives compact graph embedding of the shifted
operator. -/
theorem shiftedOperator_graph_compact
    (D : ShiftedBeamFormData (H := H) (V := V))
    (hcompact : Abstract.SequentiallyCompactEmbedding D.embed) :
    Abstract.SequentiallyCompactGraphEmbedding D.shiftedOperator :=
  D.toCoerciveFormData.associatedOperator_graph_compact hcompact

/-- Compact form embedding also gives compact graph embedding of the
unshifted free-beam operator. -/
theorem beamOperator_graph_compact
    (D : ShiftedBeamFormData (H := H) (V := V))
    (hcompact : Abstract.SequentiallyCompactEmbedding D.embed) :
    Abstract.SequentiallyCompactGraphEmbedding D.beamOperator := by
  exact Abstract.graphCompact_addBounded
    D.shiftedOperator (-(1 : H →L[ℂ] H))
    (D.shiftedOperator_graph_compact hcompact)

end ShiftedBeamFormData

end

end Analytic
end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti