/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/

import ForTauCeti.Analysis.InnerProductSpace.PolarPartialIsometry

/-!
# Final-space identities for the bounded polar isometry

The nonacute direct-rotation development needs the *final* projection identity
`U U⋆ = P_(closure range T)` alongside the initial one `U⋆ U = P_(closure range |T|)`,
together with the unitary `polarPartialFinalEquiv` between the two spaces.

Both now come straight from
`ForTauCeti/Analysis/InnerProductSpace/PolarPartialIsometry.lean`, which develops the
general bounded polar decomposition — rectangular, infinite-dimensional, no invertibility
hypothesis — over our own `ContinuousLinearMap.modulus`.  This module is the thin
square-case naming layer the Davis--Kahan geometry reads.

## History

Until 2026-07-28 this file obtained the polar decomposition from `vendor/Spectra`
(`Spectra.QuantumMechanics.Channels`) and, worse, **declared its own contents into that
vendored namespace**, so eight Davis--Kahan results were indistinguishable from Spectra's
own API.  Both problems are gone: the mathematics is ours, and the declarations live in the
Davis--Kahan namespace with the rest of the geometry development.

The replacement is a strict generalisation rather than a transcription.  The two
constructions coincide — both extend `|T| x ↦ T x` from the dense range of the modulus —
but the ForTauCeti one is stated for `E →L[ℂ] F` with independent source and target, and it
proves the uniqueness characterisation that makes `adjoint_polarIsometry` a three-line
consequence instead of a 140-line argument.  That characterisation is also what lets
`DavisKahan/Interop/Spectra/OperatorAbsoluteValue.lean` identify the Spectra-backed polar
isometry with ours, so nothing downstream had to choose between the two.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The final space in the bounded polar decomposition, `closure (range T)`. -/
abbrev polarFinalRange (T : H →L[ℂ] H) : Submodule ℂ H := T.polarFinal

/-- The initial space in the bounded polar decomposition, `closure (range |T|)`. -/
abbrev polarRange (T : H →L[ℂ] H) : Submodule ℂ H := T.polarInitial

/-- The polar partial isometry `U : H →L[ℂ] H`. -/
abbrev polarIsometry (T : H →L[ℂ] H) : H →L[ℂ] H := T.polarPartial

/-- The isometry `K → H`, `|T| x ↦ T x`, on the initial space. -/
abbrev polarPartial (T : H →L[ℂ] H) : T.polarInitial →L[ℂ] H := T.polarPartialAux

/-- The modulus `|T|`. -/
abbrev absOp (T : H →L[ℂ] H) : H →L[ℂ] H := T.modulus

/-- The modulus, corestricted to the initial space. -/
abbrev absOpCorestrict (T : H →L[ℂ] H) : H →ₗ[ℂ] T.polarInitial := T.modulusCorestrict

theorem absOp_isSelfAdjoint (T : H →L[ℂ] H) : IsSelfAdjoint (absOp T) :=
  T.modulus_isSelfAdjoint

theorem absOp_nonneg (T : H →L[ℂ] H) : 0 ≤ absOp T := T.modulus_nonneg

theorem absOp_mem_polarRange (T : H →L[ℂ] H) (x : H) : absOp T x ∈ polarRange T :=
  T.modulus_apply_mem_polarInitial x

theorem norm_absOp_apply (T : H →L[ℂ] H) (x : H) : ‖absOp T x‖ = ‖T x‖ :=
  T.norm_modulus_apply x

theorem denseRange_absOpCorestrict (T : H →L[ℂ] H) : DenseRange (absOpCorestrict T) :=
  T.denseRange_modulusCorestrict

theorem polarPartial_absOpCorestrict (T : H →L[ℂ] H) (x : H) :
    polarPartial T (absOpCorestrict T x) = T x :=
  T.polarPartialAux_modulusCorestrict x

theorem norm_polarPartial_eq (T : H →L[ℂ] H) (x : T.polarInitial) :
    ‖polarPartial T x‖ = ‖x‖ :=
  T.norm_polarPartialAux_apply x

theorem polarIsometry_apply_eq (T : H →L[ℂ] H) (w : H) :
    polarIsometry T w = polarPartial T (T.polarInitial.orthogonalProjectionOnto w) := rfl

@[simp] theorem polarIsometry_absOp (T : H →L[ℂ] H) (x : H) :
    polarIsometry T (absOp T x) = T x :=
  T.polarPartial_apply_modulus x

/-- The range of the polar partial isometry lies in the final polar space. -/
theorem polarPartial_mem_finalRange (T : H →L[ℂ] H) (x : T.polarInitial) :
    polarPartial T x ∈ polarFinalRange T := by
  have hx : T.polarPartialAux x = T.polarPartial (x : H) := by
    rw [ContinuousLinearMap.polarPartial_apply]
    congr 1
    exact (Subtype.ext (by
      simp [])).symm
  rw [polarFinalRange, T.polarFinal_eq_range_polarPartial, hx]
  exact ⟨(x : H), rfl⟩

/-- The polar partial isometry, restricted to its final space, is onto. -/
theorem polarPartial_final_surjective (T : H →L[ℂ] H) :
    Function.Surjective
      ((polarPartial T).codRestrict (polarFinalRange T)
        (polarPartial_mem_finalRange T)) := by
  rintro ⟨y, hy⟩
  rw [polarFinalRange, T.polarFinal_eq_range_polarPartial] at hy
  obtain ⟨z, rfl⟩ := hy
  have hz : T.polarPartial z = T.polarPartialAux (T.polarInitial.orthogonalProjectionOnto z) :=
    rfl
  exact ⟨T.polarInitial.orthogonalProjectionOnto z, Subtype.ext (by simpa using hz.symm)⟩

/-- The polar partial isometry as a unitary between its initial and final spaces. -/
def polarPartialFinalEquiv (T : H →L[ℂ] H) :
    T.polarInitial ≃ₗᵢ[ℂ] polarFinalRange T :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := ((polarPartial T).codRestrict (polarFinalRange T)
        (polarPartial_mem_finalRange T)).toLinearMap
      norm_map' := fun x => by
        change ‖polarPartial T x‖ = ‖x‖
        exact T.norm_polarPartialAux_apply x }
    (polarPartial_final_surjective T)

/-- **The final projection identity** `U U⋆ = P_(closure range T)`. -/
theorem polarIsometry_comp_adjoint_self (T : H →L[ℂ] H) :
    polarIsometry T ∘L (polarIsometry T).adjoint = (polarFinalRange T).starProjection :=
  T.polarPartial_comp_adjoint

/-- **The initial projection identity** `U⋆ U = P_(closure range |T|)`. -/
theorem polarIsometry_adjoint_comp_self (T : H →L[ℂ] H) :
    (polarIsometry T).adjoint ∘L polarIsometry T = (polarRange T).starProjection :=
  T.adjoint_comp_polarPartial

/-- `U⋆ T = |T|`, the initial-space identity. -/
theorem polarIsometry_adjoint_comp (T : H →L[ℂ] H) :
    (polarIsometry T).adjoint ∘L T = absOp T :=
  T.adjoint_polarPartial_comp_self

/-- The polar decomposition `U |T| = T`. -/
theorem polar_decomposition (T : H →L[ℂ] H) :
    polarIsometry T ∘L absOp T = T :=
  T.polarPartial_comp_modulus

/-- **The adjoint of the polar isometry is the polar isometry of the adjoint.** -/
theorem adjoint_polarIsometry (T : H →L[ℂ] H) :
    (polarIsometry T).adjoint = polarIsometry T.adjoint :=
  (T.polarPartial_adjoint).symm

end

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
