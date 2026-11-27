/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure
public import ForTauCeti.Analysis.InnerProductSpace.SeparatedIntertwiner
public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.BorelNatural

/-!
# Spectral projections are natural under a unitary intertwiner

A unitary `e` commuting with a self-adjoint partial map `A` commutes with every
spectral projection `E_A(B)`.

This is the missing "Borel step" that `SeparatedIntertwiner` records as open in
general: it carries an intertwining relation past the *continuous* functional
calculus into the *bounded Borel* one.  In the generality of an arbitrary
bounded intertwiner that is a monotone-class argument on the sesquilinear form.
For a **unitary** intertwiner it is already available, because
`BorelCalculus.borelCalculus_comp_val_of_intertwines` transports the diagonal
measures themselves.  That is exactly the case a reducing-subspace argument
needs, since a subspace reduces `A` if and only if its *reflection* -- a
unitary -- commutes with `A`.

Both spectral projections use `Complex.inverseCayleyCoord` to pull back real
Borel sets. The comparison below relates the spectrum-subtype and complex
plane versions of the indicator.

## Sources

*Follows nothing in particular*: the commutation that a reducing-subspace
uniqueness argument needs between a spectral projection and a projection onto a
reducing subspace.

## Provenance

*New.*  Composes `SeparatedIntertwiner.cayley_intertwines` with
`BorelCalculus.specProjC_apply_of_intertwines`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The real spectral projection equals the complex spectral projection of its
inverse-Cayley preimage. -/
theorem specProjection_eq_specProjC (B : Set ℝ) (hB : MeasurableSet B) :
    specProjection hA B hB =
      BorelCalculus.specProjC (hA.isStarNormal_cayley)
        (Complex.measurable_inverseCayleyCoord hB) := by
  rw [specProjection_eq_borelCalculus, BorelCalculus.specProjC_def]
  exact BorelCalculus.borelCalculus_congr_ae _ _ _ fun _ =>
    Filter.Eventually.of_forall fun _ => rfl

/-- **Spectral projections are natural under a unitary intertwiner.**

If the unitary `e` preserves `dom A` and commutes with `A` there, then it commutes
with every spectral projection of `A`. -/
theorem specProjection_apply_of_unitary_intertwines (e : H ≃ₗᵢ[ℂ] H)
    (hmaps : ∀ x : A.domain, e (x : H) ∈ A.domain)
    (hint : ∀ x : A.domain, A ⟨e (x : H), hmaps x⟩ = e (A x))
    (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    e (specProjection hA B hB x) = specProjection hA B hB (e x) := by
  have hcay : e.toLinearIsometry.toContinuousLinearMap ∘L A.cayley
      = A.cayley ∘L e.toLinearIsometry.toContinuousLinearMap :=
    cayley_intertwines hA hA hmaps hint
  have he : ∀ z : H, e (A.cayley z) = A.cayley (e z) := by
    intro z
    have h := congrArg (fun T : H →L[ℂ] H => T z) hcay
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry] using h
  rw [specProjection_eq_specProjC hA B hB]
  exact BorelCalculus.specProjC_apply_of_intertwines (hA.isStarNormal_cayley) e he
    (Complex.measurable_inverseCayleyCoord hB) x

end LinearPMap
end TauCeti
