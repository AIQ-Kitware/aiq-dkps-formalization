/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.RealSpectrumBorelSymbols
public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.CyclicModel
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The diagonal spectral measure of a self-adjoint operator, on its real spectrum

Tau Ceti's `StarAlgHom.representationDiagMeasure`, applied to `cfcHom ha`, supplies the
scalar spectral measure of a vector on `spectrum ℂ a`.
`ForTauCeti/Analysis/InnerProductSpace/RealSpectrumBorelSymbols.lean` has
already moved the *symbol* side of the cyclic multiplication model to `spectrum ℝ a`.  This
module moves the *measure* side.

The two sides are independent.  A symbol is a function, so it transports by reindexing; a
measure is not, and it transports by pushforward.  Both transports run along one map,
`TauCeti.realSpectrumHomeomorph ha : spectrum ℂ a ≃ₜ spectrum ℝ a`, which is a Borel
isomorphism because both spectra carry the subspace Borel σ-algebra.

## What is delivered

`realSpectrumDiagMeasure ha ξ` is the pushforward of `(cfcHom
ha.isStarNormal).representationDiagMeasure ξ` along the
homeomorphism, and `measurePreserving_realSpectrumHomeomorph` says the homeomorphism is
measure-preserving between the two.  Because the map is a Borel *isomorphism*, the same
statement holds in the other direction
(`measurePreserving_realSpectrumHomeomorph_symm`), and that is what upgrades the `Lp`
transport from a linear isometry to a linear isometric *equivalence*:

```text
realSpectrumDiagMeasureLpEquiv ha ξ :
  Lp ℂ 2 (realSpectrumDiagMeasure ha ξ) ≃ₗᵢ[ℂ] Lp ℂ 2 ((cfcHom
  ha.isStarNormal).representationDiagMeasure ξ)
```

The equivalence uses Tau Ceti's `Lp.compMeasurePreservingₗᵢEquiv` on the homeomorphism
and its inverse. The real cyclic model composes this equivalence with the complex cyclic
isometry.

## Main results

* `TauCeti.BorelCalculus.realSpectrumDiagMeasure`: the real-spectrum diagonal measure, as a
  pushforward, with `realSpectrumDiagMeasure_eq_map` as its characteristic lemma and
  `instIsFiniteMeasure_realSpectrumDiagMeasure` recording finiteness.
* `TauCeti.BorelCalculus.measurePreserving_realSpectrumHomeomorph` and
  `TauCeti.BorelCalculus.measurePreserving_realSpectrumHomeomorph_symm`: the measure-preserving
  statement, in both directions.
* `TauCeti.BorelCalculus.realSpectrumDiagMeasure_apply` and
  `TauCeti.BorelCalculus.integral_realSpectrumDiagMeasure`: the change-of-variables identities
  on sets and on integrals.
* `TauCeti.BorelCalculus.realSpectrumDiagMeasureLpEquiv`: **the deliverable** — the `ℂ`-linear
  isometric equivalence of the two `L²` spaces, with `realSpectrumDiagMeasureLpEquiv_apply`,
  `coeFn_realSpectrumDiagMeasureLpEquiv` and `coeFn_realSpectrumDiagMeasureLpEquiv_symm`
  naming its two underlying maps and their almost-everywhere values.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.); written here, new for
  this library.
* The original equivalence assembled the two Mathlib pullbacks and proved their inverse laws.
  The native measure-preserving equivalence now supplies that construction.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
-/

public section

open MeasureTheory

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section Measure

/-- **The diagonal spectral measure of a self-adjoint operator, on its real spectrum.**

This is `(cfcHom ha.isStarNormal).representationDiagMeasure ξ` pushed forward along
`realSpectrumHomeomorph ha : spectrum ℂ a ≃ₜ spectrum ℝ a`. This is the measure
used to integrate the squared norm of a bounded Borel symbol on the real spectrum. -/
noncomputable def realSpectrumDiagMeasure (ha : IsSelfAdjoint a) (ξ : H) :
    Measure (spectrum ℝ a) :=
  ((cfcHom ha.isStarNormal).representationDiagMeasure ξ).map (realSpectrumHomeomorph ha)

private theorem realSpectrumDiagMeasure_eq_map_aux (ha : IsSelfAdjoint a) (ξ : H) :
    realSpectrumDiagMeasure ha ξ
      = ((cfcHom ha.isStarNormal).representationDiagMeasure ξ).map (realSpectrumHomeomorph ha) :=
        rfl

/-- The real-spectrum diagonal measure is the pushforward of the diagonal measure: the
characteristic lemma, so no consumer needs the body. -/
theorem realSpectrumDiagMeasure_eq_map (ha : IsSelfAdjoint a) (ξ : H) :
    realSpectrumDiagMeasure ha ξ
      = ((cfcHom ha.isStarNormal).representationDiagMeasure ξ).map (realSpectrumHomeomorph ha) :=
  realSpectrumDiagMeasure_eq_map_aux ha ξ

/-- The real-spectrum diagonal measure is finite, being the pushforward of a finite measure. -/
instance instIsFiniteMeasure_realSpectrumDiagMeasure (ha : IsSelfAdjoint a) (ξ : H) :
    IsFiniteMeasure (realSpectrumDiagMeasure ha ξ) := by
  rw [realSpectrumDiagMeasure_eq_map]
  exact Measure.isFiniteMeasure_map _ _

end Measure

section MeasurePreserving

/-- **The measure-preserving statement.**

`realSpectrumHomeomorph ha` carries the diagonal measure of `ξ` on `spectrum ℂ a` to its
real-spectrum counterpart on `spectrum ℝ a`.  Measurability is continuity of the
homeomorphism, and the pushforward identity is the definition of the target measure. -/
theorem measurePreserving_realSpectrumHomeomorph (ha : IsSelfAdjoint a) (ξ : H) :
    MeasurePreserving (realSpectrumHomeomorph ha) ((cfcHom
      ha.isStarNormal).representationDiagMeasure ξ)
      (realSpectrumDiagMeasure ha ξ) :=
  ⟨measurable_realSpectrumHomeomorph ha, (realSpectrumDiagMeasure_eq_map ha ξ).symm⟩

/-- **The measure-preserving statement, backward direction.**

The inverse homeomorphism carries the real-spectrum diagonal measure back.  This direction is
available only because the transport is along a Borel *isomorphism*, and it is what turns the
`L²` transport into an equivalence rather than a bare isometry. -/
theorem measurePreserving_realSpectrumHomeomorph_symm (ha : IsSelfAdjoint a) (ξ : H) :
    MeasurePreserving (realSpectrumHomeomorph ha).symm (realSpectrumDiagMeasure ha ξ)
      ((cfcHom ha.isStarNormal).representationDiagMeasure ξ) :=
  MeasurePreserving.symm (realSpectrumHomeomorph ha).toMeasurableEquiv
    (measurePreserving_realSpectrumHomeomorph ha ξ)

/-- **Change of variables on sets.**  The real-spectrum diagonal measure of a set is the
diagonal measure of its preimage under the homeomorphism. -/
theorem realSpectrumDiagMeasure_apply (ha : IsSelfAdjoint a) (ξ : H) (s : Set (spectrum ℝ a)) :
    realSpectrumDiagMeasure ha ξ s
      = (cfcHom ha.isStarNormal).representationDiagMeasure ξ (realSpectrumHomeomorph ha ⁻¹' s) :=
  ((measurePreserving_realSpectrumHomeomorph ha ξ).measure_preimage_equiv
    (f := (realSpectrumHomeomorph ha).toMeasurableEquiv) s).symm

/-- **Change of variables on integrals.**  Integrating against the real-spectrum diagonal
measure is integrating the reindexed integrand against the diagonal measure.  This is the form
in which the transport meets the defining property `StarAlgHom.integral_representationDiagMeasure`
of the diagonal
measure. -/
theorem integral_realSpectrumDiagMeasure (ha : IsSelfAdjoint a) (ξ : H)
    (g : spectrum ℝ a → ℂ) :
    ∫ x, g x ∂(realSpectrumDiagMeasure ha ξ)
      = ∫ z, g (realSpectrumHomeomorph ha z) ∂((cfcHom ha.isStarNormal).representationDiagMeasure
        ξ) :=
  ((measurePreserving_realSpectrumHomeomorph ha ξ).integral_comp'
    (f := (realSpectrumHomeomorph ha).toMeasurableEquiv) g).symm

end MeasurePreserving

section LpTransport

/-- Pullback along the real-spectrum homeomorphism identifies the two spectral `L²` spaces. -/
noncomputable def realSpectrumDiagMeasureLpEquiv (ha : IsSelfAdjoint a) (ξ : H) :
    Lp ℂ 2 (realSpectrumDiagMeasure ha ξ) ≃ₗᵢ[ℂ] Lp ℂ 2 ((cfcHom
      ha.isStarNormal).representationDiagMeasure ξ) :=
  Lp.compMeasurePreservingₗᵢEquiv ℂ (measurePreserving_realSpectrumHomeomorph ha ξ)
    (measurePreserving_realSpectrumHomeomorph_symm ha ξ)
    (Filter.Eventually.of_forall fun x => (realSpectrumHomeomorph ha).apply_symm_apply x)

/-- The equivalence is Mathlib's composition-with-a-measure-preserving-map, in the direction
that reindexes a real-spectrum class into a complex-spectrum one. -/
theorem realSpectrumDiagMeasureLpEquiv_apply (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    realSpectrumDiagMeasureLpEquiv ha ξ F
      = Lp.compMeasurePreserving (realSpectrumHomeomorph ha)
          (measurePreserving_realSpectrumHomeomorph ha ξ) F :=
  Lp.compMeasurePreservingₗᵢEquiv_apply ℂ _ _ _ F

/-- The inverse equivalence is composition with the inverse homeomorphism. -/
theorem realSpectrumDiagMeasureLpEquiv_symm_apply (ha : IsSelfAdjoint a) (ξ : H)
    (G : Lp ℂ 2 ((cfcHom ha.isStarNormal).representationDiagMeasure ξ)) :
    (realSpectrumDiagMeasureLpEquiv ha ξ).symm G
      = Lp.compMeasurePreserving (realSpectrumHomeomorph ha).symm
          (measurePreserving_realSpectrumHomeomorph_symm ha ξ) G :=
  Lp.compMeasurePreservingₗᵢEquiv_symm_apply ℂ _ _ _ G

/-- **The pointwise description of the transport.**  As a function on `spectrum ℂ a`, the
image class is the original one read at the real part of the spectral point, almost everywhere
for the diagonal measure. -/
theorem coeFn_realSpectrumDiagMeasureLpEquiv (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    (realSpectrumDiagMeasureLpEquiv ha ξ F : spectrum ℂ a → ℂ)
      =ᵐ[(cfcHom ha.isStarNormal).representationDiagMeasure ξ]
        (F : spectrum ℝ a → ℂ) ∘ realSpectrumHomeomorph ha := by
  rw [realSpectrumDiagMeasureLpEquiv_apply]
  exact Lp.coeFn_compMeasurePreserving F (measurePreserving_realSpectrumHomeomorph ha ξ)

/-- The pointwise description of the inverse transport, almost everywhere for the
real-spectrum diagonal measure. -/
theorem coeFn_realSpectrumDiagMeasureLpEquiv_symm (ha : IsSelfAdjoint a) (ξ : H)
    (G : Lp ℂ 2 ((cfcHom ha.isStarNormal).representationDiagMeasure ξ)) :
    ((realSpectrumDiagMeasureLpEquiv ha ξ).symm G : spectrum ℝ a → ℂ)
      =ᵐ[realSpectrumDiagMeasure ha ξ]
        (G : spectrum ℂ a → ℂ) ∘ (realSpectrumHomeomorph ha).symm := by
  rw [realSpectrumDiagMeasureLpEquiv_symm_apply]
  exact Lp.coeFn_compMeasurePreserving G (measurePreserving_realSpectrumHomeomorph_symm ha ξ)

end LpTransport

end BorelCalculus
end TauCeti
