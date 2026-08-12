/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Geometry.Halmos.TwoProjections
import DavisKahan.SpectralTheory.SpectralRestriction
-- supplies `compressOperator`
import DavisKahan.Sylvester.Spectrum
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
-- grounded Section-3 predicates promoted out of the experimental frontier;
-- re-exported here so Core's remaining declarations keep seeing their names
import DavisKahan.Geometry.Halmos.GenericRotationPredicates
-- grounded relational/projection declarations promoted out of this stub;
-- re-exported here so Core's importers keep seeing their names
import DavisKahan.Geometry.Halmos.UnitaryEquivalence
import DavisKahan.SpectralTheory.CircleRieszProjection
import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.MultiplicityModel

/-!
# Experimental frontier interfaces for the remaining Davis--Kahan 1970 proof

This module isolates reusable signatures needed by several uncompleted source
results.  The declarations form the stable frontier API and
are not imported by the supported library target.

The purpose is to make the remaining dependency graph explicit.  Each
interface is intended to be replaced by a concrete construction or theorem,
not treated as a permanent hypothesis in the source-facing API.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Frontier


universe u v

section SpectralMultiplicityData

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- **Equality of spectral multiplicity data over an arbitrary `RCLike` scalar field.**

Two operators have the same spectral multiplicity when each is unitarily equivalent to the
multiplication model of a `TauCeti.MultiplicityDatum 𝕜` -- a finite measure on `ℂ` together with
an **antitone** sequence of measurable level sets -- and the two data agree: the base measures
are in the same **measure class**, and the level sets agree up to null sets.  The spectral
parameter and base measure remain complex; only the `L²` fibres and model operator use `𝕜`.

This discharges both requirements the earlier `sorry`ed definition's docstring made.  The
measure class is `TauCeti.MeasureEquiv`, a named relation proved to be an `Equivalence` at the
point of definition so that the quotient can be formed later.  The **cardinal-valued
multiplicity function** is encoded by its super-level sets: `level k` is `{z | k < m z}`, so a
point of `level k \ level (k+1)` has multiplicity exactly `k + 1` and a point of every `level k`
has multiplicity `ℵ₀`.  Level sets are used rather than a function `ℂ → ℕ∞` because then every
hypothesis is a plain `MeasurableSet`, and the antitonicity that makes them super-level sets of
*some* function is a field of the datum, established by
`TauCeti.antitone_levelSet` when a model is built.

The encoding is not a proxy: `TauCeti.MultiplicityDatum.multiplicity` is the honest
`ℂ → ℕ∞` multiplicity function, `TauCeti.MultiplicityDatum.mem_level_iff` proves
`level k = {z | k < multiplicity z}`, and
`TauCeti.MultiplicityDatum.measurable_multiplicity` proves it measurable.  Level sets are
carried in the structure only because that makes every hypothesis a plain `MeasurableSet`.

**What this is and is not.**  It is an existential over *presentations*, and it is what makes
`sameSpectralMultiplicity_iff_unitarilyEquivalent` provable and paper-faithful.  It is **not** a
canonical invariant: nothing here says the datum of an operator is unique, and uniqueness of the
multiplicity decomposition remains an open obligation of this development.  In particular this
does **not** inhabit
`TauCeti.DavisKahan.SpectralMultiplicityFoundation`,
whose `multiplicity` field is a *function* and therefore needs uniqueness as well as existence.
See `dev/section3-multiplicity-plan-2026-08-06.md` §5. -/
def SameSpectralMultiplicity
    (A : H₁ →L[𝕜] H₁) (B : H₂ →L[𝕜] H₂) : Prop :=
  ∃ D E : TauCeti.MultiplicityDatum 𝕜,
    TauCeti.OperatorUnitaryEquiv A D.operator ∧
    TauCeti.OperatorUnitaryEquiv B E.operator ∧
    TauCeti.MeasureEquiv D.base E.base ∧
    ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0

end SpectralMultiplicityData

section CrossSpaceClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- **Same multiplicity data implies unitary equivalence**, with no separability hypothesis on
either space.

Chain the two models: `A ≃ D.operator ≃ E.operator ≃ B`.  This theorem remains at the
complex specialization: the available middle step `TauCeti.operatorUnitaryEquiv_of_measureEquiv`
uses the complex `rnDerivL2Equiv` API.  Generalizing that Radon--Nikodym unitary to arbitrary
`RCLike` scalars is separate mathematics from field-indexing the multiplicity datum. -/
theorem unitarilyEquivalent_of_sameSpectralMultiplicity
    (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) (h : SameSpectralMultiplicity A B) :
    BoundedOperatorsUnitaryEquivalent A B := by
  obtain ⟨D, E, hAD, hBE, hbase, hlevel⟩ := h
  exact hAD.trans
    ((TauCeti.operatorUnitaryEquiv_of_measureEquiv hbase hlevel).trans hBE.symm)

omit [CompleteSpace H₂] in
/-- **Unitary equivalence implies the same multiplicity data.**

This is the direction that needs the existence half of Hahn--Hellinger, and therefore the
separability of `H₁`: a model for `A` is built from a *countable* cyclic decomposition, and
countability of the index is what lets the level-set normalisation run, since ranks count
earlier indices.  `H₂` needs nothing -- `B` inherits `A`'s model along the given unitary, so the
same datum serves for both.  This theorem therefore remains at the complex specialization:
`TauCeti.BorelCalculus.exists_hasMultiplicityModel` is the complex Hahn--Hellinger existence
theorem, and the real existence direction is intentionally not asserted here. -/
theorem sameSpectralMultiplicity_of_unitarilyEquivalent
    [TopologicalSpace.SeparableSpace H₁]
    (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) (hA : IsSelfAdjoint A)
    (h : BoundedOperatorsUnitaryEquivalent A B) : SameSpectralMultiplicity A B := by
  obtain ⟨D, hAD⟩ := TauCeti.BorelCalculus.exists_hasMultiplicityModel hA.isStarNormal
  refine ⟨D, D, hAD, ?_, TauCeti.MeasureEquiv.refl _, fun k => ?_⟩
  · exact (TauCeti.OperatorUnitaryEquiv.symm h).trans hAD
  · simp

/-- Spectral multiplicity data classify self-adjoint bounded operators up to
unitary equivalence.  This is the missing spectral-theorem bridge in the
paper's formulation of Theorem 3.1.

**On the separability hypothesis.**  It is carried on `H₁` only, and it is *paper-faithful*:
separability is one of the paper's **standing assumptions**, taken from the Introduction and
Sections 1--2 and therefore governing Section 3.  The public source surrogate records it
verbatim -- "`H` is a separable Hilbert space, real or complex, with finite dimensionality only
a special case" (`prose/distilled_literature/DavisKahan1970_part_III.tex`, *Standing assumptions
from the transcription*).  The same list records that for noncompact operators the source itself
expects singular-value lists to be replaced by *spectral multiplicity language*, which is
precisely the phrasing proved here.  Nothing
already proved is weakened by it either: the operator-level classification
`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant` remains stated and proved
with no separability at all, and it is that theorem, not this one, that grounds the frontier
node for Theorem 3.1.  The `←` direction here is also separability-free; see
`unitarilyEquivalent_of_sameSpectralMultiplicity`.

The reason separability enters at all is that the existence of a multiplicity model needs a
*countable* cyclic decomposition, and the level-set normal form needs a linearly ordered index
because ranks count earlier indices.  A non-separable statement would need the
uniform-multiplicity form indexed by cardinals, whose measures are not σ-finite, and hence a
Radon--Nikodym theory this development does not have. -/
theorem sameSpectralMultiplicity_iff_unitarilyEquivalent
    [TopologicalSpace.SeparableSpace H₁]
    (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (hA : IsSelfAdjoint A) (_hB : IsSelfAdjoint B) :
    SameSpectralMultiplicity A B ↔
      BoundedOperatorsUnitaryEquivalent A B :=
  ⟨unitarilyEquivalent_of_sameSpectralMultiplicity A B,
    sameSpectralMultiplicity_of_unitarilyEquivalent A B hA⟩

end CrossSpaceClassification

end Frontier
end DavisKahan
end TauCeti