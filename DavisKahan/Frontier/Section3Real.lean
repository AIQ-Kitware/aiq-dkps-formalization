/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Frontier.Section3
import DavisKahan.SpectralTheory.Real.RealMultiplicityModel

/-!
# Theorem 3.1 in the multiplicity phrasing, over a real Hilbert space

`Section3.twoProjection_operator_classification_real` already carries the *classification content*
of Davis--Kahan Theorem 3.1 at real scalars, with no compactness, no finite dimension and no
separability: two ordered pairs of subspaces are unitarily equivalent iff their elementary Halmos
summands match and their angle operators are unitarily equivalent.  What was missing over `ℝ` was
the **translation of that invariant into multiplicity language** -- the paper phrases Theorem 3.1
with *spectral multiplicity functions*, and the passage between "unitarily equivalent" and "same
multiplicity data" is Hahn--Hellinger, which Mathlib has for no scalar field.

This module supplies the translation.  Both directions are proved, and each uses a different half
of the real multiplicity theory:

* `unitarilyEquivalent_of_sameSpectralMultiplicity_real` uses
  `TauCeti.operatorUnitaryEquiv_of_measureEquiv_real`, which needs no Hahn--Hellinger at all --
  only that a real multiplication operator is the restriction of a complex one with the *same,
  real valued*, symbol, so that the complex Radon--Nikodym unitary applies and descends.  There is
  no separability hypothesis, and the base measures need not be carried by the real axis.
* `sameSpectralMultiplicity_of_unitarilyEquivalent_real` uses
  `exists_hasMultiplicityModel_real`, the existence half of real Hahn--Hellinger.  That is where
  separability of `H₁` is spent, exactly as in the complex statement, and where reality of the
  base measure is *produced* rather than assumed -- a self-adjoint operator has real spectrum.

## Scope

The multiplicity datum stays a `TauCeti.MultiplicityDatum` with `base : Measure ℂ`; no
`Measure ℝ` datum is built, and reality of the base is nowhere a field of the structure.  What
changes at `ℝ` is the scalar field of the *model `L²` fibres*, which is what
`TauCeti.MultiplicityDatum.retype` records, and the base measure and level sets -- the entire
multiplicity content -- are literally unchanged.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Frontier

open TauCeti.DavisKahan

section RealTransfer

variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- **Same multiplicity data implies unitary equivalence, over a real Hilbert space**, with no
separability hypothesis on either space and no reality hypothesis on the base measures.

The complex statement's docstring recorded that this direction "remains at the complex
specialization: the available middle step `TauCeti.operatorUnitaryEquiv_of_measureEquiv` uses the
complex `rnDerivL2Equiv` API".  It does -- and it turns out not to matter: the real model operator
is multiplication by a *real valued* symbol, so it is the restriction to the real classes of the
complex operator with the same symbol, and a real symbol commutes with pointwise conjugation.  The
complex Radon--Nikodym unitary is `star`-equivariant (`TauCeti.star_rnDerivL2Equiv`), so it
restricts.  A field-generic Radon--Nikodym unitary is therefore *not* needed here. -/
theorem unitarilyEquivalent_of_sameSpectralMultiplicity_real (A : H₁ →L[ℝ] H₁) (B : H₂ →L[ℝ] H₂)
    (h : SameSpectralMultiplicity A B) : BoundedOperatorsUnitaryEquivalent A B := by
  obtain ⟨D, E, hAD, hBE, hbase, hlevel⟩ := h
  exact hAD.trans
    ((TauCeti.operatorUnitaryEquiv_of_measureEquiv_real hbase hlevel).trans hBE.symm)

omit [CompleteSpace H₂] in
/-- **Unitary equivalence implies the same multiplicity data, over a real Hilbert space.**

This is the direction that needs the existence half of Hahn--Hellinger, now available over `ℝ` as
`RealSpectralRestriction.exists_hasMultiplicityModel_real`, and therefore the separability of
`H₁` -- exactly the hypothesis the complex statement carries, and for exactly the same reason: a
model is built from a *countable* cyclic decomposition, and countability of the index is what lets
the level-set normalisation run.  `H₂` needs nothing; `B` inherits `A`'s model along the given
unitary, so the same datum serves for both. -/
theorem sameSpectralMultiplicity_of_unitarilyEquivalent_real
    [TopologicalSpace.SeparableSpace H₁] (A : H₁ →L[ℝ] H₁) (B : H₂ →L[ℝ] H₂)
    (hA : IsSelfAdjoint A) (h : BoundedOperatorsUnitaryEquivalent A B) :
    SameSpectralMultiplicity A B := by
  obtain ⟨D, hAD⟩ := RealSpectralRestriction.exists_hasMultiplicityModel_real hA
  refine ⟨D, D, hAD, ?_, TauCeti.MeasureEquiv.refl _, fun k => ?_⟩
  · exact (TauCeti.OperatorUnitaryEquiv.symm h).trans hAD
  · simp

omit [CompleteSpace H₂] in
/-- **Spectral multiplicity data classify bounded self-adjoint operators on a separable real
Hilbert space up to unitary equivalence.**  This is the real analogue of
`sameSpectralMultiplicity_iff_unitarilyEquivalent`. -/
theorem sameSpectralMultiplicity_iff_unitarilyEquivalent_real
    [TopologicalSpace.SeparableSpace H₁] (A : H₁ →L[ℝ] H₁) (B : H₂ →L[ℝ] H₂)
    (hA : IsSelfAdjoint A) :
    SameSpectralMultiplicity A B ↔ BoundedOperatorsUnitaryEquivalent A B :=
  ⟨unitarilyEquivalent_of_sameSpectralMultiplicity_real A B,
    sameSpectralMultiplicity_of_unitarilyEquivalent_real A B hA⟩

end RealTransfer

namespace Section3

open MathAhead.HiddenFoundations

section RealClassification

universe u v

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℝ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℝ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

set_option maxSynthPendingDepth 3

/-- **Davis--Kahan 1970, Theorem 3.1, in the paper's own phrasing, over a real Hilbert space.**

The spectral multiplicity data of the two angle operators, together with the elementary
multiplicities, form a complete invariant for ordered pairs of subspaces of a real Hilbert space.

This is the last sentence of Theorem 3.1 that was still complex-only.  The classification
*content* was already real (`twoProjection_operator_classification_real`, with no compactness, no
finite dimension and no separability); what is added here is the translation of its invariant into
multiplicity language, which is Hahn--Hellinger over `ℝ`.  Separability of `H₁` is carried for the
`→` direction alone, exactly as in the complex statement; the `←` direction is
separability-free. -/
theorem theorem3_1_spectralMultiplicity_classification_real
    [TopologicalSpace.SeparableSpace H₁] :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      SameSpectralMultiplicity (genericCosineBlock U₁ V₁) (genericCosineBlock U₂ V₂) := by
  rw [twoProjection_operator_classification]
  constructor
  · rintro ⟨htriv, hgen⟩
    exact ⟨htriv, sameSpectralMultiplicity_of_unitarilyEquivalent_real _ _
      (isSelfAdjoint_genericCosineBlock U₁ V₁) hgen⟩
  · rintro ⟨htriv, hmult⟩
    exact ⟨htriv, unitarilyEquivalent_of_sameSpectralMultiplicity_real _ _ hmult⟩

end RealClassification

end Section3

end Frontier
end Experimental
end DavisKahan
end TauCeti
