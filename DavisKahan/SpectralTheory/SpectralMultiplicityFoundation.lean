/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Geometry.Polar.TwoProjectionOperatorClassification
import DavisKahan.OperatorIdeal.ApproximationNumbers.SchattenApproximationFoundation

/-!
# Explicit spectral-multiplicity foundation for Section 3

The operator-level Halmos classification does not require direct integrals.
The remaining step in the printed Theorem 3.1 is the general theorem that a
bounded self-adjoint operator is classified up to unitary equivalence by its
spectral multiplicity function.  That theorem is not currently present in the
repository or in the pinned dependencies.

This file gives the missing theorem an explicit, reusable interface.  It also
separates the easier compact specialization, where the invariant can be an
ordered eigenvalue list with multiplicity.  No pair-of-projections theorem
needs to invent direct-integral machinery once these interfaces are available.
-/

open scoped InnerProductSpace

open TauCeti.DavisKahan.ExactSinTheta

namespace TauCeti
namespace DavisKahan

noncomputable section

universe v w

/-- Unitary equivalence of bounded operators acting on possibly different
Hilbert spaces. -/
def BoundedOperatorsUnitaryEquivalent
    {H K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] K,
    (U : H →L[ℂ] K) ∘L A = B ∘L (U : H →L[ℂ] K)

-- The two Hilbert-space universes genuinely only occur together, inside the
-- `max` of the unitary-equivalence relation; neither appears alone.  Same
-- situation, and the same resolution, as `TauCeti.OperatorIdealFamily` in
-- `ForTauCeti/Analysis/OperatorIdeal/Family/Basic.lean`.
set_option linter.checkUnivs false in
/-- Full direct-integral multiplicity theorem, isolated as a foundation.
`Datum` is intentionally abstract: a later implementation may use measurable
cardinal-valued multiplicity functions, cyclic decompositions, or a canonical
measure-class presentation. -/
structure SpectralMultiplicityFoundation where
  Datum : Type w
  multiplicity :
    ∀ {H : Type v}
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      (H →L[ℂ] H) → Datum
  invariant :
    ∀ {H K : Type v}
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      {A : H →L[ℂ] H} {B : K →L[ℂ] K},
      BoundedOperatorsUnitaryEquivalent A B → multiplicity A = multiplicity B
  complete :
    ∀ {H K : Type v}
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      {A : H →L[ℂ] H} {B : K →L[ℂ] K},
      IsSelfAdjointOperator A → IsSelfAdjointOperator B →
      multiplicity A = multiplicity B →
      BoundedOperatorsUnitaryEquivalent A B

namespace SpectralMultiplicityFoundation

/-- Equality of multiplicity data is equivalent to unitary equivalence for
bounded self-adjoint operators. -/
theorem multiplicity_eq_iff
    (M : SpectralMultiplicityFoundation.{v, w})
    {H K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A : H →L[ℂ] H} {B : K →L[ℂ] K}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B) :
    M.multiplicity A = M.multiplicity B ↔
      BoundedOperatorsUnitaryEquivalent A B := by
  constructor
  · exact M.complete hA hB
  · exact M.invariant

end SpectralMultiplicityFoundation

/-- Compact positive-operator classification by the approximation-number list.
For a compact positive operator these numbers are its eigenvalues in decreasing
order, multiplicity counted.

**The trivial-kernel hypotheses are not decoration.**  Without them the
specification is *unsatisfiable*, not merely unproved: `A = 0` on `ℂ` and
`B = 0` on `ℂ²` are both compact, positive and self-adjoint with identical
approximation-number sequences (all zero), yet no linear isometric equivalence
`ℂ ≃ₗᵢ ℂ²` exists.  A structure with an unsatisfiable field has no inhabitants,
so every theorem taking it as a hypothesis is vacuous — the same trap class as
a `sorry`-ed definition.  They were absent until 2026-08-06.

The hypotheses are exactly what genericity supplies in Corollary 3.1: on the
generic part of a subspace pair no vector sits at angle `π / 2`, so the angle
operator has trivial kernel (`eigenspace_genericCosineBlock_zero`). -/
structure CompactPositiveListFoundation where
  positive_compact_list_complete :
    ∀ {H K : Type v}
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      {A : H →L[ℂ] H} {B : K →L[ℂ] K},
      IsSelfAdjointOperator A → IsSelfAdjointOperator B →
      (∀ x, 0 ≤ RCLike.re ⟪x, A x⟫_ℂ) →
      (∀ x, 0 ≤ RCLike.re ⟪x, B x⟫_ℂ) →
      IsCompactOperator A → IsCompactOperator B →
      Module.End.eigenspace A.toLinearMap 0 = ⊥ →
      Module.End.eigenspace B.toLinearMap 0 = ⊥ →
      (∀ n, approximationNumberSequence A n =
        approximationNumberSequence B n) →
      BoundedOperatorsUnitaryEquivalent A B
  positive_compact_list_invariant :
    ∀ {H K : Type v}
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      {A : H →L[ℂ] H} {B : K →L[ℂ] K},
      BoundedOperatorsUnitaryEquivalent A B →
      ∀ n, approximationNumberSequence A n =
        approximationNumberSequence B n

namespace CompactPositiveListFoundation

/-- Exact compact specialization used by Davis--Kahan Corollary 3.1. -/
theorem list_eq_iff_unitarilyEquivalent
    (M : CompactPositiveListFoundation.{v})
    {H K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A : H →L[ℂ] H} {B : K →L[ℂ] K}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪x, A x⟫_ℂ)
    (hBpos : ∀ x, 0 ≤ RCLike.re ⟪x, B x⟫_ℂ)
    (hAc : IsCompactOperator A) (hBc : IsCompactOperator B)
    (hA0 : Module.End.eigenspace A.toLinearMap 0 = ⊥)
    (hB0 : Module.End.eigenspace B.toLinearMap 0 = ⊥) :
    (∀ n, approximationNumberSequence A n =
      approximationNumberSequence B n) ↔
      BoundedOperatorsUnitaryEquivalent A B := by
  constructor
  · exact M.positive_compact_list_complete hA hB hApos hBpos hAc hBc hA0 hB0
  · intro h
    exact M.positive_compact_list_invariant h

end CompactPositiveListFoundation

end
end DavisKahan
end TauCeti