/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
import ForTauCeti.Analysis.OperatorIdeal.Family.TraceClass

/-!
# Ky Fan dominance

A symmetric operator ideal family is **Ky Fan dominant** when majorization of every finite
Ky Fan gauge forces its own gauge to be dominated:

```
(∀ k, A.kyFanGauge k ≤ B.kyFanGauge k) → N.gauge A ≤ N.gauge B.
```

This is the hypothesis under which the infinite-dimensional Davis--Kahan estimates hold for
a general unitarily invariant norm, and by the Ky Fan dominance principle it holds for every
symmetric gauge.  That principle — weak majorization implies domination for all symmetric
gauges — is Milestone B2 of `ForTauCetiRoadmap/OperatorIdeals/README.md` and is *not*
proved here; what is proved is that the three families staged so far satisfy the property
directly, each in one line, without going near majorization theory.

## Property, not data

`DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean` carries dominance as a
*field* of a `KyFanDominantIdealFamily` structure, bundled with completeness.  The roadmap
records that the Tau Ceti form should instead be a class over
`TauCeti.SymmetricOperatorIdealFamily`, so that a family carries dominance as a property of
the family it already is rather than as extra data attached to a copy of it.  That is what
this module provides.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean`
  (the `gauge_le_of_forall_kyFanApproximationGauge_le` field of
  `TauCeti.DavisKahan.Experimental.ExactSinTheta.KyFanDominantIdealFamily`).
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **restructured**.  The condition is unchanged; it becomes a class over
  the canonical family instead of a structure field, as the roadmap specifies, and the
  completeness field is dropped because `TauCeti.OperatorIdealFamily.IsComplete` is already
  its own class.
* Spectra influence: none.
-/

open scoped ENNReal InnerProductSpace

public section

namespace TauCeti

universe v

open ContinuousLinearMap

/-- **Ky Fan dominance.**  Majorization of every finite Ky Fan gauge forces the ideal gauge
to be dominated too. -/
class IsKyFanDominant (N : SymmetricOperatorIdealFamily.{0, v} ℂ) : Prop where
  /-- The dominance implication. -/
  gauge_le_of_forall_kyFanGauge_le :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      {A B : E →L[ℂ] F},
      (∀ k, A.kyFanGauge k ≤ B.kyFanGauge k) → N.gauge A ≤ N.gauge B

namespace IsKyFanDominant

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Dominance in the two-part form the sine-theta development uses: a majorized operator is
a member whenever the majorizing one is, and its gauge is no larger. -/
theorem mem_carrier_and_gauge_le (N : SymmetricOperatorIdealFamily.{0, v} ℂ)
    [IsKyFanDominant N] {A B : E →L[ℂ] F}
    (hB : B ∈ N.toOperatorIdealFamily.carrier)
    (hAB : ∀ k, A.kyFanGauge k ≤ B.kyFanGauge k) :
    A ∈ N.toOperatorIdealFamily.carrier ∧ N.gauge A ≤ N.gauge B := by
  have hle := IsKyFanDominant.gauge_le_of_forall_kyFanGauge_le (N := N) hAB
  exact ⟨ne_top_of_le_ne_top hB hle, hle⟩

/-- Equal Ky Fan gauges force equal ideal gauges. -/
theorem gauge_eq_of_forall_kyFanGauge_eq (N : SymmetricOperatorIdealFamily.{0, v} ℂ)
    [IsKyFanDominant N] {A B : E →L[ℂ] F}
    (h : ∀ k, A.kyFanGauge k = B.kyFanGauge k) :
    N.gauge A = N.gauge B :=
  le_antisymm
    (IsKyFanDominant.gauge_le_of_forall_kyFanGauge_le (N := N) fun k => (h k).le)
    (IsKyFanDominant.gauge_le_of_forall_kyFanGauge_le (N := N) fun k => (h k).ge)

end IsKyFanDominant

/-- The operator norm is the first Ky Fan gauge, so dominance is the `k = 1` instance. -/
instance isKyFanDominant_operatorNormFamily :
    IsKyFanDominant (operatorNormFamily.{0, v} ℂ) where
  gauge_le_of_forall_kyFanGauge_le {_E _F} _ _ _ _ _ _ {_A _B} h := by
    have h1 := h 1
    rw [ContinuousLinearMap.kyFanGauge_one, ContinuousLinearMap.kyFanGauge_one] at h1
    simpa [operatorNormFamily] using ENNReal.ofReal_le_ofReal h1

/-- A Ky Fan family is dominated by hypothesis at its own index. -/
instance isKyFanDominant_kyFanIdealFamily (k : ℕ) (hk : 0 < k) :
    IsKyFanDominant (kyFanIdealFamily.{v} k hk) where
  gauge_le_of_forall_kyFanGauge_le {_E _F} _ _ _ _ _ _ {_A _B} h :=
    ENNReal.ofReal_le_ofReal (h k)

/-- The nuclear norm is the supremum of the Ky Fan gauges, so dominance is monotonicity of
that supremum. -/
instance isKyFanDominant_traceClassIdealFamily :
    IsKyFanDominant (traceClassIdealFamily.{v} ℂ) where
  gauge_le_of_forall_kyFanGauge_le {_E _F} _ _ _ _ _ _ {_A _B} h := by
    rw [gauge_traceClassIdealFamily, gauge_traceClassIdealFamily,
      ContinuousLinearMap.nuclearENorm_eq_iSup_kyFanGauge,
      ContinuousLinearMap.nuclearENorm_eq_iSup_kyFanGauge]
    exact iSup_mono fun k => ENNReal.ofReal_le_ofReal (h k)

end TauCeti
