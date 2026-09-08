/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.OperatorIdeal.NormalizedUnitaryInvariantNorm
import ForTauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge

/-!
# Exploration: Fan dominance at the Davis--Kahan source norm boundary

This file is deliberately standalone.  Nothing imports it, and it does not
change `SourceUnitaryInvariantNorm`, `NormalizedUnitaryInvariantNorm`, or any
production theorem signature.

The question being tested is narrower than "formalize Calkin's theorem":

1. Davis--Kahan work on separable Hilbert spaces.
2. Their source norm class is represented by `SourceUnitaryInvariantNorm`.
3. The source-facing theorem should not require an extra `HasFanDominance`
   argument if Fan dominance is a theorem of that source class.
4. Existing `ForTauCeti` infrastructure already proves that a gauge obtained
   from a symmetric sequence gauge is Fan dominant.

The compile probes below isolate the missing implication.  They show that a
*separable symmetric-gauge representation theorem* for a source norm is enough
to derive the exact Fan-dominance property needed at the source boundary.
Consequently, if this file compiles, the remaining mathematical task is the
representation theorem itself (or some shorter theorem implying it), rather
than any Davis--Kahan-specific estimate.

No `sorry`, `axiom`, or replacement source structure is introduced here.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta
namespace FanDominanceExploration

open scoped ENNReal InnerProductSpace

noncomputable section

universe v

/-- Fan dominance restricted to the separable Hilbert-space scope used by the
Davis--Kahan paper.

This is intentionally a local exploration predicate rather than a field added
to `SourceUnitaryInvariantNorm`. -/
def HasFanDominanceSeparable (N : SourceUnitaryInvariantNorm.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [TopologicalSpace.SeparableSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    [TopologicalSpace.SeparableSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

/-- A separable Calkin-style representation statement, stated only as strongly
as this exploration needs it.

The same symmetric sequence gauge must represent the source norm on every
separable source/target pair.  This is the missing mathematical bridge we want
to investigate; it is a proposition here, not an assumption added to the source
norm structure. -/
def HasSymmetricGaugeRepresentationSeparable
    (N : SourceUnitaryInvariantNorm.{0, v} ℂ) : Prop :=
  ∃ Φ : TauCeti.SymmetricGauge,
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [TopologicalSpace.SeparableSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      [TopologicalSpace.SeparableSpace F]
      (A : E →L[ℂ] F),
      N.toSymmetricOperatorIdealFamily.gauge A =
        Φ.extend (TauCeti.approxSeq A)

/-- The existing unrestricted Fan-dominance property certainly implies the
separable version.  This checks that `HasFanDominanceSeparable` is only a
restriction of the current target, not a different mathematical condition. -/
theorem hasFanDominanceSeparable_of_hasFanDominance
    (N : SourceUnitaryInvariantNorm.{0, v} ℂ) (h : N.HasFanDominance) :
    HasFanDominanceSeparable N := by
  intro E F E' F'
  intro _ _ _ _
  intro _ _ _ _
  intro _ _ _ _
  intro _ _ _ _
  intro A B hAB
  exact h hAB

/-- **Main reduction probe.**

If a source norm has one symmetric sequence gauge representing it on every
separable Hilbert-space pair, then it has Fan dominance on exactly that
separable scope.

The proof uses only infrastructure already present in `ForTauCeti`:

* `approxSeq_antitone` for approximation-number sequences;
* the definition of the Ky Fan gauge as a finite prefix sum; and
* `SymmetricGauge.extend_le_extend_of_forall_sum_le`, the proved weak-majorization
  monotonicity of the extended symmetric gauge.

Thus a successful compile isolates the remaining gap to the representation
step. -/
theorem hasFanDominanceSeparable_of_symmetricGaugeRepresentation
    (N : SourceUnitaryInvariantNorm.{0, v} ℂ)
    (hrep : HasSymmetricGaugeRepresentationSeparable N) :
    HasFanDominanceSeparable N := by
  rcases hrep with ⟨Φ, hΦ⟩
  intro E F E' F'
  intro _ _ _ _
  intro _ _ _ _
  intro _ _ _ _
  intro _ _ _ _
  intro A B hAB
  rw [hΦ A, hΦ B]
  apply Φ.extend_le_extend_of_forall_sum_le
    (TauCeti.approxSeq_antitone A) (TauCeti.approxSeq_antitone B)
  intro k
  have hk := hAB k
  simp only [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge] at hk
  rw [show (∑ n ∈ Finset.range k, TauCeti.approxSeq A n) =
        ENNReal.ofReal (∑ n ∈ Finset.range k, A.approximationNumber n) by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun i _ => A.approximationNumber_nonneg i)]
      rfl,
    show (∑ n ∈ Finset.range k, TauCeti.approxSeq B n) =
        ENNReal.ofReal (∑ n ∈ Finset.range k, B.approximationNumber n) by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun i _ => B.approximationNumber_nonneg i)]
      rfl]
  exact ENNReal.ofReal_le_ofReal hk

/-!
## What remains after the reduction

The intended next experiment is *not* to modify either source norm structure.
It is to attempt, in this same standalone file, a theorem of the shape

```lean
-- schematic only; deliberately not asserted here
-- theorem sourceNorm_hasSymmetricGaugeRepresentationSeparable
--     (N : SourceUnitaryInvariantNorm.{0, v} ℂ) :
--     HasSymmetricGaugeRepresentationSeparable N := ...
```

The current generic symmetric-gauge library explicitly proves the forward
Calkin construction (`SymmetricGauge -> operator ideal family`) and records that
the converse is the substantial missing direction.  Keeping that target here
makes compiler feedback useful without letting an exploratory hypothesis leak
into the production theorem surface.
-/

end

end FanDominanceExploration
end ExactSinTheta
end DavisKahan
end TauCeti
