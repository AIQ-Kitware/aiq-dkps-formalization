/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.OperatorIdeal.NormalizedUnitaryInvariantNorm
import ForTauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge
import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm.Majorization

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
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
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
  intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hAB
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
## Probe 2: recover finite-dimensional Fan dominance directly from the source laws

The symmetric-gauge representation above is deliberately stronger than we
should expect for the entire source class.  In particular, this repository
already records source-like norms with a Calkin-quotient contribution: those
need not equal the maximal extension of their restriction to finite-rank
operators.

The next probe therefore avoids any infinite symmetric-gauge representation.
It asks only whether the source gauge, restricted to finite-dimensional
operator spaces, is already enough to feed the proved finite-dimensional Fan
dominance theorem.

There is one local hypothesis below: every finite-dimensional operator belongs
to the source ideal.  Rank-one normalization plus the ideal laws should imply
that hypothesis; keeping it separate in this probe lets the compiler test the
majorization route independently of the finite-rank decomposition needed to
prove membership.
-/

/-- Every operator between finite-dimensional complex Hilbert spaces belongs to
this source ideal.

This is an exploration predicate, not a new field.  The next probe will try to
derive it from rank-one normalization. -/
def HasFiniteDimensionalMembership
    (N : SourceUnitaryInvariantNorm.{0, 0} ℂ) : Prop :=
  ∀ {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →L[ℂ] F),
    N.toSymmetricOperatorIdealFamily.Mem A

/-- A linear isometric equivalence is a contraction.  Local copy of the tiny
fact used by the production source-norm façade; kept here so this exploration
does not depend on any Fan-dominant wrapper. -/
private theorem norm_isometryEquiv_le_one_finite
    {X Y : Type}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (g : X ≃ₗᵢ[ℂ] Y) :
    ‖(g.toContinuousLinearEquiv : X →L[ℂ] Y)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp

/-- On finite-dimensional members, the source gauge is invariant under
unitaries on both sides.  This is derived from the ideal law in both directions,
not assumed. -/
theorem gaugeReal_comp_isometryEquiv_finite
    (N : SourceUnitaryInvariantNorm.{0, 0} ℂ)
    (hfinite : HasFiniteDimensionalMembership N)
    {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (e : F ≃ₗᵢ[ℂ] F) (f : E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] F) :
    N.toSymmetricOperatorIdealFamily.gaugeReal
        ((e.toContinuousLinearEquiv : F →L[ℂ] F) ∘L A ∘L
          (f.toContinuousLinearEquiv : E →L[ℂ] E)) =
      N.toSymmetricOperatorIdealFamily.gaugeReal A := by
  let S := N.toSymmetricOperatorIdealFamily
  set B := (e.toContinuousLinearEquiv : F →L[ℂ] F) ∘L A ∘L
    (f.toContinuousLinearEquiv : E →L[ℂ] E) with hB
  change S.gaugeReal B = S.gaugeReal A
  have hA : S.Mem A := by
    simpa [S] using hfinite A
  have hBmem : S.Mem B := by
    simpa [S] using hfinite B
  have hAeq : A =
      (e.symm.toContinuousLinearEquiv : F →L[ℂ] F) ∘L B ∘L
        (f.symm.toContinuousLinearEquiv : E →L[ℂ] E) := by
    ext x
    simp [hB]
  refine le_antisymm ?_ ?_
  · calc
      S.gaugeReal B
          ≤ S.gaugeReal
              (A ∘L (f.toContinuousLinearEquiv : E →L[ℂ] E)) := by
            rw [hB, ← ContinuousLinearMap.comp_assoc]
            exact S.gaugeReal_comp_left_le _
              (S.comp_right_mem _ hA)
              (norm_isometryEquiv_le_one_finite e)
      _ ≤ S.gaugeReal A :=
          S.gaugeReal_comp_right_le _ hA
            (norm_isometryEquiv_le_one_finite f)
  · calc
      S.gaugeReal A =
          S.gaugeReal
            ((e.symm.toContinuousLinearEquiv : F →L[ℂ] F) ∘L B ∘L
              (f.symm.toContinuousLinearEquiv : E →L[ℂ] E)) := by
            rw [← hAeq]
      _ ≤ S.gaugeReal
              (B ∘L (f.symm.toContinuousLinearEquiv : E →L[ℂ] E)) := by
            rw [← ContinuousLinearMap.comp_assoc]
            exact S.gaugeReal_comp_left_le _
              (S.comp_right_mem _ hBmem)
              (norm_isometryEquiv_le_one_finite e.symm)
      _ ≤ S.gaugeReal B :=
          S.gaugeReal_comp_right_le _ hBmem
            (norm_isometryEquiv_le_one_finite f.symm)

/-- Restrict a source ideal gauge to finite-dimensional linear maps.  Under the
local membership hypothesis it is a rectangular unitarily invariant seminorm,
so the existing T-transform/Fan-dominance engine applies without any symmetric
sequence-gauge representation of the infinite-dimensional ideal. -/
noncomputable def finiteRectangularSeminorm
    (N : SourceUnitaryInvariantNorm.{0, 0} ℂ)
    (hfinite : HasFiniteDimensionalMembership N)
    {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] :
    TauCeti.RectangularUnitarilyInvariantSeminorm ℂ E F where
  toFun A :=
    N.toSymmetricOperatorIdealFamily.gaugeReal A.toContinuousLinearMap
  add_le' A B := by
    let S := N.toSymmetricOperatorIdealFamily
    have hA : S.Mem A.toContinuousLinearMap := by
      simpa [S] using hfinite A.toContinuousLinearMap
    have hB : S.Mem B.toContinuousLinearMap := by
      simpa [S] using hfinite B.toContinuousLinearMap
    change S.gaugeReal (A + B).toContinuousLinearMap ≤
      S.gaugeReal A.toContinuousLinearMap + S.gaugeReal B.toContinuousLinearMap
    rw [map_add]
    exact S.gaugeReal_add_le hA hB
  smul' c A := by
    let S := N.toSymmetricOperatorIdealFamily
    have hA : S.Mem A.toContinuousLinearMap := by
      simpa [S] using hfinite A.toContinuousLinearMap
    change S.gaugeReal (c • A).toContinuousLinearMap =
      ‖c‖ * S.gaugeReal A.toContinuousLinearMap
    rw [map_smul]
    exact S.gaugeReal_smul c hA
  invariant' U V A := by
    let S := N.toSymmetricOperatorIdealFamily
    have hcomp :
        (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).toContinuousLinearMap =
          (U.toContinuousLinearEquiv : F →L[ℂ] F) ∘L
            A.toContinuousLinearMap ∘L
              (V.toContinuousLinearEquiv : E →L[ℂ] E) := by
      ext x
      simp
    change S.gaugeReal
        (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).toContinuousLinearMap =
      S.gaugeReal A.toContinuousLinearMap
    rw [hcomp]
    simpa [S] using
      gaugeReal_comp_isometryEquiv_finite N hfinite U V
        A.toContinuousLinearMap

/-- **Finite-dimensional reduction.**

Once finite-dimensional membership is known, the source laws already imply
Fan dominance for arbitrary rectangular finite-dimensional operators.  The
proof is exactly the existing rectangular T-transform theorem, with the bridge
from finite singular-value sums to approximation-number Ky Fan gauges. -/
theorem finiteDimensional_fanDominance_real
    (N : SourceUnitaryInvariantNorm.{0, 0} ℂ)
    (hfinite : HasFiniteDimensionalMembership N)
    {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {A B : E →L[ℂ] F}
    (hAB : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) :
    N.toSymmetricOperatorIdealFamily.gaugeReal A ≤
      N.toSymmetricOperatorIdealFamily.gaugeReal B := by
  have hlin : ∀ k,
      TauCeti.RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k A.toLinearMap ≤
        TauCeti.RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k B.toLinearMap := by
    intro k
    rw [rectangularKyFanSum_eq_kyFanApproximationGauge,
      rectangularKyFanSum_eq_kyFanApproximationGauge]
    have hA : A.toLinearMap.toContinuousLinearMap = A := by
      ext x
      rfl
    have hB : B.toLinearMap.toContinuousLinearMap = B := by
      ext x
      rfl
    rw [hA, hB]
    exact hAB k
  change (finiteRectangularSeminorm N hfinite) A.toLinearMap ≤
    (finiteRectangularSeminorm N hfinite) B.toLinearMap
  exact (finiteRectangularSeminorm N hfinite).apply_le_of_kyFanSum_le hlin

/-- The same finite-dimensional result at the canonical `ℝ≥0∞` gauge level,
which is the shape of `SourceUnitaryInvariantNorm.HasFanDominance`. -/
theorem finiteDimensional_fanDominance
    (N : SourceUnitaryInvariantNorm.{0, 0} ℂ)
    (hfinite : HasFiniteDimensionalMembership N)
    {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {A B : E →L[ℂ] F}
    (hAB : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) :
    N.toSymmetricOperatorIdealFamily.gauge A ≤
      N.toSymmetricOperatorIdealFamily.gauge B := by
  have hA := hfinite A
  have hB := hfinite B
  apply (ENNReal.toReal_le_toReal hA hB).mp
  exact finiteDimensional_fanDominance_real N hfinite hAB

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
