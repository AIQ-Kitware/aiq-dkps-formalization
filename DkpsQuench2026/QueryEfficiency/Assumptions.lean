/-
Public data, assumption, and estimator interfaces for the raw-response Quench theorem family.

The finite and compact-infinite routes share the same paper-level conclusion but
use different response-concentration mechanisms.  This module contains only the
public interfaces; proof assembly lives in `Finite`, `Infinite`, and
`AllQueries`.
-/

import DkpsQuench2026.QueryEfficiency.Spectral

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory ProbabilityTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench2026.QueryEfficiency

open Acharyya2024
open DkpsQuench2026

universe u v wr wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωref : Type wr} [MeasurableSpace Ωref]
variable {Ωresp : Type wy} [MeasurableSpace Ωresp]
/-- Raw data needed to run the conservative finite-model raw-response Quench
pipeline for one query subset. -/
structure FiniteSubsetData (d m p : Nat) where
  perspective : Model Q X → Vec d
  rawResponse : ∀ n, Model Q X → Fin (safeFiniteReplicates n) →
    Ωresp → Acharyya2024.Mat m p
  populationMean : Model Q X → Acharyya2024.Mat m p
  varianceBound : Real
  covarianceFloor : Real
  lipschitzConstant : Real

/-- Honest paper-facing assumptions for one finite-model query subset.

Fields deliberately omitted because the theorem layer derives them:

* no sample response means or second-moment events;
* no population configuration, Gram identity, PSD, or rank proof;
* no global eigenvalue floor or ceiling over every sample outcome;
* no explicit CMDS entry-rate or `GrowingConfigControl` certificate;
* no compactness proof for the finite model class;
* no population response-norm envelope, which follows from finiteness;
* no positivity proof for the stored score-Lipschitz constant, which is
  enlarged to `max γ 1` internally.
-/
structure FiniteSubsetAssumptions
    [Fintype (Model Q X)]
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μresp : Nat → Measure Ωresp)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : FiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p) : Prop where
  perspective_measurable : Measurable D.perspective
  full_support : PerspectiveFullSupport Pf D.perspective
  raw : RawIIDResponseModel μresp safeFiniteReplicates D.rawResponse
    D.populationMean (fun _ => D.varianceBound)
  response_realization : ModelResponseRealization D.perspective D.populationMean
  nondegenerate : PerspectiveNondegeneracy Pf D.perspective D.covarianceFloor
  score_lipschitz : ∀ f g,
    |score f Qstar - score g Qstar| ≤
      D.lipschitzConstant * ‖D.perspective f - D.perspective g‖
  baseline_pos : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)

/-- Literal finite-model raw-response Quench estimator for one query subset. -/
noncomputable def finiteEstimator
    {d m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : FiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p)
    (n : Nat) (ω : Ωref × Ωresp) (f : Model Q X) : Real :=
  yNNTieAverage_augmentedCMDS (d := d)
    (augmentedSampleResponseDist
      (augmentedRawSampleMean f_ref safeFiniteReplicates D.rawResponse))
    (fun n ω f =>
      Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
        (augmentedRawSampleMean f_ref safeFiniteReplicates D.rawResponse n ω f))
    (liftedReferenceSampler (Ωresp := Ωresp) f_ref)
    score Qstar n ω f
/-- Raw data needed for one compact infinite-model raw-response Quench theorem. -/
structure InfiniteSubsetData (d m p : Nat) where
  perspective : Model Q X → Vec d
  rawResponse : ∀ n, Model Q X →
    Fin (safeEntropyReplicates (5 * d) n) →
    Ωresp → Acharyya2024.Mat m p
  populationMean : Model Q X → Acharyya2024.Mat m p
  varianceBound : Real
  covarianceFloor : Real
  lipschitzConstant : Real
  rawResponseLipschitzConstant : Real

/-- Paper-facing assumptions for one compact infinite-model query subset.

The additional assumption relative to the finite theorem is pathwise
Lipschitz regularity of the raw response embedding over a compact perspective
range.  The theorem layer derives the replicate-mean and population-mean regularity,
finite nets, polynomial covering bound, entropy exponent, shrinking radius,
and population response envelope internally.  As in the finite route, the
stored score-Lipschitz constant need not carry a separate positivity proof; the
capstone uses a positive envelope internally. -/
structure InfiniteSubsetAssumptions
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μresp : Nat → Measure Ωresp)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : InfiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p) : Prop where
  perspective_measurable : Measurable D.perspective
  compact_range : IsCompact (Set.range D.perspective)
  full_support : PerspectiveFullSupport Pf D.perspective
  raw : RawIIDResponseModel μresp
    (safeEntropyReplicates (5 * d)) D.rawResponse
    D.populationMean (fun _ => D.varianceBound)
  raw_lipschitz : RawResponseLipschitz D.perspective
    (safeEntropyReplicates (5 * d)) D.rawResponse
    D.rawResponseLipschitzConstant
  response_realization : ModelResponseRealization D.perspective D.populationMean
  nondegenerate : PerspectiveNondegeneracy Pf D.perspective D.covarianceFloor
  score_lipschitz : ∀ f g,
    |score f Qstar - score g Qstar| ≤
      D.lipschitzConstant * ‖D.perspective f - D.perspective g‖
  baseline_pos : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)

/-- Literal compact infinite-model raw-response Quench estimator. -/
noncomputable def infiniteEstimator
    {d m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : InfiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p)
    (n : Nat) (ω : Ωref × Ωresp) (f : Model Q X) : Real :=
  yNNTieAverage_augmentedCMDS (d := d)
    (augmentedSampleResponseDist
      (augmentedRawSampleMean f_ref
        (safeEntropyReplicates (5 * d)) D.rawResponse))
    (fun n ω f =>
      Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
        (augmentedRawSampleMean f_ref
          (safeEntropyReplicates (5 * d)) D.rawResponse n ω f))
    (liftedReferenceSampler (Ωresp := Ωresp) f_ref)
    score Qstar n ω f

/-- **Relaxing a Lipschitz constant to `max c 1`.**

Both the finite and the infinite subset theorems set `gamma := max c 1` to get a
positive constant, then re-derive the Lipschitz bound at `gamma` in the same
three lines.  Stated over the *statement* of `score_lipschitz` rather than either
assumption structure, since the two carry the field independently. -/
theorem lipschitz_le_max_one {d : Nat}
    {score : Model Q X → Finset Q → Real} {Qstar : Finset Q}
    {perspective : Model Q X → Vec d} {c : Real}
    (hlip : ∀ f g, |score f Qstar - score g Qstar| ≤
      c * ‖perspective f - perspective g‖) :
    ∀ f g, |score f Qstar - score g Qstar| ≤
      max c 1 * ‖perspective f - perspective g‖ := by
  intro f g
  exact (hlip f g).trans
    (mul_le_mul_of_nonneg_right (le_max_left c 1) (norm_nonneg _))

end DkpsQuench2026.QueryEfficiency
