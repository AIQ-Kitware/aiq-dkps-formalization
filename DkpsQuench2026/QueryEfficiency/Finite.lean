/-
Finite-model raw-response Quench theorem.
-/

import DkpsQuench2026.QueryEfficiency.Assumptions

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
/-- Fixed-subset finite-model raw-response Quench theorem.

Proof assembly guide:

1. derive compactness and a population response-norm envelope from
   `Fintype`;
2. lift the iid reference sampler to the product space;
3. construct the finite raw-response subevent certificate using
   `safeFinite_concentration_ratio_zero`;
4. derive target-augmented population realization from
   `response_realization`;
5. construct centered population geometry;
6. obtain the high-probability spectral certificate from iid covariance
   concentration and `nondegenerate`;
7. build `GrowingConfigControl` using `safe_growingConfigControl`;
8. invoke
   `highProbQQueryEfficient_tieAverage_of_responseSubevents_realization_spectralSubevents`.

The theorem's visible assumptions
are the intended finite-model raw-response Quench interface.

Implementation recipe (execute in this order):
1. Install `H.raw.probability` and construct the product-space iid reference
   sampler with `iidReferenceSampler_lifted_prod`; use
   `hiid.measurable` for the reference measurability argument.
2. Obtain a finite-model population norm bound `B` from
   `exists_populationMean_norm_bound_finite D.populationMean`.
3. Build `Hmean := augmentedRawResponseMeanSubevents_finite` with
   `replicates := safeFiniteReplicates`, `η := safeResponseTolerance`, and
   variance `fun _ => D.varianceBound`; discharge its ratio with
   `safeFinite_concentration_ratio_zero (Fintype.card (Model Q X))
   D.varianceBound`.
4. Derive target-augmented realization using
   `augmentedRawPopulationMean_realization D.perspective f_ref
   D.populationMean H.response_realization`.
5. Obtain `Bψ` and the spectral certificate from
   `exists_growingSpectralSubevents_of_compact_iid_nondegenerate`; compactness of
   the finite perspective range follows from finiteness.
6. Build `Hrate` with `safe_growingConfigControl m d hm B Bψ
   D.covarianceFloor`; use nonnegativity of `B`, `Bψ`, and
   `H.nondegenerate.kappa_pos`.
7. Invoke
   `highProbQQueryEfficient_tieAverage_of_responseSubevents_realization_spectralSubevents`
   on the joint space, with the lifted sampler, raw augmented sample/population
   means, `Hmean`, realization, spectral certificate, and `Hrate`.
8. Supply score Lipschitzness and the positive baseline from `H`; the theorem internally enlarges the Lipschitz constant to a positive envelope; finish by
   `simpa [finiteEstimator]`.
9. Use named arguments for all large constructors.  This proof should only
   assemble certificates; any failed estimate belongs in a lower module.
-/
theorem finiteFixedSubset
    [Fintype (Model Q X)]
    {d m p : Nat} (hm : 0 < m)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : FiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p)
    (H : FiniteSubsetAssumptions Pf μresp score Qstar Qsub D) :
    HighProbQQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp H.raw.probability)
      Pf sqLoss (yFull score Qstar)
      (finiteEstimator f_ref score Qstar D)
      (fun _ _ f => yQ score Qsub f) := by
  let hμjoint := jointStageMeasure_probability μref hμref μresp H.raw.probability
  let hiidJoint := iidReferenceSampler_lifted_prod Pf μref hμref μresp
    H.raw.probability f_ref hiid
  obtain ⟨B, hB0, hB⟩ :=
    exists_populationMean_norm_bound_finite D.populationMean
  let Hmean := augmentedRawResponseMeanSubevents_finite
    μref hμref μresp f_ref hiid.measurable
    safeFiniteReplicates D.rawResponse D.populationMean
    (fun _ => D.varianceBound) safeResponseTolerance H.raw
    safeResponseTolerance_pos
    (safeFinite_concentration_ratio_zero
      (Fintype.card (Model Q X)) D.varianceBound)
  let hrealize :
      PerspectiveResponseRealization D.perspective
        (liftedReferenceSampler (Ωresp := Ωresp) f_ref)
        (augmentedRawPopulationMean f_ref D.populationMean) :=
    augmentedRawPopulationMean_realization (Ωresp := Ωresp)
      D.perspective f_ref D.populationMean H.response_realization
  let hcompact : IsCompact (Set.range D.perspective) :=
    isCompact_range_of_fintype D.perspective
  obtain ⟨Bψ, hBψ0, hBψ, Hspectral0⟩ :=
    exists_growingSpectralSubevents_of_compact_iid_nondegenerate
      Pf (jointStageMeasure μref μresp) hμjoint D.perspective
      H.perspective_measurable hcompact
      (liftedReferenceSampler (Ωresp := Ωresp) f_ref) hiidJoint
      (augmentedRawPopulationMean f_ref D.populationMean) hrealize H.nondegenerate
  let Hspectral := Classical.choice Hspectral0
  let Hrate := safe_growingConfigControl m d hm B Bψ D.covarianceFloor
    hB0 hBψ0 H.nondegenerate.kappa_pos
  let gamma : Real := max D.lipschitzConstant 1
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    exact lt_of_lt_of_le zero_lt_one (le_max_right D.lipschitzConstant 1)
  have hlipschitz : ∀ f g,
      |score f Qstar - score g Qstar| ≤
        gamma * ‖D.perspective f - D.perspective g‖ := by
    intro f g
    exact (H.score_lipschitz f g).trans
      (mul_le_mul_of_nonneg_right
        (le_max_left D.lipschitzConstant 1) (norm_nonneg _))
  change HighProbQQueryEfficient (Q := Q) (X := X)
    (jointStageMeasure μref μresp) hμjoint Pf sqLoss
    (yFull score Qstar)
    (fun n ω f => yNNTieAverage_augmentedCMDS (d := d)
      (augmentedSampleResponseDist
        (augmentedRawSampleMean f_ref safeFiniteReplicates D.rawResponse))
      (fun n ω f =>
        Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
          (augmentedRawSampleMean f_ref safeFiniteReplicates D.rawResponse n ω f))
      (liftedReferenceSampler (Ωresp := Ωresp) f_ref)
      score Qstar n ω f)
    (fun _ _ f => yQ score Qsub f)
  exact
    highProbQQueryEfficient_tieAverage_of_responseSubevents_realization_spectralSubevents
      (d := d) (m := m) (p := p)
      (Pf := Pf) (μ := jointStageMeasure μref μresp) (hμ := hμjoint)
      (ψ := D.perspective) (hψmeas := H.perspective_measurable)
      (hcompact := hcompact) (hfull := H.full_support)
      (f_ref := liftedReferenceSampler (Ωresp := Ωresp) f_ref)
      (hiid := hiidJoint)
      (Xbar := augmentedRawSampleMean f_ref safeFiniteReplicates D.rawResponse)
      (μbar := augmentedRawPopulationMean f_ref D.populationMean)
      (η := safeResponseTolerance) (B := fun _ => B)
      (hηNonneg := fun n => (safeResponseTolerance_pos n).le)
      (Hmean := Hmean)
      (hpopulationNorm := augmentedRawPopulationMean_norm_le f_ref D.populationMean hB)
      (hrealize := hrealize)
      (α := D.covarianceFloor / 2)
      (hα := by linarith [H.nondegenerate.kappa_pos])
      (ceiling := fun n => 4 * ((n + 1 : Nat) : Real) * Bψ ^ 2)
      (Hspectral := Hspectral) (Hrate := Hrate)
      (score := score) (Qstar := Qstar) (Qsub := Qsub)
      (γ := gamma) (hlip := hlipschitz)
      (hγ := hgamma) (hbase := H.baseline_pos)


end DkpsQuench2026.QueryEfficiency
