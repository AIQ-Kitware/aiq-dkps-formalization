/-
Compact infinite-model raw-response Quench theorem.
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
/-- Fixed-subset compact infinite-model raw-response Quench theorem.

This theorem has the same proof skeleton as the finite result.  Before the
response subevent step:

1. derive sample and population Lipschitz regularity from `raw_lipschitz`;
2. construct the canonical polynomial finite net with
   `exists_safeGrowingPerspectiveNet`;
3. derive a population response-norm envelope from compactness and population
   Lipschitzness;
4. invoke `augmentedRawResponseMeanSubevents_infinite`, discharging its ratio
   with `safeEntropy_concentration_ratio_zero` and its extension budget with
   `safe_net_extension_budget`.

This removes the abstract uniform response-concentration premise and every
explicit net/envelope certificate from the arbitrary-model growing Quench path.

Implementation recipe (execute in this order):
1. Lift the iid reference sampler to the joint space with
   `iidReferenceSampler_lifted_prod`.
2. Derive `Hreg := uniformModelResponseRegularity_of_raw_lipschitz` from
   `H.raw` and `H.raw_lipschitz`; both sample and population constants are the
   fixed raw-response Lipschitz constant.
3. Construct a canonical net and card bound with
   `exists_safeGrowingPerspectiveNet D.perspective H.compact_range
   D.rawResponseLipschitzConstant H.raw_lipschitz.constant_nonneg`.
4. Derive the population response norm bound from
   `exists_populationMean_norm_bound_of_compact_lipschitz`, using the population
   Lipschitz field of `Hreg`.
5. Build `Hmean := augmentedRawResponseMeanSubevents_infinite`; discharge the
   entropy ratio with `safeEntropy_concentration_ratio_zero` and the selected
   net-card bound, and discharge the extension budget with
   `safe_net_extension_budget` plus the net radius identity.
6. Derive augmented response realization from `H.response_realization`.
7. Build the spectral certificate from
   `exists_growingSpectralSubevents_of_compact_iid_nondegenerate` and the rate
   certificate from `safe_growingConfigControl`.
8. Invoke the response-subevent spectral capstone and finish with
   `simpa [infiniteEstimator]`.
9. Keep the finite net hidden inside this proof; do not add it or its entropy
   constant to `InfiniteSubsetAssumptions`.
-/
theorem infiniteFixedSubset
    {d m p : Nat} (hm : 0 < m)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : InfiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p)
    (H : InfiniteSubsetAssumptions Pf μresp score Qstar Qsub D) :
    HighProbQQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp H.raw.probability)
      Pf sqLoss (yFull score Qstar)
      (infiniteEstimator f_ref score Qstar D)
      (fun _ _ f => yQ score Qsub f) := by
  let hμjoint := jointStageMeasure_probability μref hμref μresp H.raw.probability
  let hiidJoint := iidReferenceSampler_lifted_prod Pf μref hμref μresp
    H.raw.probability f_ref hiid
  let Hreg := uniformModelResponseRegularity_of_raw_lipschitz
    μresp D.perspective (safeEntropyReplicates (5 * d)) D.rawResponse
    D.populationMean (fun _ => D.varianceBound) H.raw
    D.rawResponseLipschitzConstant H.raw_lipschitz
  obtain ⟨net, C, hC, hcard, hradius⟩ :=
    exists_safeGrowingPerspectiveNet D.perspective H.compact_range
      D.rawResponseLipschitzConstant H.raw_lipschitz.constant_nonneg
  obtain ⟨B, hB0, hB⟩ :=
    exists_populationMean_norm_bound_of_compact_lipschitz Pf D.perspective
      H.compact_range D.populationMean D.rawResponseLipschitzConstant
      H.raw_lipschitz.constant_nonneg (fun f g => Hreg.population_lipschitz 0 f g)
  let Hmean := augmentedRawResponseMeanSubevents_infinite
    μref hμref μresp f_ref D.perspective
    (safeEntropyReplicates (5 * d)) D.rawResponse D.populationMean
    (fun _ => D.varianceBound) H.raw net
    (fun _ => D.rawResponseLipschitzConstant)
    (fun _ => D.rawResponseLipschitzConstant)
    safeNetTolerance safeResponseTolerance Hreg
    (fun n => by
      rw [safeNetTolerance]
      exact div_pos (safeResponseTolerance_pos n) (by norm_num))
    (safeEntropy_concentration_ratio_zero (5 * d) D.varianceBound C
      (fun n => (net.centers n).card) hcard)
    (safe_net_extension_budget
      (fun _ => D.rawResponseLipschitzConstant)
      (fun _ => D.rawResponseLipschitzConstant)
      net.radius D.rawResponseLipschitzConstant
      H.raw_lipschitz.constant_nonneg
      (fun _ => H.raw_lipschitz.constant_nonneg)
      (fun _ => H.raw_lipschitz.constant_nonneg)
      (fun n => (net.radius_pos n).le)
      (fun _ => le_rfl) (fun _ => le_rfl)
      (fun n => by simpa [safePerspectiveRadius, hradius n]))
  let hrealize :
      PerspectiveResponseRealization D.perspective
        (liftedReferenceSampler (Ωresp := Ωresp) f_ref)
        (augmentedRawPopulationMean f_ref D.populationMean) :=
    augmentedRawPopulationMean_realization (Ωresp := Ωresp)
      D.perspective f_ref D.populationMean H.response_realization
  obtain ⟨Bψ, hBψ0, hBψ, Hspectral0⟩ :=
    exists_growingSpectralSubevents_of_compact_iid_nondegenerate
      Pf (jointStageMeasure μref μresp) hμjoint D.perspective
      H.perspective_measurable H.compact_range
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
        (augmentedRawSampleMean f_ref
          (safeEntropyReplicates (5 * d)) D.rawResponse))
      (fun n ω f =>
        Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
          (augmentedRawSampleMean f_ref
            (safeEntropyReplicates (5 * d)) D.rawResponse n ω f))
      (liftedReferenceSampler (Ωresp := Ωresp) f_ref)
      score Qstar n ω f)
    (fun _ _ f => yQ score Qsub f)
  exact
    highProbQQueryEfficient_tieAverage_of_responseSubevents_realization_spectralSubevents
      (d := d) (m := m) (p := p)
      (Pf := Pf) (μ := jointStageMeasure μref μresp) (hμ := hμjoint)
      (ψ := D.perspective) (hψmeas := H.perspective_measurable)
      (hcompact := H.compact_range) (hfull := H.full_support)
      (f_ref := liftedReferenceSampler (Ωresp := Ωresp) f_ref)
      (hiid := hiidJoint)
      (Xbar := augmentedRawSampleMean f_ref
        (safeEntropyReplicates (5 * d)) D.rawResponse)
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
