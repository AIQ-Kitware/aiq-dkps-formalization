/-
Final Perfect Quench theorem scaffold.

There are two complete routes:

* finite model classes: raw iid replicates plus a direct target union bound;
* compact infinite model classes: raw iid replicates plus shrinking finite nets
  and response regularity.

Both routes derive population geometry, random spectral regularity, conservative
rate conditions, reference coverage, and the literal target-augmented CMDS
nearest-neighbor estimator.  The final section lifts fixed-subset results to all
proper query subsets.
-/

import DkpsQuench.Perfect.SpectralCapstone

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

namespace DkpsQuench.Perfect

open Acharyya2024
open DkpsQuench.GrowingAcharyyaBridge
open DkpsQuench.GrowingResponseBridge

universe u v wr wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωref : Type wr} [MeasurableSpace Ωref]
variable {Ωresp : Type wy} [MeasurableSpace Ωresp]

/-- Raw data needed to run the conservative finite-model Perfect Quench
pipeline for one query subset. -/
structure FinitePerfectSubsetData (d m p : Nat) where
  perspective : Model Q X → Vec d
  rawResponse : ∀ n, Model Q X → Fin (safeFiniteReplicates n) →
    Ωresp → Acharyya2024.Mat m p
  populationMean : Model Q X → Acharyya2024.Mat m p
  varianceBound : Real
  covarianceFloor : Real
  lipschitzConstant : Real

/-- Honest paper-facing assumptions for one finite-model query subset.

Fields deliberately omitted because the scaffold derives them:

* no sample response means or second-moment events;
* no population configuration, Gram identity, PSD, or rank proof;
* no global eigenvalue floor or ceiling over every sample outcome;
* no explicit CMDS entry-rate or `GrowingConfigControl` certificate;
* no compactness proof for the finite model class;
* no population response-norm envelope, which follows from finiteness;
* no positivity proof for the stored score-Lipschitz constant, which is
  enlarged to `max γ 1` internally.
-/
structure FinitePerfectSubsetAssumptions
    [Fintype (Model Q X)]
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μresp : Nat → Measure Ωresp)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : FinitePerfectSubsetData (Q := Q) (X := X)
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

/-- Literal finite-model Perfect Quench estimator for one query subset. -/
noncomputable def finitePerfectQuenchEstimator
    {d m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : FinitePerfectSubsetData (Q := Q) (X := X)
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

/-- Fixed-subset finite-model Perfect Quench theorem.

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

After those scaffold lemmas are completed, this theorem's visible assumptions
are the intended finite-model Perfect Quench interface.

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
8. Supply score Lipschitzness, positivity, and baseline from `H`; finish by
   `simpa [finitePerfectQuenchEstimator]`.
9. Use named arguments for all large constructors.  This proof should only
   assemble certificates; any failed estimate belongs in a lower module.
-/
theorem perfectQuench_finite_fixedSubset
    [Fintype (Model Q X)]
    {d m p : Nat} (hm : 0 < m)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : FinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p)
    (H : FinitePerfectSubsetAssumptions Pf μresp score Qstar Qsub D) :
    HighProbQQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp H.raw.probability)
      Pf sqLoss (yFull score Qstar)
      (finitePerfectQuenchEstimator f_ref score Qstar D)
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

/-- Raw data needed for one compact infinite-model Perfect Quench theorem. -/
structure InfinitePerfectSubsetData (d m p : Nat) where
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
range.  The scaffold derives the replicate-mean and population-mean regularity,
finite nets, polynomial covering bound, entropy exponent, shrinking radius,
and population response envelope internally.  As in the finite route, the
stored score-Lipschitz constant need not carry a separate positivity proof; the
capstone uses a positive envelope internally. -/
structure InfinitePerfectSubsetAssumptions
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μresp : Nat → Measure Ωresp)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : InfinitePerfectSubsetData (Q := Q) (X := X)
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

/-- Literal compact infinite-model Perfect Quench estimator. -/
noncomputable def infinitePerfectQuenchEstimator
    {d m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : InfinitePerfectSubsetData (Q := Q) (X := X)
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

/-- Fixed-subset compact infinite-model Perfect Quench theorem.

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

Completing it removes the last abstract uniform response-concentration premise
and every explicit net/envelope certificate from the arbitrary-model growing
Quench path.

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
   `simpa [infinitePerfectQuenchEstimator]`.
9. Keep the finite net hidden inside this proof; do not add it or its entropy
   constant to `InfinitePerfectSubsetAssumptions`.
-/
theorem perfectQuench_infinite_fixedSubset
    {d m p : Nat} (hm : 0 < m)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (D : InfinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) d m p)
    (H : InfinitePerfectSubsetAssumptions Pf μresp score Qstar Qsub D) :
    HighProbQQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp H.raw.probability)
      Pf sqLoss (yFull score Qstar)
      (infinitePerfectQuenchEstimator f_ref score Qstar D)
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

/-- All-proper-subsets finite-model Perfect Quench.

Each valid subset receives its own dimensions, data, and assumptions, while the
reference law, response-noise law, and full score are shared.  Once
`perfectQuench_finite_fixedSubset` is complete, this proof is only the
quantifier lift encoded by `HighProbQueryEfficient`.

Implementation recipe (execute in this order):
1. Unfold `HighProbQueryEfficient`, `HighProbQueryEfficientBelow`, and
   `HighProbMQueryEfficient` until the goal introduces `m0`, `hm0`, `Qsub`,
   `hsub`, and `hcard`.
2. Derive `Qsub.card < Qstar.card` from `hcard` and `hm0` (usually by rewriting
   `hcard` into `hm0`).
3. Specialize `hm Qsub hsub hlt` and `H Qsub hsub hlt`.
4. Apply `perfectQuench_finite_fixedSubset` with dimensions
   `d Qsub`, `m Qsub`, `p Qsub` and data `D Qsub`.
5. Resolve the probability-instance equality between the theorem's
   `H.raw.probability` and the supplied `hμresp` by proof irrelevance; `simpa`
   should close it.
6. Finish estimator lambdas by reflexivity.  No event intersection or union over
   query subsets is required because the definition permits a subset-specific
   eventual threshold.
-/
theorem perfectQuench_finite_allQueries
    [Fintype (Model Q X)]
    (d m p : Finset Q → Nat)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : ∀ Qsub, FinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) (d Qsub) (m Qsub) (p Qsub))
    (hm : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      0 < m Qsub)
    (H : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      FinitePerfectSubsetAssumptions Pf μresp score Qstar Qsub (D Qsub)) :
    HighProbQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp hμresp)
      Pf sqLoss Qstar (yFull score Qstar)
      (fun Qsub => finitePerfectQuenchEstimator f_ref score Qstar (D Qsub))
      (fun Qsub _ _ f => yQ score Qsub f) := by
  intro m0 hm0 Qsub hsub hcard
  have hlt : Qsub.card < Qstar.card := by
    simpa [hcard] using hm0
  simpa only using
    (perfectQuench_finite_fixedSubset
      (Q := Q) (X := X) (Ωref := Ωref) (Ωresp := Ωresp)
      (d := d Qsub) (m := m Qsub) (p := p Qsub)
      (hm := hm Qsub hsub hlt)
      (Pf := Pf) (μref := μref) (hμref := hμref) (μresp := μresp)
      (f_ref := f_ref) (hiid := hiid) (score := score)
      (Qstar := Qstar) (Qsub := Qsub) (D := D Qsub)
      (H := H Qsub hsub hlt))

/-- All-proper-subsets compact infinite-model Perfect Quench.

As in the finite theorem, each subset may use its own embedding and response
dimensions, perspective, raw response embedding, and raw-response Lipschitz
constant.  The finite net, entropy exponent, regularity certificates, and norm
envelope are derived within the fixed-subset theorem.  The proof should apply
`perfectQuench_infinite_fixedSubset` subset-by-subset and unfold the all-budget
predicate.

Implementation recipe (execute in this order):
1. Unfold the three high-probability query-efficiency predicates exactly as in
   the finite all-query theorem.
2. Introduce the budget and subset variables and derive the strict-cardinality
   premise expected by `hm` and `H`.
3. Apply `perfectQuench_infinite_fixedSubset` to `D Qsub` with the specialized
   assumptions and positivity proof.
4. Use proof irrelevance to reconcile the stagewise response probability
   instance with `hμresp`, then `simpa` for the estimator families.
5. Do not intersect events across all query subsets: the formal definition and
   the literature quantifier order allow each subset its own eventual event and
   threshold.
-/
theorem perfectQuench_infinite_allQueries
    (d m p : Finset Q → Nat)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : ∀ Qsub, InfinitePerfectSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) (d Qsub) (m Qsub) (p Qsub))
    (hm : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      0 < m Qsub)
    (H : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      InfinitePerfectSubsetAssumptions Pf μresp score Qstar Qsub (D Qsub)) :
    HighProbQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp hμresp)
      Pf sqLoss Qstar (yFull score Qstar)
      (fun Qsub => infinitePerfectQuenchEstimator f_ref score Qstar (D Qsub))
      (fun Qsub _ _ f => yQ score Qsub f) := by
  intro m0 hm0 Qsub hsub hcard
  have hlt : Qsub.card < Qstar.card := by
    simpa [hcard] using hm0
  simpa only using
    (perfectQuench_infinite_fixedSubset
      (Q := Q) (X := X) (Ωref := Ωref) (Ωresp := Ωresp)
      (d := d Qsub) (m := m Qsub) (p := p Qsub)
      (hm := hm Qsub hsub hlt)
      (Pf := Pf) (μref := μref) (hμref := hμref) (μresp := μresp)
      (f_ref := f_ref) (hiid := hiid) (score := score)
      (Qstar := Qstar) (Qsub := Qsub) (D := D Qsub)
      (H := H Qsub hsub hlt))

end DkpsQuench.Perfect
