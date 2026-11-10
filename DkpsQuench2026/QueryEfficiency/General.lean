/-
Raw-response Quench Theorem 2 over a general model class.

This is the paper-scope theorem.  The finite route (`finiteFixedSubset`) and the
compact-infinite route (`infiniteFixedSubset`) bound the estimation error for every
target model simultaneously on one high-probability event, which is what forces a
finite model class or a compact perspective range plus pathwise response
regularity.  The paper's Theorem 2 bounds a mean squared error, an average over the
target, and its model space is neither finite nor compact.

The theorem here controls one target at a time.  For each target `f`, the stage-`n`
good event asks that

* the `n + 1` response means of the references and `f` are close to their
  population means (a finite union bound at the source rate `r = ω(n³)`),
* the population CMDS matrix of the augmented batch satisfies the spectral floor
  and ceiling (uniform in the target, from the covariance floor), and
* some reference lies within the coverage radius of `f` (full support and iid
  sampling).

On that event the literal tie-averaged estimator is accurate for `f`.  The paper's
`[0, 1]` score range then turns these target-by-target events into a
high-probability MSE bound (`highProb_mse_le_of_targetwise`), with no finiteness,
compactness, or regularity of the model class.

The remaining hypotheses beyond the printed text are measurability of the
perspective map and of the raw responses, which are well-definedness conditions of
the printed probabilities and expectations.  The response envelope
`GeneralSubsetAssumptions.response_bounded` is the bounded-support condition of the
inherited Theorem 1 setting (Acharyya et al. 2025: the response distributions
`F_ij` are supported on a bounded subset of `ℝ^p`).

The estimator follows the classical-MDS reading of the paper's Eq. (1); see the
header of `DkpsQuench2026.Geometry.AugmentedCMDS`.
-/

module

public import DkpsQuench2026.QueryEfficiency.Assumptions
public import DkpsQuench2026.Probability.TargetIntegration

public section

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
open Acharyya2025.Bridge
open Acharyya2025.Deterministic
open Acharyya2025.MathlibBridge
open Acharyya2025.ConfigPerturbation
open Acharyya2025.GrowingPipeline
open Acharyya2025.GrowingResponse
open TauCeti.Matrix (opSym)

universe u v wr wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

variable {Ωref : Type wr} [MeasurableSpace Ωref]
variable {Ωresp : Type wy} [MeasurableSpace Ωresp]

/-- The model in one coordinate of the augmented batch depends measurably on the
target and the reference sample jointly. -/
theorem measurable_augmentedModelAt_target
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (n : Nat) (i : Fin (n + 1)) :
    Measurable (fun z : Model Q X × Ωref => augmentedModelAt f_ref n z.2 z.1 i) := by
  induction i using Fin.lastCases with
  | last => simpa [augmentedModelAt] using measurable_fst
  | cast j =>
    simpa [augmentedModelAt, Function.comp_def] using
      (href n j).comp (measurable_snd (α := Model Q X) (β := Ωref))

/-- The augmented raw sample response mean is jointly measurable in the target and
the sample. -/
theorem measurable_augmentedRawSampleMean_target
    {m p : Nat}
    {μresp : Nat → Measure Ωresp} {replicates : Nat → Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    {Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p}
    {μmodel : Model Q X → Acharyya2024.Mat m p} {variance : Nat → Real}
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (n : Nat) (i : Fin (n + 1)) :
    Measurable (fun z : Model Q X × (Ωref × Ωresp) =>
      augmentedRawSampleMean f_ref replicates Y n z.2 z.1 i) := by
  have hsel : Measurable (fun z : Model Q X × (Ωref × Ωresp) =>
      augmentedModelAt f_ref n z.2.1 z.1 i) :=
    (measurable_augmentedModelAt_target f_ref href n i).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hpair : Measurable (fun z : Model Q X × (Ωref × Ωresp) =>
      (augmentedModelAt f_ref n z.2.1 z.1 i, z.2.2)) :=
    hsel.prodMk (measurable_snd.comp measurable_snd)
  simp only [augmentedRawSampleMean, modelReplicateMean, replicateMean]
  exact (Finset.measurable_sum _
    (fun k _ => (Hraw.jointly_measurable n k).comp hpair)).const_smul
    ((replicates n : Real)⁻¹)

/-- The augmented population response mean is jointly measurable in the target and
the sample. -/
theorem measurable_augmentedRawPopulationMean_target
    {m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    {μmodel : Model Q X → Acharyya2024.Mat m p} (hμmodel : Measurable μmodel)
    (n : Nat) (i : Fin (n + 1)) :
    Measurable (fun z : Model Q X × (Ωref × Ωresp) =>
      augmentedRawPopulationMean f_ref μmodel n z.2 z.1 i) := by
  simp only [augmentedRawPopulationMean]
  exact hμmodel.comp ((measurable_augmentedModelAt_target f_ref href n i).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))

/-- A bounded population response envelope bounds the perspective range, through
the model-level response realization. -/
theorem perspective_norm_le_of_response_bound
    {d m p : Nat}
    (ψ : Model Q X → Vec d) (μmodel : Model Q X → Acharyya2024.Mat m p)
    (hrealize : ModelResponseRealization ψ μmodel)
    {B : Real} (hB : ∀ f, ‖μmodel f‖ ≤ B) (f₀ : Model Q X) (f : Model Q X) :
    ‖ψ f‖ ≤ ‖ψ f₀‖ + (m : Real)⁻¹ * (2 * B) := by
  have hdiff : ‖μmodel f - μmodel f₀‖ ≤ 2 * B :=
    (norm_sub_le _ _).trans (by linarith [hB f, hB f₀])
  have hψ : ‖ψ f - ψ f₀‖ ≤ (m : Real)⁻¹ * (2 * B) := by
    rw [← hrealize f f₀]
    exact mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (Nat.cast_nonneg m))
  calc ‖ψ f‖ ≤ ‖ψ f₀‖ + ‖ψ f - ψ f₀‖ := norm_le_insert' _ _
    _ ≤ ‖ψ f₀‖ + (m : Real)⁻¹ * (2 * B) := by linarith

/-- **Paper-facing assumptions for one query subset over a general model class.**

Every field is the paper's, read through its imported Theorem 1:

* `full_support` -- Assumption 2 (Model Distribution Support), in its repaired
  target-ball form;
* `score_lipschitz` -- Assumption 1 (Lipschitz Score Function);
* `score_mem_unit` -- the score's typing `y : F × 2^{Q*} → [0, 1]`;
* `raw` -- iid embedded responses with `sup_ij trace(Cov(F_ij)) = O(1)`, the
  setting of Theorem 1;
* `response_bounded` -- the response distributions are supported on a bounded
  set, the setting of the imported Acharyya et al. (2025) theorem; only a bound on
  the population means is used;
* `response_realization` -- the population means realize the perspectives, which
  is the definition of the DKPS;
* `nondegenerate` -- the eigenvalue floor among the "technical assumptions" of
  Theorem 1 (Acharyya et al. 2025, Assumptions 1 and 2);
* `baseline_pos` -- Theorem 2's own condition `MSE(ŷ_Q) > 0`;
* `perspective_measurable` -- a well-definedness condition of Assumption 2's
  probabilities.

There is no finiteness or compactness of the model class, no regularity of the
responses in the model, and no positivity proof for the Lipschitz constant. -/
structure GeneralSubsetAssumptions
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μresp : Nat → Measure Ωresp)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    {replicates : Nat → Nat}
    (D : FiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) replicates d m p) : Prop where
  perspective_measurable : Measurable D.perspective
  full_support : PerspectiveFullSupport Pf D.perspective
  raw : RawIIDResponseModel μresp replicates D.rawResponse
    D.populationMean (fun _ => D.varianceBound)
  response_bounded : ∃ B, ∀ f, ‖D.populationMean f‖ ≤ B
  response_realization : ModelResponseRealization D.perspective D.populationMean
  nondegenerate : PerspectiveNondegeneracy Pf D.perspective D.covarianceFloor
  score_mem_unit : ∀ f, ∀ Q' ⊆ Qstar, score f Q' ∈ Set.Icc (0 : Real) 1
  score_lipschitz : ∀ f g,
    |score f Qstar - score g Qstar| ≤
      D.lipschitzConstant * ‖D.perspective f - D.perspective g‖
  baseline_pos : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)

/-- **Paper Theorem 2, first conclusion, over a general model class.**

For every `ε > 0` the literal tie-averaged nearest-neighbor predictor built from raw
cached responses eventually has `MSE ≤ ε` with high probability, at the source
replicate rate `r = ω(n³)`.  The model class is arbitrary.
`GeneralSubsetAssumptions.baseline_pos` is not used. -/
theorem generalFixedSubsetMSE
    {d m p : Nat} (hm : 0 < m)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    {replicates : Nat → Nat} (hrate : SourceReplicateRate replicates)
    (D : FiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) replicates d m p)
    (H : GeneralSubsetAssumptions Pf μresp score Qstar Qsub D) :
    ∀ ε : Real, 0 < ε →
      HighProbAtTop (jointStageMeasure μref μresp)
        (jointStageMeasure_probability μref hμref μresp H.raw.probability)
        (fun n => {ω |
          MSE Pf (yFull score Qstar)
            (fun f => finiteEstimator f_ref score Qstar D n ω f) ≤ ε}) := by
  intro ε hε
  let μ := jointStageMeasure μref μresp
  let hμ := jointStageMeasure_probability μref hμref μresp H.raw.probability
  have hiidJoint := iidReferenceSampler_lifted_prod Pf μref hμref μresp
    H.raw.probability f_ref hiid
  let ψ := D.perspective
  let fr := liftedReferenceSampler (Ωresp := Ωresp) f_ref
  let Xbar := augmentedRawSampleMean f_ref replicates D.rawResponse
  let μbar := augmentedRawPopulationMean (Ωresp := Ωresp) f_ref D.populationMean
  let η := safeResponseTolerance
  -- Response envelope and the perspective bound it implies.
  obtain ⟨B₀, hB₀⟩ := H.response_bounded
  let B : Real := max B₀ 0
  have hBnn : 0 ≤ B := le_max_right _ _
  have hB : ∀ f, ‖D.populationMean f‖ ≤ B := fun f => (hB₀ f).trans (le_max_left _ _)
  have : Nonempty (Model Q X) := nonempty_of_isProbabilityMeasure Pf
  let f₀ : Model Q X := Classical.arbitrary _
  have hbdd : Bornology.IsBounded (Set.range ψ) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨_, by
      rintro _ ⟨f, rfl⟩
      exact perspective_norm_le_of_response_bound ψ D.populationMean
        H.response_realization hB f₀ f⟩
  -- Spectral certificate, uniform in the target, from the covariance floor.
  let hrealize : PerspectiveResponseRealization ψ fr μbar :=
    augmentedRawPopulationMean_realization (Ωresp := Ωresp)
      ψ f_ref D.populationMean H.response_realization
  obtain ⟨Bψ, hBψ0, hBψ, Hspectral0⟩ :=
    exists_growingSpectralSubevents_of_bounded_iid_nondegenerate
      Pf μ hμ ψ H.perspective_measurable hbdd fr hiidJoint μbar hrealize
      H.nondegenerate
  let Hspectral := Classical.choice Hspectral0
  let Hrate := safe_growingConfigControl m d hm B Bψ D.covarianceFloor
    hBnn hBψ0 H.nondegenerate.kappa_pos
  -- Lipschitz constant and the accuracy budget.
  let γ : Real := max D.lipschitzConstant 1
  have hγ : 0 < γ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlip : ∀ f g,
      |score f Qstar - score g Qstar| ≤ γ * ‖ψ f - ψ g‖ :=
    lipschitz_le_max_one H.score_lipschitz
  let t : Real := ε / 2
  have ht : 0 < t := by positivity
  let ρ : Real := Real.sqrt t / (2 * γ)
  let cmax : Real := Real.sqrt t / (4 * γ)
  have hρ : 0 < ρ := by positivity
  have hcmax : 0 < cmax := by positivity
  let radialRate : Nat → Real := fun n => 2 * Hrate.bound n
  have hradialRateZero : Tendsto radialRate atTop (𝓝 0) := by
    simpa [radialRate] using tendsto_const_nhds.mul Hrate.bound_zero
  have hradialRateNonneg : ∀ n, 0 ≤ radialRate n := fun n =>
    mul_nonneg (by norm_num) (Hrate.bound_nonneg n)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hradialRateZero cmax hcmax
  -- Deterministic stage conditions.
  let good : Nat → Prop := fun n =>
    N < n ∧ d ≤ n + 1 ∧
      configFrobBound d (max ((n : Real)) 1 * (D.covarianceFloor / 2))
        (4 * ((n + 1 : Nat) : Real) * Bψ ^ 2)
        (((n + 1 : Nat) : Real) *
          cmdsEntrywiseRate (n + 1) m (responseDistBound m (B + η n)) (η n)) ≤
        Hrate.bound n
  have hgood : ∀ᶠ n in atTop, good n := by
    filter_upwards [eventually_gt_atTop N, eventually_dimension_le_succ d,
      Hrate.configFrobBound_le] with n hn hdim hbound
    exact ⟨hn, hdim, hbound⟩
  -- The target-by-target good sets.
  let respClose : Nat → Set (Model Q X × (Ωref × Ωresp)) := fun n =>
    {z | ∀ i, ‖Xbar n z.2 z.1 i - μbar n z.2 z.1 i‖ ≤ η n}
  let covered : Nat → Set (Model Q X × (Ωref × Ωresp)) := fun n =>
    {z | ∃ j : Fin n, ‖ψ (fr n z.2 j) - ψ z.1‖ < ρ}
  let G : Nat → Set (Model Q X × (Ωref × Ωresp)) := fun n =>
    {_z | good n} ∩ (Prod.snd ⁻¹' Hspectral.event n) ∩ respClose n ∩ covered n
  have hrespMeas : ∀ n, MeasurableSet (respClose n) := by
    intro n
    simp only [respClose, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      ((measurable_augmentedRawSampleMean_target f_ref hiid.measurable H.raw n i).sub
        (measurable_augmentedRawPopulationMean_target (Ωresp := Ωresp) f_ref
          hiid.measurable H.raw.mean_measurable n i)).norm
      measurable_const
  have hcoveredMeas : ∀ n, MeasurableSet (covered n) := by
    intro n
    simp only [covered, Set.ofPred_exists]
    exact MeasurableSet.iUnion fun j => measurableSet_lt
      ((H.perspective_measurable.comp
          ((hiidJoint.measurable n j).comp measurable_snd)).sub
        (H.perspective_measurable.comp measurable_fst)).norm
      measurable_const
  have hGmeas : ∀ n, MeasurableSet (G n) := fun n =>
    (((MeasurableSet.const _).inter
      (measurable_snd (Hspectral.measurable n))).inter (hrespMeas n)).inter
      (hcoveredMeas n)
  -- The estimator is the radial tie average, hence stays in `[0, 1]`.
  have hy : ∀ f, yFull score Qstar f ∈ Set.Icc (0 : Real) 1 := fun f =>
    H.score_mem_unit f Qstar subset_rfl
  have hest : ∀ n ω f, finiteEstimator f_ref score Qstar D n ω f =
      radialTieAverageNN
        (augmentedSpectralRadialDistance (d := d)
          (augmentedSampleResponseDist Xbar)
          (fun n ω f =>
            Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
              (Xbar n ω f)))
        fr (yFull score Qstar) n ω f := fun _ _ _ => rfl
  have hyhat : ∀ n ω f,
      finiteEstimator f_ref score Qstar D n ω f ∈ Set.Icc (0 : Real) 1 := by
    intro n ω f
    rw [hest]
    by_cases hn : n > 0
    · rw [radialTieAverageNN_of_pos _ _ _ n ω f hn]
      exact radialTieAverage_mem_Icc hn _ _
        (fun i => (hy _).1) (fun i => (hy _).2)
    · rw [radialTieAverageNN_of_not_pos _ _ _ n ω f hn]
      exact ⟨le_rfl, zero_le_one⟩
  -- On a good set the squared error is at most `t`.
  have herr : ∀ n f ω, (f, ω) ∈ G n →
      sqLoss (finiteEstimator f_ref score Qstar D n ω f) (yFull score Qstar f) ≤ t := by
    rintro n f ω ⟨⟨⟨⟨hNn, hdim, hbound⟩, hspec⟩, hresp⟩, hcover⟩
    have hnpos : n > 0 := lt_of_le_of_lt (Nat.zero_le N) hNn
    have hentry : EntrywiseClose
        (classicalMDSMatrix (augmentedSampleResponseDist Xbar n ω f))
        (classicalMDSMatrix (responseDist (μbar n ω f)))
        (cmdsEntrywiseRate (n + 1) m (responseDistBound m (B + η n)) (η n)) := by
      simpa [augmentedSampleResponseDist] using
        cmdsEntrywise_of_responseMeanClose_of_population_norm (by omega)
          (Xbar n ω f) (μbar n ω f) (safeResponseTolerance_pos n).le hresp
          (augmentedRawPopulationMean_norm_le f_ref D.populationMean hB n ω f)
    have hrad : ∀ i, |augmentedSpectralRadialDistance (d := d)
          (augmentedSampleResponseDist Xbar)
          (fun n ω f =>
            Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
              (Xbar n ω f)) n ω f i -
          ‖ψ (fr n ω i) - ψ f‖| ≤ radialRate n :=
      fun i => abs_augmentedSpectralRadialDistance_sub_le ψ fr
        (augmentedSampleResponseDist Xbar) (fun n ω f => responseDist (μbar n ω f))
        (fun n ω f =>
          Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar n ω f))
        (centeredAugmentedPerspectiveConfig ψ fr)
        (centeredAugmentedPerspectiveConfig_gram_eq ψ fr μbar hrealize)
        (centeredAugmentedPerspectiveConfig_radial ψ fr)
        (fun n => mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
          (by linarith [H.nondegenerate.kappa_pos]))
        Hrate hdim hbound hentry
        (Hspectral.floor n ω hspec f) (Hspectral.ceiling_bound n ω hspec f) i
    have hcLe : radialRate n ≤ cmax := by
      have h := hN n hNn.le
      rw [Real.dist_eq, sub_zero] at h
      exact (le_abs_self _).trans h.le
    obtain ⟨j, hj⟩ := hcover
    have hpoint := radialTieAverage_pointwise_error hnpos
      (fun i => ‖ψ (fr n ω i) - ψ f‖) _ (radialRate n) ρ γ
      (hradialRateNonneg n) hρ.le hγ.le hrad ⟨j, hj.le⟩
      (fun i => yFull score Qstar (fr n ω i)) (yFull score Qstar f)
      (fun i => hlip (fr n ω i) f)
    rw [hest, radialTieAverageNN_of_pos _ _ _ n ω f hnpos]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hpoint 2
    rw [sq_abs] at hsq
    exact hsq.trans (by
      simpa [ρ, cmax] using radial_parameter_choice t γ (radialRate n)
        ht hγ (hradialRateNonneg n) hcLe)
  -- Each fixed target is good with high probability.
  have hG : ∀ f, HighProbAtTop μ hμ (fun n => Prod.mk f ⁻¹' G n) := by
    intro f
    have := hμ
    have hrespSecMeas : ∀ n, MeasurableSet (Prod.mk f ⁻¹' respClose n) := fun n =>
      measurable_prodMk_left (hrespMeas n)
    have hrespHP : HighProbAtTop μ hμ (fun n => Prod.mk f ⁻¹' respClose n) := by
      have hT := highProb_uniformTargetResponseMeanClose_of_secondMoment
        (T := Unit) μ (fun n => n + 1)
        (fun n ω _ i => Xbar n ω f i) (fun n ω _ i => μbar n ω f i)
        (fun n => D.varianceBound / replicates n) η
        (fun n _ i => integrable_sq_augmentedRawSampleMean_sub_population
          μref hμref μresp f_ref hiid.measurable replicates D.rawResponse
          D.populationMean (fun _ => D.varianceBound) H.raw n f i)
        (fun n _ i => integral_norm_sq_augmentedRawSampleMean_sub_population_le
          μref hμref μresp f_ref hiid.measurable replicates D.rawResponse
          D.populationMean (fun _ => D.varianceBound) H.raw n f i)
        safeResponseTolerance_pos
        (by simpa using
          finite_concentration_ratio_zero_of_sourceRate hrate 1 D.varianceBound)
      exact HighProbAtTop.mono (show HighProbAtTop μ hμ _ from hT) fun n ω hω i => hω () i
    have hcoverHP : HighProbAtTop μ hμ (fun n => Prod.mk f ⁻¹' covered n) :=
      HighProbAtTop.mono
        (highProb_referenceHits Pf μ hμ fr hiidJoint (perspectiveBall ψ f ρ)
          (measurableSet_perspectiveBall ψ H.perspective_measurable f ρ)
          (H.full_support.measure_pos f hρ))
        fun n ω hω => by
          obtain ⟨j, hj⟩ := mem_referenceHits.mp hω
          exact ⟨j, mem_perspectiveBall.mp hj⟩
    have hcoverSecMeas : ∀ n, MeasurableSet (Prod.mk f ⁻¹' covered n) := fun n =>
      measurable_prodMk_left (hcoveredMeas n)
    have hAll := HighProbAtTop.inter
      (HighProbAtTop.inter Hspectral.highProb hrespHP Hspectral.measurable hrespSecMeas)
      hcoverHP (fun n => (Hspectral.measurable n).inter (hrespSecMeas n)) hcoverSecMeas
    refine hAll.mono_eventually ?_
    filter_upwards [hgood] with n hn
    rintro ω ⟨⟨hspec, hresp⟩, hcov⟩
    exact ⟨⟨⟨hn, hspec⟩, hresp⟩, hcov⟩
  have hmain := highProb_mse_le_of_targetwise Pf μ hμ (yFull score Qstar)
    (fun n ω f => finiteEstimator f_ref score Qstar D n ω f) hy hyhat ht.le
    G hGmeas herr hG ht
  refine HighProbAtTop.mono hmain fun n ω hω => ?_
  simpa only [Set.mem_ofPred_eq, t, add_halves] using hω

/-- **Paper Theorem 2 over a general model class: fixed-subset query efficiency.**

With the paper's condition `MSE(ŷ_Q) > 0`, the literal tie-averaged estimator is
eventually no worse than the subset-score baseline with high probability. -/
theorem generalFixedSubset
    {d m p : Nat} (hm : 0 < m)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    {replicates : Nat → Nat} (hrate : SourceReplicateRate replicates)
    (D : FiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) replicates d m p)
    (H : GeneralSubsetAssumptions Pf μresp score Qstar Qsub D) :
    HighProbQQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp H.raw.probability)
      Pf sqLoss (yFull score Qstar)
      (finiteEstimator f_ref score Qstar D)
      (fun _ _ f => yQ score Qsub f) := by
  apply highProbQQueryEfficient_of_mse_atTop Pf
    (jointStageMeasure μref μresp)
    (jointStageMeasure_probability μref hμref μresp H.raw.probability)
    (yFull score Qstar) (yQ score Qsub)
    (finiteEstimator f_ref score Qstar D)
  · exact generalFixedSubsetMSE (Q := Q) (X := X) (Ωref := Ωref) (Ωresp := Ωresp)
      (d := d) (m := m) (p := p) hm Pf μref hμref μresp f_ref hiid score Qstar Qsub
      hrate D H
  · exact H.baseline_pos

/-- **Paper Theorem 2 over a general model class: all proper query subsets.**

Each proper subset receives its own dimensions, data, and assumptions, while the
reference law, response-noise law, and full score are shared; this is the
quantifier order of the paper's query-efficiency definition. -/
theorem generalAllQueries
    (d m p : Finset Q → Nat)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (replicates : Finset Q → Nat → Nat)
    (hrate : ∀ Qsub, SourceReplicateRate (replicates Qsub))
    (D : ∀ Qsub, FiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) (replicates Qsub) (d Qsub) (m Qsub) (p Qsub))
    (hm : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      0 < m Qsub)
    (H : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      GeneralSubsetAssumptions Pf μresp score Qstar Qsub (D Qsub)) :
    HighProbQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp hμresp)
      Pf sqLoss Qstar (yFull score Qstar)
      (fun Qsub => finiteEstimator f_ref score Qstar (D Qsub))
      (fun Qsub _ _ f => yQ score Qsub f) := by
  intro m0 hm0 Qsub hsub hcard
  have hlt : Qsub.card < Qstar.card := by
    simpa [hcard] using hm0
  simpa only using
    (generalFixedSubset
      (Q := Q) (X := X) (Ωref := Ωref) (Ωresp := Ωresp)
      (d := d Qsub) (m := m Qsub) (p := p Qsub)
      (hm := hm Qsub hsub hlt)
      (Pf := Pf) (μref := μref) (hμref := hμref) (μresp := μresp)
      (f_ref := f_ref) (hiid := hiid) (score := score)
      (Qstar := Qstar) (Qsub := Qsub) (hrate := hrate Qsub) (D := D Qsub)
      (H := H Qsub hsub hlt))

end DkpsQuench2026.QueryEfficiency
