/-
Uniform response concentration over infinite model classes.

The finite-model theorem uses a union bound over every target.  For an infinite
class, raw-response Quench needs a shrinking finite net plus pathwise/population
regularity.  This module keeps the empirical-process argument elementary:
finite-net concentration followed by deterministic Lipschitz extension.
-/

import DkpsQuench2026.Response.Regularity

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

namespace DkpsQuench2026

open Acharyya2024
open Acharyya2025.GrowingResponse

universe u v wr wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωref : Type wr} [MeasurableSpace Ωref]
variable {Ωresp : Type wy} [MeasurableSpace Ωresp]

/-- Uniform model-level response-mean event before references and targets are
assembled into an augmented batch. -/
def modelUniformResponseEvent
    {m p : Nat}
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (η : Nat → Real) (n : Nat) : Set Ωresp :=
  {ω | ∀ f, ‖Xbar n ω f - μmodel f‖ ≤ η n}

/-- Response-mean event checked only on one stage's finite perspective net. -/
def modelNetResponseEventFor
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (net : GrowingPerspectiveNet ψ)
    (τ : Nat → Real) (n : Nat) : Set Ωresp :=
  {ω | ∀ f ∈ net.centers n, ‖Xbar n ω f - μmodel f‖ ≤ τ n}

/-- Finite-net control extends to the full model class under sample and
population Lipschitz regularity.
-/
theorem modelNetResponseEventFor_subset_uniform
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (net : GrowingPerspectiveNet ψ)
    (Lsample Lpopulation τ η : Nat → Real)
    (Hreg : UniformModelResponseRegularity ψ Xbar μmodel
      Lsample Lpopulation)
    (hbudget : ∀ n,
      τ n + (Lsample n + Lpopulation n) * net.radius n ≤ η n)
    (n : Nat) :
    modelNetResponseEventFor ψ Xbar μmodel net τ n ⊆
      modelUniformResponseEvent Xbar μmodel η n := by
  intro ω hω
  simp only [modelNetResponseEventFor, modelUniformResponseEvent, Set.mem_setOf_eq] at hω ⊢
  intro g
  obtain ⟨c, hc, hcov⟩ := net.covers n g
  have h1 : ‖Xbar n ω g - Xbar n ω c‖ ≤ Lsample n * ‖ψ g - ψ c‖ :=
    Hreg.sample_lipschitz n ω g c
  have h2 : ‖Xbar n ω c - μmodel c‖ ≤ τ n := hω c hc
  have h3 : ‖μmodel c - μmodel g‖ ≤ Lpopulation n * ‖ψ c - ψ g‖ :=
    Hreg.population_lipschitz n c g
  have htri : ‖Xbar n ω g - μmodel g‖ ≤
      ‖Xbar n ω g - Xbar n ω c‖ + ‖Xbar n ω c - μmodel c‖ + ‖μmodel c - μmodel g‖ := by
    have heq : Xbar n ω g - μmodel g =
        Xbar n ω g - Xbar n ω c + (Xbar n ω c - μmodel c) + (μmodel c - μmodel g) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hsym : ‖ψ g - ψ c‖ = ‖ψ c - ψ g‖ := norm_sub_rev _ _
  have hle : ‖ψ c - ψ g‖ ≤ net.radius n := hcov.le
  have hb1 : Lsample n * ‖ψ g - ψ c‖ ≤ Lsample n * net.radius n := by
    rw [hsym]; exact mul_le_mul_of_nonneg_left hle (Hreg.sample_nonneg n)
  have hb3 : Lpopulation n * ‖ψ c - ψ g‖ ≤ Lpopulation n * net.radius n :=
    mul_le_mul_of_nonneg_left hle (Hreg.population_nonneg n)
  have hbud : τ n + (Lsample n * net.radius n + Lpopulation n * net.radius n) ≤ η n := by
    have := hbudget n; rwa [add_mul] at this
  linarith [htri, h1, h2, h3, hb1, hb3, hbud]

/-- Measurability of the finite-net response event.

Only finite intersections are involved; the population response is constant
on the response sample space.
-/
theorem measurableSet_modelNetResponseEventFor
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (net : GrowingPerspectiveNet ψ)
    (τ : Nat → Real)
    (hXbar : ∀ n f, Measurable fun ω => Xbar n ω f)
    (n : Nat) :
    MeasurableSet (modelNetResponseEventFor ψ Xbar μmodel net τ n) := by
  unfold modelNetResponseEventFor
  exact measurableSet_finset_all (net.centers n)
    (fun f => {ω | ‖Xbar n ω f - μmodel f‖ ≤ τ n})
    (fun f _ => measurableSet_le
      (((hXbar n f).sub measurable_const).norm) measurable_const)

/-- Finite-net response concentration from uniform modelwise second moments.

The proof is a Chebyshev bound for each center followed by a finite union bound.
The only growth quantity is the actual cardinality of the chosen stage net.
This theorem intentionally does not hide that entropy term behind a vague
uniform-concentration premise.
-/
theorem highProb_modelNetResponseEventFor_of_secondMoment
    {d m p : Nat}
    (μresp : Nat → Measure Ωresp) (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (net : GrowingPerspectiveNet ψ)
    (σ2 τ : Nat → Real)
    (hint : ∀ n f,
      Integrable (fun ω => ‖Xbar n ω f - μmodel f‖ ^ 2) (μresp n))
    (hσ2 : ∀ n f,
      ∫ ω, ‖Xbar n ω f - μmodel f‖ ^ 2 ∂(μresp n) ≤ σ2 n)
    (hτ : ∀ n, 0 < τ n)
    (hratio : Tendsto (fun n =>
      ((net.centers n).card : Real) * σ2 n / (τ n) ^ 2) atTop (𝓝 0)) :
    HighProbAtTop μresp hμresp
      (modelNetResponseEventFor ψ Xbar μmodel net τ) := by
  apply highProbAtTop_of_tendsto_compl_zero
  have hbound : ∀ n,
      μresp n ((modelNetResponseEventFor ψ Xbar μmodel net τ n)ᶜ)
        ≤ ENNReal.ofReal (((net.centers n).card : Real) * σ2 n / (τ n) ^ 2) := by
    intro n
    have hincl : (modelNetResponseEventFor ψ Xbar μmodel net τ n)ᶜ
        ⊆ ⋃ f ∈ net.centers n, {ω | τ n < ‖Xbar n ω f - μmodel f‖} := by
      intro ω hω
      simp only [modelNetResponseEventFor, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall,
        not_le] at hω
      obtain ⟨f, hfc, hfgt⟩ := hω
      exact Set.mem_biUnion hfc hfgt
    have hcheb : ∀ f, μresp n {ω | τ n < ‖Xbar n ω f - μmodel f‖}
        ≤ ENNReal.ofReal (σ2 n / (τ n) ^ 2) := fun f =>
      TauCeti.meas_gt_le_ofReal_integral_sq_div_sq (μresp n) (hint n f) (hτ n) (hσ2 n f)
    calc
      μresp n ((modelNetResponseEventFor ψ Xbar μmodel net τ n)ᶜ)
          ≤ μresp n (⋃ f ∈ net.centers n, {ω | τ n < ‖Xbar n ω f - μmodel f‖}) :=
            measure_mono hincl
      _ ≤ ∑ f ∈ net.centers n, μresp n {ω | τ n < ‖Xbar n ω f - μmodel f‖} :=
            measure_biUnion_finset_le _ _
      _ ≤ ∑ _f ∈ net.centers n, ENNReal.ofReal (σ2 n / (τ n) ^ 2) :=
            Finset.sum_le_sum fun f _ => hcheb f
      _ = ((net.centers n).card : ENNReal) * ENNReal.ofReal (σ2 n / (τ n) ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (((net.centers n).card : Real) * (σ2 n / (τ n) ^ 2)) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (((net.centers n).card : Real) * σ2 n / (τ n) ^ 2) := by
            congr 1; ring
  have hub : Tendsto
      (fun n => ENNReal.ofReal (((net.centers n).card : Real) * σ2 n / (τ n) ^ 2))
      atTop (𝓝 0) := by simpa using ENNReal.tendsto_ofReal hratio
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
    (fun _ => zero_le) hbound

/-- Infinite-class uniform response concentration by finite nets and
regularity.

Once this is complete, the arbitrary-model growing response bridge no longer
needs uniform concentration as an external input.  Applications supply a
shrinking net, pointwise second moments, and pathwise/population regularity.
-/
theorem highProb_modelUniformResponseEvent_of_net_regular
    {d m p : Nat}
    (μresp : Nat → Measure Ωresp) (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (ψ : Model Q X → Vec d)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (net : GrowingPerspectiveNet ψ)
    (Lsample Lpopulation σ2 τ η : Nat → Real)
    (Hreg : UniformModelResponseRegularity ψ Xbar μmodel
      Lsample Lpopulation)
    (hint : ∀ n f,
      Integrable (fun ω => ‖Xbar n ω f - μmodel f‖ ^ 2) (μresp n))
    (hσ2 : ∀ n f,
      ∫ ω, ‖Xbar n ω f - μmodel f‖ ^ 2 ∂(μresp n) ≤ σ2 n)
    (hτ : ∀ n, 0 < τ n)
    (hratio : Tendsto (fun n =>
      ((net.centers n).card : Real) * σ2 n / (τ n) ^ 2) atTop (𝓝 0))
    (hbudget : ∀ n,
      τ n + (Lsample n + Lpopulation n) * net.radius n ≤ η n) :
    HighProbAtTop μresp hμresp
      (modelUniformResponseEvent Xbar μmodel η) :=
  HighProbAtTop.mono
    (highProb_modelNetResponseEventFor_of_secondMoment μresp hμresp ψ Xbar μmodel net σ2 τ
      hint hσ2 hτ hratio)
    (fun n => modelNetResponseEventFor_subset_uniform ψ Xbar μmodel net Lsample Lpopulation
      τ η Hreg hbudget n)

/-- A model-uniform response event implies every target-augmented response
event, including randomly selected references.
-/
theorem modelUniformResponseEvent_subset_augmented
    {m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (Xbar : Nat → Ωresp → Model Q X → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (η : Nat → Real) (n : Nat) :
    {ω : Ωref × Ωresp | ω.2 ∈ modelUniformResponseEvent Xbar μmodel η n} ⊆
      augmentedUniformResponseMeanEvent
        (fun n ω f i => Xbar n ω.2
          (augmentedModelAt f_ref n ω.1 f i))
        (augmentedRawPopulationMean f_ref μmodel) η n := by
  intro ω hω f i
  exact hω (augmentedModelAt f_ref n ω.1 f i)

/-- Lift a high-probability response-only event to the independent joint sample
space.
-/
theorem highProb_prod_mk_right
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp) (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (E : Nat → Set Ωresp)
    (hEmeas : ∀ n, MeasurableSet (E n))
    (hE : HighProbAtTop μresp hμresp E) :
    HighProbAtTop (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp hμresp)
      (fun n => {ω : Ωref × Ωresp | ω.2 ∈ E n}) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hE δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hrect : {ω : Ωref × Ωresp | ω.2 ∈ E n} = (Set.univ : Set Ωref) ×ˢ E n := by
    ext ω; simp
  show ((μref n).prod (μresp n)) {ω : Ωref × Ωresp | ω.2 ∈ E n} ≥ 1 - δ
  haveI := hμref n
  rw [hrect, Measure.prod_prod, measure_univ, one_mul]
  exact hN n hn

/-- Infinite-model augmented response concentration from raw iid replicates,
shrinking perspective nets, and response regularity.

This is the final response-statistics seam needed by the infinite-model
raw-response Quench capstone.  No finite model-class assumption remains.
-/
theorem highProb_augmentedRawResponseMean_infinite
    {d m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (net : GrowingPerspectiveNet ψ)
    (Lsample Lpopulation τ η : Nat → Real)
    (Hreg : UniformModelResponseRegularity ψ
      (modelReplicateMean replicates Y) μmodel Lsample Lpopulation)
    (hτ : ∀ n, 0 < τ n)
    (hratio : Tendsto (fun n =>
      ((net.centers n).card : Real) * (variance n / replicates n) /
        (τ n) ^ 2) atTop (𝓝 0))
    (hbudget : ∀ n,
      τ n + (Lsample n + Lpopulation n) * net.radius n ≤ η n) :
    HighProbAtTop (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp Hraw.probability)
      (augmentedUniformResponseMeanEvent
        (augmentedRawSampleMean f_ref replicates Y)
        (augmentedRawPopulationMean f_ref μmodel) η) := by
  have hXbar : ∀ n f, Measurable (fun ω => modelReplicateMean replicates Y n ω f) := by
    intro n f
    simp only [modelReplicateMean, replicateMean]
    exact (Finset.measurable_sum _ (fun k _ => Hraw.measurable n f k)).const_smul
      ((replicates n : Real)⁻¹)
  have hint : ∀ n f,
      Integrable (fun ω => ‖modelReplicateMean replicates Y n ω f - μmodel f‖ ^ 2) (μresp n) := by
    intro n f
    haveI := Hraw.probability n
    have hL2 : MemLp (fun ω => modelReplicateMean replicates Y n ω f) 2 (μresp n) := by
      simp only [modelReplicateMean, replicateMean]
      exact (memLp_finsetSum _ (fun k _ => Hraw.memLp_two n f k)).const_smul
        ((replicates n : Real)⁻¹)
    exact ((hL2.sub (memLp_const _)).norm).integrable_sq
  have hσ2 : ∀ n f,
      ∫ ω, ‖modelReplicateMean replicates Y n ω f - μmodel f‖ ^ 2 ∂(μresp n)
        ≤ variance n / replicates n := fun n f =>
    integral_norm_sq_modelReplicateMean_sub_mean_le μresp replicates Y μmodel variance Hraw n f
  have hnet : HighProbAtTop μresp Hraw.probability
      (modelNetResponseEventFor ψ (modelReplicateMean replicates Y) μmodel net τ) :=
    highProb_modelNetResponseEventFor_of_secondMoment μresp Hraw.probability ψ
      (modelReplicateMean replicates Y) μmodel net (fun n => variance n / replicates n) τ
      hint hσ2 hτ hratio
  have hEmeas : ∀ n, MeasurableSet
      (modelNetResponseEventFor ψ (modelReplicateMean replicates Y) μmodel net τ n) :=
    fun n => measurableSet_modelNetResponseEventFor ψ (modelReplicateMean replicates Y) μmodel
      net τ hXbar n
  have hjoint := highProb_prod_mk_right μref hμref μresp Hraw.probability
    (modelNetResponseEventFor ψ (modelReplicateMean replicates Y) μmodel net τ) hEmeas hnet
  refine HighProbAtTop.mono hjoint (fun n ω hω => ?_)
  have huniform : ω.2 ∈ modelUniformResponseEvent (modelReplicateMean replicates Y) μmodel η n :=
    modelNetResponseEventFor_subset_uniform ψ (modelReplicateMean replicates Y) μmodel net
      Lsample Lpopulation τ η Hreg hbudget n hω
  exact modelUniformResponseEvent_subset_augmented f_ref (modelReplicateMean replicates Y)
    μmodel η n huniform

/-- Measurable finite-net subevents for infinite-model augmented response
concentration.

The event stored in this certificate is the product lift of the finite-net
response event, not the universal target event.  Its subset field performs the
regularity extension and augmented-batch reduction.  This design is essential:
it avoids asking Lean to prove measurability of an uncountable intersection.
-/
noncomputable def augmentedRawResponseMeanSubevents_infinite
    {d m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (ψ : Model Q X → Vec d)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (net : GrowingPerspectiveNet ψ)
    (Lsample Lpopulation τ η : Nat → Real)
    (Hreg : UniformModelResponseRegularity ψ
      (modelReplicateMean replicates Y) μmodel Lsample Lpopulation)
    (hτ : ∀ n, 0 < τ n)
    (hratio : Tendsto (fun n =>
      ((net.centers n).card : Real) * (variance n / replicates n) /
        (τ n) ^ 2) atTop (𝓝 0))
    (hbudget : ∀ n,
      τ n + (Lsample n + Lpopulation n) * net.radius n ≤ η n) :
    AugmentedResponseMeanSubevents
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp Hraw.probability)
      (augmentedRawSampleMean f_ref replicates Y)
      (augmentedRawPopulationMean f_ref μmodel) η := by
  have hXbar : ∀ n f, Measurable (fun ω => modelReplicateMean replicates Y n ω f) := by
    intro n f
    simp only [modelReplicateMean, replicateMean]
    exact (Finset.measurable_sum _ (fun k _ => Hraw.measurable n f k)).const_smul
      ((replicates n : Real)⁻¹)
  have hint : ∀ n f,
      Integrable (fun ω => ‖modelReplicateMean replicates Y n ω f - μmodel f‖ ^ 2) (μresp n) := by
    intro n f
    haveI := Hraw.probability n
    have hL2 : MemLp (fun ω => modelReplicateMean replicates Y n ω f) 2 (μresp n) := by
      simp only [modelReplicateMean, replicateMean]
      exact (memLp_finsetSum _ (fun k _ => Hraw.memLp_two n f k)).const_smul
        ((replicates n : Real)⁻¹)
    exact ((hL2.sub (memLp_const _)).norm).integrable_sq
  have hσ2 : ∀ n f,
      ∫ ω, ‖modelReplicateMean replicates Y n ω f - μmodel f‖ ^ 2 ∂(μresp n)
        ≤ variance n / replicates n := fun n f =>
    integral_norm_sq_modelReplicateMean_sub_mean_le μresp replicates Y μmodel variance Hraw n f
  have hnet : HighProbAtTop μresp Hraw.probability
      (modelNetResponseEventFor ψ (modelReplicateMean replicates Y) μmodel net τ) :=
    highProb_modelNetResponseEventFor_of_secondMoment μresp Hraw.probability ψ
      (modelReplicateMean replicates Y) μmodel net (fun n => variance n / replicates n) τ
      hint hσ2 hτ hratio
  have hEmeas : ∀ n, MeasurableSet
      (modelNetResponseEventFor ψ (modelReplicateMean replicates Y) μmodel net τ n) :=
    fun n => measurableSet_modelNetResponseEventFor ψ (modelReplicateMean replicates Y) μmodel
      net τ hXbar n
  exact
    { event := fun n => {ω : Ωref × Ωresp |
        ω.2 ∈ modelNetResponseEventFor ψ (modelReplicateMean replicates Y) μmodel net τ n}
      measurable := fun n => measurable_snd (hEmeas n)
      highProb := highProb_prod_mk_right μref hμref μresp Hraw.probability
        (modelNetResponseEventFor ψ (modelReplicateMean replicates Y) μmodel net τ) hEmeas hnet
      subset := fun n ω hω =>
        modelUniformResponseEvent_subset_augmented f_ref (modelReplicateMean replicates Y)
          μmodel η n
          (modelNetResponseEventFor_subset_uniform ψ (modelReplicateMean replicates Y) μmodel
            net Lsample Lpopulation τ η Hreg hbudget n hω) }

end DkpsQuench2026
