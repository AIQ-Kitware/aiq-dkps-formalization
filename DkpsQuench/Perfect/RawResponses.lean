/-
Raw iid response observations for Perfect Quench.

Reference sampling and response sampling are placed on separate probability
spaces and then combined with a product measure.  This is not cosmetic: if a
random reference index and its cached response array lived on the same opaque
sample space, selecting the response array by the random model could introduce
selection bias.  The product construction makes the required independence
structural.
-/

import DkpsQuench.Perfect.SpectralRegularity

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
open Acharyya2025.GrowingResponse
open DkpsQuench.GrowingResponseBridge

universe u v wr wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωref : Type wr} [MeasurableSpace Ωref]
variable {Ωresp : Type wy} [MeasurableSpace Ωresp]

/-- Stagewise product measure carrying independent reference and response
randomness. -/
noncomputable def jointStageMeasure
    (μref : Nat → Measure Ωref) (μresp : Nat → Measure Ωresp) :
    Nat → Measure (Ωref × Ωresp) :=
  fun n => (μref n).prod (μresp n)

/-- Lift a reference sampler to the joint space by ignoring response
randomness. -/
def liftedReferenceSampler
    (f_ref : ∀ n, Ωref → Fin n → Model Q X) :
    ∀ n, Ωref × Ωresp → Fin n → Model Q X :=
  fun n ω i => f_ref n ω.1 i

/-- Per-model average of the raw cached response replicates. -/
noncomputable def modelReplicateMean
    {m p : Nat}
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (n : Nat) (ωresp : Ωresp) (f : Model Q X) : Acharyya2024.Mat m p :=
  replicateMean (Y n f) ωresp

/-- Target-augmented sample response means on the product sample space. -/
noncomputable def augmentedRawSampleMean
    {m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (n : Nat) (ω : Ωref × Ωresp) (f : Model Q X) :
    Fin (n + 1) → Acharyya2024.Mat m p :=
  fun i => modelReplicateMean replicates Y n ω.2
    (augmentedModelAt f_ref n ω.1 f i)

/-- Target-augmented population response means.  These depend on the reference
sample through the selected reference models, but not on response noise. -/
def augmentedRawPopulationMean
    {m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (n : Nat) (ω : Ωref × Ωresp) (f : Model Q X) :
    Fin (n + 1) → Acharyya2024.Mat m p :=
  fun i => μmodel (augmentedModelAt f_ref n ω.1 f i)

/-- Product of probability measures is a probability measure.

This should be a thin wrapper around Mathlib's product-measure instance.  Keep
it separate so all later files can install the stagewise instance with one
line.

Implementation recipe (execute in this order):
1. Introduce `n` and install `hμref n` and `hμresp n` as local instances with
   `letI`.
2. Unfold `jointStageMeasure`.
3. Let typeclass synthesis close `IsProbabilityMeasure ((μref n).prod
   (μresp n))`; the Mathlib product-measure probability instance should apply.
4. If synthesis does not fire, prove `measure_univ = 1` using
   `Measure.prod_apply` on `univ ×ˢ univ`, the measurable-univ facts, and the two
   probability masses.  Do not add sigma-finiteness assumptions; probability
   measures already provide them.
-/
theorem jointStageMeasure_probability
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp) (hμresp : ∀ n, IsProbabilityMeasure (μresp n)) :
    ∀ n, IsProbabilityMeasure (jointStageMeasure μref μresp n) := by
  intro n
  letI := hμref n
  letI := hμresp n
  unfold jointStageMeasure
  infer_instance

/-- The lifted reference sampler preserves its iid law under independent
product extension.

Suggested proof route: measurable coordinate maps are compositions with
`Prod.fst`; every joint event is a cylinder set `A ×ˢ univ`; install the two
stagewise probability instances, apply the product-measure formula, and simplify
the response-space mass to one.

Implementation recipe (execute in this order):
1. Inspect the fields of `IIDReferenceSampler` and refine them one at a time; do
   not unfold the whole structure in the goal.
2. For every measurability field, compose `hiid.measurable n i` with
   `measurable_fst` and simplify `liftedReferenceSampler`.
3. For each marginal-law field, rewrite a preimage under the lifted map as a
   cylinder set `A ×ˢ Set.univ`.
4. Apply the product-measure rectangle formula, using measurability from the
   original iid sampler, then simplify `(μresp n) univ = 1` under
   `hμresp n`.
5. For pairwise independence/joint-law fields, perform the same cylinder-set
   reduction for two coordinates and reuse the corresponding field of `hiid`.
6. Search the exact structure declaration before coding; every resulting proof
   should be a wrapper around an existing `hiid` field, not a new iid argument.
-/
theorem iidReferenceSampler_lifted_prod
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp) (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref) :
    IIDReferenceSampler Pf (jointStageMeasure μref μresp)
      (liftedReferenceSampler (Ωresp := Ωresp) f_ref) := by
  sorry

/-- Model-level response-distance realization automatically realizes every
random target-augmented population batch.

Implementation recipe (execute in this order):
1. Introduce `n ω f i j` and unfold `PerspectiveResponseRealization`,
   `augmentedRawPopulationMean`, and `liftedReferenceSampler` only at the goal.
2. Simplify the two selected population means to
   `μmodel (augmentedModelAt f_ref n ω.1 f i)` and the analogous `j` term.
3. Apply `hrealize` to those two models.
4. Finish by `rfl`/`simpa [augmentedModelAt]`; the response-space coordinate is
   irrelevant.  No case split on `i` or `j` is needed.
-/
theorem augmentedRawPopulationMean_realization
    {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (hrealize : ModelResponseRealization ψ μmodel) :
    PerspectiveResponseRealization ψ
      (liftedReferenceSampler (Ωresp := Ωresp) f_ref)
      (augmentedRawPopulationMean f_ref μmodel) := by
  intro n ω f i j
  simp only [responseDist, responseDistEntry, augmentedRawPopulationMean,
    liftedReferenceSampler, augmentedModelAt]
  exact hrealize _ _

/-- A model-level population norm envelope lifts to every augmented batch. -/
theorem augmentedRawPopulationMean_norm_le
    {m p : Nat}
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    {B : Real} (hB : ∀ f, ‖μmodel f‖ ≤ B) :
    ∀ n (ω : Ωref × Ωresp) f i,
      ‖augmentedRawPopulationMean f_ref μmodel n ω f i‖ ≤ B := by
  intro n ω f i
  exact hB _

/-- Second-moment bound for one model's concrete replicate average.

Suggested proof route: install `Hraw.probability n` locally and apply
`integral_norm_sq_replicateMean_sub_mean_le_of_bound` from
`Acharyya2025.GrowingResponse` with the corresponding structure fields.

Implementation recipe (execute in this order):
1. Install `Hraw.probability n` as the local probability instance.
2. Unfold `modelReplicateMean` only enough to expose `replicateMean`.
3. Apply
   `integral_norm_sq_replicateMean_sub_mean_le_of_bound` from
   `Acharyya2025.GrowingResponse` with:
   `P := μresp n`, `r := replicates n`, `Y := Y n f`, `μ := μmodel f`, and
   variance bound `variance n`.
4. Discharge its premises respectively with `Hraw.replicates_pos`,
   `Hraw.memLp_two`, `Hraw.mean_entry`, `Hraw.pairwise_independent`, and
   `Hraw.second_moment`.
5. Use named arguments and `simpa [modelReplicateMean]` to avoid universe or
   dependent-index elaboration failures.
-/
theorem integral_norm_sq_modelReplicateMean_sub_mean_le
    {m p : Nat}
    (μresp : Nat → Measure Ωresp)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (n : Nat) (f : Model Q X) :
    ∫ ωresp,
      ‖modelReplicateMean replicates Y n ωresp f - μmodel f‖ ^ 2
        ∂(μresp n) ≤ variance n / replicates n := by
  haveI := Hraw.probability n
  -- Upgrade the coordinate means to a Bochner (vector-valued) mean.
  have hmean : ∀ k, ∫ ω, Y n f k ω ∂(μresp n) = μmodel f := by
    intro k
    have hint : Integrable (Y n f k) (μresp n) :=
      (Hraw.memLp_two n f k).integrable one_le_two
    ext c
    have h : (EuclideanSpace.proj c : Acharyya2024.Mat m p →L[Real] Real)
          (∫ ω, Y n f k ω ∂(μresp n)) = ∫ ω, Y n f k ω c ∂(μresp n) :=
      (ContinuousLinearMap.integral_comp_comm _ hint).symm
    rw [Hraw.mean_entry n f k c] at h
    exact h
  -- Apply the universe-polymorphic sample-mean second-moment bound.
  have hbound := ForMathlib.integral_norm_sq_average_sub_le_of_bound
    (μresp n) (Hraw.replicates_pos n) (Y n f) (μmodel f)
    (Hraw.memLp_two n f) hmean (Hraw.pairwise_independent n f) (Hraw.second_moment n f)
  simpa [modelReplicateMean, replicateMean] using hbound

/-- Uniform modelwise second moments transfer through random reference
selection on the independent product space.

This is the Fubini/selection lemma.  For each fixed reference outcome, every
augmented coordinate selects some model, and the response-space integral is
bounded uniformly by the preceding theorem.  Integrate that bound over the
reference space.  Do not assume the model class is finite.

Implementation recipe (execute in this order):
1. Unfold the two augmented means and set
   `g ωref := augmentedModelAt f_ref n ωref f i`.
2. Use the product-integral/Fubini theorem to rewrite the joint integral as
   `∫ ωref, ∫ ωresp, ‖modelReplicateMean ... (g ωref) - μmodel (g ωref)‖²
   ∂μresp n ∂μref n`.
3. Prove the integrand is jointly measurable/integrable from `href`,
   `Hraw.jointly_measurable`, and the finite-sum definition of the replicate
   mean.  If needed, first establish a local measurable function lemma for the
   selected model.
4. For each fixed `ωref`, apply
   `integral_norm_sq_modelReplicateMean_sub_mean_le` to `g ωref`.
5. Integrate the constant upper bound over `μref n`; install `hμref n` and
   simplify its total mass to one.
6. Do not use finiteness of the model class; the uniform modelwise second-moment
   field is exactly what makes random selection harmless.
-/
theorem integral_norm_sq_augmentedRawSampleMean_sub_population_le
    {m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (n : Nat) (f : Model Q X) (i : Fin (n + 1)) :
    ∫ ω,
      ‖augmentedRawSampleMean f_ref replicates Y n ω f i -
        augmentedRawPopulationMean f_ref μmodel n ω f i‖ ^ 2
        ∂(jointStageMeasure μref μresp n) ≤
      variance n / replicates n := by
  haveI := hμref n
  haveI := Hraw.probability n
  have hC0 : (0 : Real) ≤ variance n / replicates n := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    have hk : (0 : Real) ≤
        ∫ ω, ‖Y n f ⟨0, Hraw.replicates_pos n⟩ ω - μmodel f‖ ^ 2 ∂(μresp n) :=
      integral_nonneg fun _ => by positivity
    exact le_trans hk (Hraw.second_moment n f ⟨0, Hraw.replicates_pos n⟩)
  by_cases hInt : Integrable
      (fun ω => ‖augmentedRawSampleMean f_ref replicates Y n ω f i -
        augmentedRawPopulationMean f_ref μmodel n ω f i‖ ^ 2)
      (jointStageMeasure μref μresp n)
  · have hprod : jointStageMeasure μref μresp n = (μref n).prod (μresp n) := rfl
    rw [hprod] at hInt ⊢
    rw [MeasureTheory.integral_prod _ hInt]
    have hfib : ∀ ωref, ∫ ωresp,
        ‖augmentedRawSampleMean f_ref replicates Y n (ωref, ωresp) f i -
          augmentedRawPopulationMean f_ref μmodel n (ωref, ωresp) f i‖ ^ 2 ∂(μresp n)
          ≤ variance n / replicates n := by
      intro ωref
      simpa [augmentedRawSampleMean, augmentedRawPopulationMean]
        using integral_norm_sq_modelReplicateMean_sub_mean_le μresp replicates Y μmodel
          variance Hraw n (augmentedModelAt f_ref n ωref f i)
    have hconst : ∫ _ωref : Ωref, (variance n / (replicates n : Real)) ∂(μref n)
        = variance n / replicates n := by
      simp
    exact le_trans
      (integral_mono hInt.integral_prod_left (integrable_const _) hfib) (le_of_eq hconst)
  · rw [integral_undef hInt]; exact hC0

/-- Measurability and integrability package for augmented raw sample errors.

The proof should use product measurability, finite replicate sums, and the
measurability fields in `RawIIDResponseModel`.  The population term depends only
on the reference coordinate; its measurability follows from the reference
sampler and any model-level measurability needed by the application.  If the
current `IIDReferenceSampler` interface is insufficient, add the smallest
model-level measurability field to `RawIIDResponseModel` rather than assuming
measurability separately at every augmented index.

Implementation recipe (execute in this order):
1. Prove measurability of the selected raw response
   `(ωref,ωresp) ↦ Y n (augmentedModelAt ... ωref ...) k ωresp` by composing
   `href` with `Hraw.jointly_measurable n k`.
2. Deduce measurability of `augmentedRawSampleMean` from the finite replicate sum
   and scalar multiplication; use `Hraw.replicates_pos n` only for algebra, not
   measurability.
3. Prove measurability of the population term using `Hraw.mean_measurable`
   composed with the selected-model map.
4. Hence the squared norm error is measurable.
5. Obtain a finite integral bound from
   `integral_norm_sq_augmentedRawSampleMean_sub_population_le`; combine
   nonnegativity with the finite real bound to show the integral is not `∞`.
6. Conclude `Integrable` using `integrableOn_iff_compl`/`integrable_iff_norm` or
   the lemma converting measurable nonnegative functions with finite integral.
7. If the current interfaces cannot prove step 1, add one reusable helper about
   measurability of `augmentedModelAt`; do not add per-index assumptions to this
   theorem.
-/
theorem integrable_sq_augmentedRawSampleMean_sub_population
    {m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (n : Nat) (f : Model Q X) (i : Fin (n + 1)) :
    Integrable (fun ω =>
      ‖augmentedRawSampleMean f_ref replicates Y n ω f i -
        augmentedRawPopulationMean f_ref μmodel n ω f i‖ ^ 2)
      (jointStageMeasure μref μresp n) := by
  haveI := hμref n
  haveI := Hraw.probability n
  have hsel : Measurable (fun ωref => augmentedModelAt f_ref n ωref f i) := by
    induction i using Fin.lastCases with
    | last => simp [augmentedModelAt]
    | cast j => simpa [augmentedModelAt] using href n j
  have hpair : Measurable (fun ω : Ωref × Ωresp =>
      (augmentedModelAt f_ref n ω.1 f i, ω.2)) :=
    (hsel.comp measurable_fst).prodMk measurable_snd
  have hmeasSample : Measurable (fun ω : Ωref × Ωresp =>
      augmentedRawSampleMean f_ref replicates Y n ω f i) := by
    simp only [augmentedRawSampleMean, modelReplicateMean, replicateMean]
    exact (Finset.measurable_sum _
      (fun k _ => (Hraw.jointly_measurable n k).comp hpair)).const_smul
      ((replicates n : Real)⁻¹)
  have hmeasPop : Measurable (fun ω : Ωref × Ωresp =>
      augmentedRawPopulationMean f_ref μmodel n ω f i) := by
    simp only [augmentedRawPopulationMean]
    exact Hraw.mean_measurable.comp (hsel.comp measurable_fst)
  have hmeas : Measurable (fun ω : Ωref × Ωresp =>
      ‖augmentedRawSampleMean f_ref replicates Y n ω f i -
        augmentedRawPopulationMean f_ref μmodel n ω f i‖ ^ 2) :=
    (hmeasSample.sub hmeasPop).norm.pow_const 2
  -- Per-fiber second-moment bound (uniform in the reference outcome).
  have hfib : ∀ ωref, ∫ ωresp,
      ‖augmentedRawSampleMean f_ref replicates Y n (ωref, ωresp) f i -
        augmentedRawPopulationMean f_ref μmodel n (ωref, ωresp) f i‖ ^ 2 ∂(μresp n)
        ≤ variance n / replicates n := fun ωref => by
    simpa [augmentedRawSampleMean, augmentedRawPopulationMean]
      using integral_norm_sq_modelReplicateMean_sub_mean_le μresp replicates Y μmodel variance
        Hraw n (augmentedModelAt f_ref n ωref f i)
  -- Per-fiber integrability (the replicate mean is L², so its centred square is L¹).
  have hfibInt : ∀ ωref, Integrable (fun ωresp =>
      ‖augmentedRawSampleMean f_ref replicates Y n (ωref, ωresp) f i -
        augmentedRawPopulationMean f_ref μmodel n (ωref, ωresp) f i‖ ^ 2) (μresp n) := by
    intro ωref
    have hL2 : MemLp (fun ωresp =>
        augmentedRawSampleMean f_ref replicates Y n (ωref, ωresp) f i) 2 (μresp n) := by
      simp only [augmentedRawSampleMean, modelReplicateMean, replicateMean]
      exact (memLp_finsetSum _ (fun k _ =>
        Hraw.memLp_two n (augmentedModelAt f_ref n ωref f i) k)).const_smul
        ((replicates n : Real)⁻¹)
    have hpop : MemLp (fun ωresp =>
        augmentedRawPopulationMean f_ref μmodel n (ωref, ωresp) f i) 2 (μresp n) := by
      simp only [augmentedRawPopulationMean]; exact memLp_const _
    exact (hL2.sub hpop).norm.integrable_sq
  have hprod : jointStageMeasure μref μresp n = (μref n).prod (μresp n) := rfl
  rw [hprod, MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Eventually.of_forall hfibInt, ?_⟩
  refine Integrable.mono' (integrable_const (variance n / replicates n))
    (hmeas.aestronglyMeasurable.norm.integral_prod_right') (Eventually.of_forall fun ωref => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  refine le_trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun ωresp => ?_))) (hfib ωref)
  exact Real.norm_of_nonneg (by positivity)

/-- Measurability of the target-augmented raw response event.

Use joint measurability of the raw response array, measurability of the model
mean, and measurability of the lifted reference sampler.  The universal target
quantifier is finite in the theorem below; the infinite-model path avoids this
event and uses measurable finite-net subevents instead.

Implementation recipe (execute in this order):
1. Unfold `augmentedUniformResponseMeanEvent`; rewrite the universal quantifiers
   as finite conjunctions over `Finset.univ : Finset (Model Q X)` and
   `Finset.univ : Finset (Fin (n+1))`.
2. For fixed `f,i`, prove measurability of the scalar map
   `ω ↦ ‖augmentedRawSampleMean ... ω f i - augmentedRawPopulationMean ... ω f i‖`
   using the measurability construction from
   `integrable_sq_augmentedRawSampleMean_sub_population` (or factor that
   construction into a helper lemma).
3. Apply `measurableSet_le` against the constant `η n`.
4. Apply `measurableSet_finset_all` twice to assemble the event.
5. The parameter `variance` is only carried through `Hraw`; do not try to use a
   moment bound in this measurability proof.
-/
theorem measurableSet_augmentedRawResponseMeanEvent_finite
    [Fintype (Model Q X)]
    {m p : Nat}
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ω => f_ref n ω i)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance η : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (n : Nat) :
    MeasurableSet (augmentedUniformResponseMeanEvent
      (augmentedRawSampleMean f_ref replicates Y)
      (augmentedRawPopulationMean f_ref μmodel) η n) := by
  have hmeas : ∀ (f : Model Q X) (i : Fin (n + 1)),
      Measurable (fun ω : Ωref × Ωresp =>
        ‖augmentedRawSampleMean f_ref replicates Y n ω f i -
          augmentedRawPopulationMean f_ref μmodel n ω f i‖) := by
    intro f i
    have hsel : Measurable (fun ωref => augmentedModelAt f_ref n ωref f i) := by
      induction i using Fin.lastCases with
      | last => simp [augmentedModelAt]
      | cast j => simpa [augmentedModelAt] using href n j
    have hpair : Measurable (fun ω : Ωref × Ωresp =>
        (augmentedModelAt f_ref n ω.1 f i, ω.2)) :=
      (hsel.comp measurable_fst).prodMk measurable_snd
    have hmeasSample : Measurable (fun ω : Ωref × Ωresp =>
        augmentedRawSampleMean f_ref replicates Y n ω f i) := by
      simp only [augmentedRawSampleMean, modelReplicateMean, replicateMean]
      exact (Finset.measurable_sum _
        (fun k _ => (Hraw.jointly_measurable n k).comp hpair)).const_smul
        ((replicates n : Real)⁻¹)
    have hmeasPop : Measurable (fun ω : Ωref × Ωresp =>
        augmentedRawPopulationMean f_ref μmodel n ω f i) := by
      simp only [augmentedRawPopulationMean]
      exact Hraw.mean_measurable.comp (hsel.comp measurable_fst)
    exact (hmeasSample.sub hmeasPop).norm
  have hev : augmentedUniformResponseMeanEvent (augmentedRawSampleMean f_ref replicates Y)
      (augmentedRawPopulationMean f_ref μmodel) η n
      = ⋂ f, ⋂ i, {ω : Ωref × Ωresp |
          ‖augmentedRawSampleMean f_ref replicates Y n ω f i -
            augmentedRawPopulationMean f_ref μmodel n ω f i‖ ≤ η n} := by
    ext ω
    simp only [augmentedUniformResponseMeanEvent, Acharyya2025.Bridge.UniformResponseMeanClose,
      Set.mem_setOf_eq, Set.mem_iInter]
  rw [hev]
  exact MeasurableSet.iInter fun f => MeasurableSet.iInter fun i =>
    measurableSet_le (hmeas f i) measurable_const

/-- Finite-model uniform response concentration derived directly from raw iid
replicates.

Completing this theorem removes the abstract `Xbar`, per-index integrability,
per-index second-moment, and response-event hypotheses from the finite-model
Perfect Quench capstone.  The remaining rate condition is explicit in the
replicate count and tolerance.  The reference measurability argument is passed
separately here and is discharged by `IIDReferenceSampler.measurable` in the
final capstone.

Implementation recipe (execute in this order):
1. For fixed `n`, let `Bad f i := {ω | η n < ‖Xbar ω f i - μbar ω f i‖}` and
   show the complement of the desired event is contained in
   `⋃ f, ⋃ i, Bad f i`.
2. Apply the Chebyshev/second-moment inequality to each `Bad f i`, using
   `integrable_sq_augmentedRawSampleMean_sub_population`, the bound
   `integral_norm_sq_augmentedRawSampleMean_sub_population_le`, and `hη n`.
3. Apply finite subadditivity over the model and augmented-index `Finset.univ`s;
   simplify their cardinalities to
   `Fintype.card (Model Q X)` and `n+1`.
4. Bound the complement probability by the real ratio in `hratio`, converted to
   `ENNReal.ofReal` exactly as in
   `highProb_uniformTargetResponseMeanClose_of_secondMoment`.
5. Convert `hratio` to the `HighProbAtTop` statement using the local complement
   criterion from `GrowingResponse`; keep the desired event measurable via
   `measurableSet_augmentedRawResponseMeanEvent_finite`.
6. Reuse the existing finite-target theorem directly if its dependent types
   align; otherwise copy only its outer union-bound skeleton.
-/
theorem highProb_augmentedRawResponseMean_finite
    [Fintype (Model Q X)]
    {m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ωref => f_ref n ωref i)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance η : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (hη : ∀ n, 0 < η n)
    (hratio : Tendsto (fun n =>
      (Fintype.card (Model Q X) : Real) * ((n + 1 : Nat) : Real) *
        (variance n / replicates n) / (η n) ^ 2) atTop (𝓝 0)) :
    HighProbAtTop (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp Hraw.probability)
      (augmentedUniformResponseMeanEvent
        (augmentedRawSampleMean f_ref replicates Y)
        (augmentedRawPopulationMean f_ref μmodel) η) := by
  haveI : ∀ u, IsProbabilityMeasure (jointStageMeasure μref μresp u) :=
    jointStageMeasure_probability μref hμref μresp Hraw.probability
  exact highProb_uniformTargetResponseMeanClose_of_secondMoment
    (jointStageMeasure μref μresp) (fun n => n + 1)
    (augmentedRawSampleMean f_ref replicates Y)
    (augmentedRawPopulationMean f_ref μmodel)
    (fun n => variance n / replicates n) η
    (fun n f i => integrable_sq_augmentedRawSampleMean_sub_population
      μref hμref μresp f_ref href replicates Y μmodel variance Hraw n f i)
    (fun n f i => integral_norm_sq_augmentedRawSampleMean_sub_population_le
      μref hμref μresp f_ref href replicates Y μmodel variance Hraw n f i)
    hη hratio

/-- Finite-model measurable subevent certificate for raw response means.

This packages the preceding probability and measurability theorems in the exact
form consumed by the Perfect Quench spectral capstone.

Implementation recipe (execute in this order):
1. Refine `AugmentedResponseMeanSubevents` with
   `event := augmentedUniformResponseMeanEvent ... η`.
2. Fill `measurable` using
   `measurableSet_augmentedRawResponseMeanEvent_finite`.
3. Fill `highProb` using `highProb_augmentedRawResponseMean_finite`.
4. Fill `subset` with `Set.Subset.rfl`.
5. This definition must be a pure packaging step; if any field requires new
   probability work, the preceding theorem is incomplete.
-/
noncomputable def augmentedRawResponseMeanSubevents_finite
    [Fintype (Model Q X)]
    {m p : Nat}
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (href : ∀ n i, Measurable fun ω => f_ref n ω i)
    (replicates : Nat → Nat)
    (Y : ∀ n, Model Q X → Fin (replicates n) → Ωresp → Acharyya2024.Mat m p)
    (μmodel : Model Q X → Acharyya2024.Mat m p)
    (variance η : Nat → Real)
    (Hraw : RawIIDResponseModel μresp replicates Y μmodel variance)
    (hη : ∀ n, 0 < η n)
    (hratio : Tendsto (fun n =>
      (Fintype.card (Model Q X) : Real) * ((n + 1 : Nat) : Real) *
        (variance n / replicates n) / (η n) ^ 2) atTop (𝓝 0)) :
    AugmentedResponseMeanSubevents
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp Hraw.probability)
      (augmentedRawSampleMean f_ref replicates Y)
      (augmentedRawPopulationMean f_ref μmodel) η :=
  { event := augmentedUniformResponseMeanEvent
      (augmentedRawSampleMean f_ref replicates Y)
      (augmentedRawPopulationMean f_ref μmodel) η
    measurable := fun n =>
      measurableSet_augmentedRawResponseMeanEvent_finite μresp f_ref href replicates Y
        μmodel variance η Hraw n
    highProb := highProb_augmentedRawResponseMean_finite μref hμref μresp f_ref href
      replicates Y μmodel variance η Hraw hη hratio
    subset := fun _ => Set.Subset.rfl }

end DkpsQuench.Perfect
