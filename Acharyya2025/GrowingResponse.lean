/-
Stage-dependent response concentration for growing Acharyya2025 populations.

The fixed-population rate chain uses one type Fin n throughout.  The growing
Quench bridge instead forms a target-augmented population of size n+1 at stage
n.  This file generalizes the response-mean and CMDS-entrywise concentration
steps to a stage-dependent finite index type Fin (count u).

It also connects concrete replicate arrays to their sample means.  The raw
replicate theorem is stated for deterministic stage populations; random
reference populations can use the more general second-moment interface below,
which allows the population mean itself to depend on the sampling outcome.
-/

import Acharyya2024.SecondMoment
import Acharyya2025.RateChain

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

namespace Acharyya2025.GrowingResponse

open Acharyya2024
open Acharyya2024.SecondMoment
open Acharyya2025.Bridge
open Acharyya2025.Deterministic
open Acharyya2025.RateChain

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Universe-polymorphic complement-probability criterion used by the growing
response layer.  The fixed-population RateChain helper intentionally remains
at its original universe to avoid burdening its older theorem chain. -/
theorem highProbAtTop_of_tendsto_compl_zero
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]
    (E : Nat → Set Ω)
    (h : Tendsto (fun u => P u ((E u)ᶜ)) atTop (𝓝 0)) :
    HighProbAtTop P E := by
  intro δ hδ
  have hev : ∀ᶠ u in atTop, P u ((E u)ᶜ) < δ :=
    h.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun u hu => ?_⟩
  have hcompl : P u ((E u)ᶜ) ≤ δ := (hN u (le_of_lt hu)).le
  have h1 : (1 : ENNReal) - δ ≤ 1 - P u ((E u)ᶜ) :=
    tsub_le_tsub_left hcompl 1
  exact h1.trans (TauCeti.one_sub_measure_compl_le (P u) (E u))

/-- Average a finite family of response vectors.  The zero-replicate branch is
left at Lean's totalized scalar inverse; every statistical theorem below
requires a positive replicate count. -/
noncomputable def replicateMean {m p r : Nat}
    (Y : Fin r → Ω → Mat m p) (ω : Ω) : Mat m p :=
  (r : Real)⁻¹ • ∑ k, Y k ω

/-- Stage-indexed replicate average for a growing finite population. -/
noncomputable def growingReplicateMean
    {m p : Nat} (count replicates : Nat → Nat)
    (Y : ∀ u, Fin (count u) → Fin (replicates u) → Ω → Mat m p)
    (u : Nat) (ω : Ω) (i : Fin (count u)) : Mat m p :=
  replicateMean (Y u i) ω

/-- The standard iid second-moment estimate for the concrete replicate average.
This is a direct matrix-valued specialization of the Acharyya2024 sample-mean
identity because Mat m p is a finite Euclidean space. -/
theorem integral_norm_sq_replicateMean_sub_mean_le_of_bound
    {Ω0 : Type} [MeasurableSpace Ω0]
    (P : Measure Ω0) [IsProbabilityMeasure P]
    {m p r : Nat} (hr : 0 < r)
    (Y : Fin r → Ω0 → Mat m p) (μ : Mat m p)
    (hL2 : ∀ k, MemLp (Y k) 2 P)
    (hmean : ∀ k c, ∫ ω, Y k ω c ∂P = μ c)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (Y i) (Y j) P)
    {γ : Real}
    (hbound : ∀ k, ∫ ω, ‖Y k ω - μ‖ ^ 2 ∂P ≤ γ) :
    ∫ ω, ‖replicateMean Y ω - μ‖ ^ 2 ∂P ≤ γ / r := by
  simpa [replicateMean] using
    integral_norm_sq_sampleMean_sub_mean_le_of_bound
      P hr Y μ hL2 hmean hindep hbound

/-- A varying finite population satisfies uniform response-mean concentration
when every stage-indexed response mean lies within eta of its population mean. -/
def GrowingUniformResponseMeanClose
    {m p : Nat} (count : Nat → Nat)
    (Xbar μ : ∀ u, Ω → Fin (count u) → Mat m p)
    (η : Nat → Real) (u : Nat) : Set Ω :=
  {ω | UniformResponseMeanClose (Xbar u ω) (μ u ω) (η u)}

/--
**Finite Chebyshev-plus-union bound for the response means.**

For a fixed model count, the probability that every model's sample response mean is within `η`
of its population counterpart is at least `1 - N σ² / η²`.

The paper's Theorem 1 is a statement of exactly this shape -- an explicit finite lower bound on
a probability, in terms of the response variances -- whereas
`highProb_uniformResponseMeanClose_of_growing_secondMoment` below states the asymptotic
consequence.  The census records that no single declaration reproduced the displayed finite
bound; this supplies the probability step of it.  What remains between this and the printed
Theorem 1 is the passage from response means to entries of the doubly centred matrix, which is
where the source's factor `16` and its `1/(rm)` scaling arise.
-/
theorem prob_uniformResponseMeanClose_ge_of_secondMoment
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N m p : Nat}
    (Xbar μ : Ω → Fin N → Mat m p)
    (σ2 η : Real) (hη : 0 < η)
    (hint : ∀ i, Integrable (fun ω => ‖Xbar ω i - μ ω i‖ ^ 2) P)
    (hσ2 : ∀ i, ∫ ω, ‖Xbar ω i - μ ω i‖ ^ 2 ∂P ≤ σ2) :
    1 - ENNReal.ofReal ((N : Real) * σ2 / η ^ 2)
      ≤ P {ω | UniformResponseMeanClose (Xbar ω) (μ ω) η} := by
  have hcheb : ∀ i : Fin N,
      P {ω | η < ‖Xbar ω i - μ ω i‖} ≤ ENNReal.ofReal (σ2 / η ^ 2) := fun i =>
    TauCeti.meas_gt_le_ofReal_integral_sq_div_sq P (hint i) hη (hσ2 i)
  have hincl : {ω | UniformResponseMeanClose (Xbar ω) (μ ω) η}ᶜ
      ⊆ ⋃ i : Fin N, {ω | η < ‖Xbar ω i - μ ω i‖} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
    exact hω (fun i => hnot i)
  have hcompl : P ({ω | UniformResponseMeanClose (Xbar ω) (μ ω) η}ᶜ)
      ≤ ENNReal.ofReal ((N : Real) * σ2 / η ^ 2) := by
    calc P ({ω | UniformResponseMeanClose (Xbar ω) (μ ω) η}ᶜ)
        ≤ P (⋃ i : Fin N, {ω | η < ‖Xbar ω i - μ ω i‖}) := measure_mono hincl
      _ ≤ ∑ i : Fin N, P {ω | η < ‖Xbar ω i - μ ω i‖} :=
          measure_iUnion_fintype_le (μ := P) (fun i => {ω | η < ‖Xbar ω i - μ ω i‖})
      _ ≤ ∑ _i : Fin N, ENNReal.ofReal (σ2 / η ^ 2) := Finset.sum_le_sum fun i _ => hcheb i
      _ = (N : ENNReal) * ENNReal.ofReal (σ2 / η ^ 2) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ENNReal.ofReal ((N : Real) * (σ2 / η ^ 2)) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal ((N : Real) * σ2 / η ^ 2) := by rw [mul_div_assoc]
  rw [tsub_le_iff_right]
  calc (1 : ENNReal) = P Set.univ := by simp
    _ ≤ P {ω | UniformResponseMeanClose (Xbar ω) (μ ω) η}
        + P ({ω | UniformResponseMeanClose (Xbar ω) (μ ω) η}ᶜ) := by
        simpa using measure_union_le (μ := P)
          {ω | UniformResponseMeanClose (Xbar ω) (μ ω) η}
          ({ω | UniformResponseMeanClose (Xbar ω) (μ ω) η}ᶜ)
    _ ≤ P {ω | UniformResponseMeanClose (Xbar ω) (μ ω) η}
        + ENNReal.ofReal ((N : Real) * σ2 / η ^ 2) := by gcongr

/-- Stage-dependent Chebyshev plus union bound.  The number of models may vary
with the asymptotic stage, and the population means may depend on the same
outcome as the sample means.  Only the integrated squared errors enter the
proof. -/
theorem highProb_uniformResponseMeanClose_of_growing_secondMoment
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]
    {m p : Nat} (count : Nat → Nat)
    (Xbar μ : ∀ u, Ω → Fin (count u) → Mat m p)
    (σ2 η : Nat → Real)
    (hint : ∀ u (i : Fin (count u)),
      Integrable (fun ω => ‖Xbar u ω i - μ u ω i‖ ^ 2) (P u))
    (hσ2 : ∀ u (i : Fin (count u)),
      ∫ ω, ‖Xbar u ω i - μ u ω i‖ ^ 2 ∂(P u) ≤ σ2 u)
    (hη_pos : ∀ u, 0 < η u)
    (hratio : Tendsto
      (fun u => (count u : Real) * σ2 u / (η u) ^ 2)
      atTop (𝓝 0)) :
    HighProbAtTop P
      (GrowingUniformResponseMeanClose count Xbar μ η) := by
  apply highProbAtTop_of_tendsto_compl_zero
  have hbound : ∀ u,
      P u ((GrowingUniformResponseMeanClose count Xbar μ η u)ᶜ)
        ≤ ENNReal.ofReal
          ((count u : Real) * σ2 u / (η u) ^ 2) := by
    intro u
    have hincl :
        (GrowingUniformResponseMeanClose count Xbar μ η u)ᶜ
          ⊆ ⋃ i : Fin (count u),
            {ω | η u < ‖Xbar u ω i - μ u ω i‖} := by
      intro ω hω
      by_contra hnot
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
      exact hω (fun i => hnot i)
    have hcheb : ∀ i : Fin (count u),
        P u {ω | η u < ‖Xbar u ω i - μ u ω i‖}
          ≤ ENNReal.ofReal (σ2 u / (η u) ^ 2) := fun i =>
      TauCeti.meas_gt_le_ofReal_integral_sq_div_sq
        (P u) (hint u i) (hη_pos u) (hσ2 u i)
    calc
      P u ((GrowingUniformResponseMeanClose count Xbar μ η u)ᶜ)
          ≤ P u (⋃ i : Fin (count u),
              {ω | η u < ‖Xbar u ω i - μ u ω i‖}) :=
            measure_mono hincl
      _ ≤ ∑ i : Fin (count u),
          P u {ω | η u < ‖Xbar u ω i - μ u ω i‖} :=
            measure_iUnion_fintype_le (μ := P u)
              (fun i => {ω | η u < ‖Xbar u ω i - μ u ω i‖})
      _ ≤ ∑ _i : Fin (count u),
          ENNReal.ofReal (σ2 u / (η u) ^ 2) :=
            Finset.sum_le_sum fun i _ => hcheb i
      _ = (count u : ENNReal) *
          ENNReal.ofReal (σ2 u / (η u) ^ 2) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ENNReal.ofReal
          ((count u : Real) * (σ2 u / (η u) ^ 2)) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg (count u)),
              ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal
          ((count u : Real) * σ2 u / (η u) ^ 2) := by
            rw [mul_div_assoc]
  have hub : Tendsto
      (fun u => ENNReal.ofReal
        ((count u : Real) * σ2 u / (η u) ^ 2))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hratio
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hub (fun _ => zero_le) hbound

/-- Concrete iid-replicate corollary for a growing deterministic population.
The per-replicate second moment gamma u becomes gamma u / replicates u for the
sample mean, and the remaining asymptotic condition is the corresponding
stage-size union-bound ratio. -/
theorem highProb_uniformResponseMeanClose_of_growing_iid_replicates
    {Ω0 : Type} [MeasurableSpace Ω0]
    (P : Nat → Measure Ω0) [∀ u, IsProbabilityMeasure (P u)]
    {m p : Nat} (count replicates : Nat → Nat)
    (hrep : ∀ u, 0 < replicates u)
    (Y : ∀ u, Fin (count u) → Fin (replicates u) → Ω0 → Mat m p)
    (μ : ∀ u, Fin (count u) → Mat m p)
    (hL2 : ∀ u i k, MemLp (Y u i k) 2 (P u))
    (hmean : ∀ u i k c, ∫ ω, Y u i k ω c ∂(P u) = μ u i c)
    (hindep : ∀ u i,
      Set.Pairwise (Set.univ : Set (Fin (replicates u)))
        fun k l => IndepFun (Y u i k) (Y u i l) (P u))
    (γ η : Nat → Real)
    (hbound : ∀ u i k,
      ∫ ω, ‖Y u i k ω - μ u i‖ ^ 2 ∂(P u) ≤ γ u)
    (hsample_int : ∀ u i, Integrable
      (fun ω => ‖growingReplicateMean count replicates Y u ω i - μ u i‖ ^ 2)
      (P u))
    (hη_pos : ∀ u, 0 < η u)
    (hratio : Tendsto
      (fun u => (count u : Real) * (γ u / replicates u) / (η u) ^ 2)
      atTop (𝓝 0)) :
    HighProbAtTop P
      (fun u => {ω | UniformResponseMeanClose
        (growingReplicateMean count replicates Y u ω) (μ u) (η u)}) := by
  let μrandom : ∀ u, Ω0 → Fin (count u) → Mat m p :=
    fun u _ => μ u
  apply highProb_uniformResponseMeanClose_of_growing_secondMoment
    P count (growingReplicateMean count replicates Y) μrandom
    (fun u => γ u / replicates u) η
  · intro u i
    simpa [growingReplicateMean, μrandom] using hsample_int u i
  · intro u i
    simpa [growingReplicateMean, μrandom] using
      integral_norm_sq_replicateMean_sub_mean_le_of_bound
        (P u) (hrep u) (Y u i) (μ u i)
        (hL2 u i) (hmean u i) (hindep u i) (hbound u i)
  · exact hη_pos
  · simpa using hratio

/-! ### Paper-scale response tolerance bookkeeping -/

/-- Response-mean tolerance associated with a desired operator-scale error `x`.
The direct entrywise response bridge contributes one later factor of the
population size when entrywise matrix error is converted to operator norm, so
choosing `η = x / n` cancels that factor. -/
noncomputable def paperResponseTolerance (n : Nat) (x : Real) : Real :=
  x / (n : Real)

/-- With positive population size, the batch-scaled direct CMDS rate at
`paperResponseTolerance n x` is a fixed constant times `x`, independent of `n`. -/
theorem scaled_cmdsEntrywiseRate_paperResponseTolerance
    (n m : Nat) (hn : 0 < n) (R x : Real) :
    (n : Real) * cmdsEntrywiseRate n m R (paperResponseTolerance n x) =
      16 * R * (m : Real)⁻¹ * x := by
  have hn' : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [cmdsEntrywiseRate, responseEntrywiseRate, paperResponseTolerance,
    div_eq_mul_inv]
  calc
    (n : Real) * (4 * ((2 * R) * ((m : Real)⁻¹ * (2 * (x * (n : Real)⁻¹)))))
        = (16 * R * (m : Real)⁻¹ * x) * ((n : Real) * (n : Real)⁻¹) := by ring
    _ = 16 * R * (m : Real)⁻¹ * x := by
      rw [mul_inv_cancel₀ hn']
      ring

/-- For an already-averaged response with second-moment bound `σ²`, the
Chebyshev/union-bound ratio at `η = x/n` is exactly `n³ σ² / x²`. -/
theorem secondMoment_ratio_paperResponseTolerance
    (n : Nat) (hn : 0 < n) (x σ2 : Real) (hx : x ≠ 0) :
    (n : Real) * σ2 / (paperResponseTolerance n x) ^ 2 =
      (n : Real) ^ 3 * σ2 / x ^ 2 := by
  have hn' : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [paperResponseTolerance]
  field_simp [hn', hx]

/-- The Chebyshev/union-bound ratio at the paper-scaled response tolerance has
the exact `n^3 / r` structure.  Here `r` is the replicate count and `γ` bounds
the per-replicate second moment. -/
theorem concentration_ratio_paperResponseTolerance
    (n r : Nat) (hn : 0 < n) (x γ : Real) (hx : x ≠ 0) :
    (n : Real) * (γ / r) / (paperResponseTolerance n x) ^ 2 =
      ((n : Real) ^ 3 * γ) / r / x ^ 2 := by
  calc
    (n : Real) * (γ / r) / (paperResponseTolerance n x) ^ 2
        = (n : Real) ^ 3 * (γ / r) / x ^ 2 :=
          secondMoment_ratio_paperResponseTolerance n hn x (γ / r) hx
    _ = ((n : Real) ^ 3 * γ) / r / x ^ 2 := by ring

/-- Growing version of the preceding identity.  It isolates the exact base
quantity behind Acharyya's `n^3/r` concentration statement without committing
to a particular real-power parametrization of `x`. -/
theorem concentration_ratio_paperResponseTolerance_growing
    (count replicates : Nat → Nat)
    (hcount : ∀ u, 0 < count u)
    (x γ : Nat → Real) (hx : ∀ u, x u ≠ 0) :
    (fun u => (count u : Real) * (γ u / replicates u) /
        (paperResponseTolerance (count u) (x u)) ^ 2) =
      (fun u => ((count u : Real) ^ 3 * γ u) / replicates u / (x u) ^ 2) := by
  funext u
  exact concentration_ratio_paperResponseTolerance
    (count u) (replicates u) (hcount u) (x u) (γ u) (hx u)

/-- Growing Chebyshev concentration at a paper-scale operator target `x`.
After the direct pairwise response bridge, the natural response tolerance is
`x/count`; the only probabilistic ratio left is `count³ σ² / x²`. -/
theorem highProb_uniformResponseMeanClose_of_growing_secondMoment_paperScale
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]
    {m p : Nat} (count : Nat → Nat) (hcount : ∀ u, 0 < count u)
    (Xbar μ : ∀ u, Ω → Fin (count u) → Mat m p)
    (σ2 x : Nat → Real)
    (hint : ∀ u (i : Fin (count u)),
      Integrable (fun ω => ‖Xbar u ω i - μ u ω i‖ ^ 2) (P u))
    (hσ2 : ∀ u (i : Fin (count u)),
      ∫ ω, ‖Xbar u ω i - μ u ω i‖ ^ 2 ∂(P u) ≤ σ2 u)
    (hx_pos : ∀ u, 0 < x u)
    (hratio : Tendsto
      (fun u => (count u : Real) ^ 3 * σ2 u / (x u) ^ 2)
      atTop (𝓝 0)) :
    HighProbAtTop P
      (GrowingUniformResponseMeanClose count Xbar μ
        (fun u => paperResponseTolerance (count u) (x u))) := by
  apply highProb_uniformResponseMeanClose_of_growing_secondMoment
    P count Xbar μ σ2 (fun u => paperResponseTolerance (count u) (x u))
  · exact hint
  · exact hσ2
  · intro u
    have hcount' : (0 : Real) < count u := by exact_mod_cast hcount u
    exact div_pos (hx_pos u) hcount'
  · have heq :
        (fun u => (count u : Real) * σ2 u /
          (paperResponseTolerance (count u) (x u)) ^ 2) =
        (fun u => (count u : Real) ^ 3 * σ2 u / (x u) ^ 2) := by
      funext u
      exact secondMoment_ratio_paperResponseTolerance
        (count u) (hcount u) (x u) (σ2 u) (ne_of_gt (hx_pos u))
    rw [heq]
    exact hratio

/-- Concrete iid-replicate form of the paper-scale concentration theorem.
The hypothesis is the exact joint ratio produced by Chebyshev plus the model
union bound after choosing response tolerance `x/count`:
`count^3 * gamma / replicates / x^2 -> 0`. -/
theorem highProb_uniformResponseMeanClose_of_growing_iid_replicates_paperScale
    {Ω0 : Type} [MeasurableSpace Ω0]
    (P : Nat → Measure Ω0) [∀ u, IsProbabilityMeasure (P u)]
    {m p : Nat} (count replicates : Nat → Nat)
    (hcount : ∀ u, 0 < count u)
    (hrep : ∀ u, 0 < replicates u)
    (Y : ∀ u, Fin (count u) → Fin (replicates u) → Ω0 → Mat m p)
    (μ : ∀ u, Fin (count u) → Mat m p)
    (hL2 : ∀ u i k, MemLp (Y u i k) 2 (P u))
    (hmean : ∀ u i k c, ∫ ω, Y u i k ω c ∂(P u) = μ u i c)
    (hindep : ∀ u i,
      Set.Pairwise (Set.univ : Set (Fin (replicates u)))
        fun k l => IndepFun (Y u i k) (Y u i l) (P u))
    (γ x : Nat → Real)
    (hbound : ∀ u i k,
      ∫ ω, ‖Y u i k ω - μ u i‖ ^ 2 ∂(P u) ≤ γ u)
    (hsample_int : ∀ u i, Integrable
      (fun ω => ‖growingReplicateMean count replicates Y u ω i - μ u i‖ ^ 2)
      (P u))
    (hx_pos : ∀ u, 0 < x u)
    (hratio : Tendsto
      (fun u => ((count u : Real) ^ 3 * γ u) / replicates u / (x u) ^ 2)
      atTop (𝓝 0)) :
    HighProbAtTop P
      (fun u => {ω | UniformResponseMeanClose
        (growingReplicateMean count replicates Y u ω) (μ u)
        (paperResponseTolerance (count u) (x u))}) := by
  apply highProb_uniformResponseMeanClose_of_growing_iid_replicates
    P count replicates hrep Y μ hL2 hmean hindep γ
    (fun u => paperResponseTolerance (count u) (x u)) hbound hsample_int
  · intro u
    have hcount' : (0 : Real) < count u := by exact_mod_cast hcount u
    exact div_pos (hx_pos u) hcount'
  · have heq := concentration_ratio_paperResponseTolerance_growing
      count replicates hcount x γ (fun u => ne_of_gt (hx_pos u))
    rw [heq]
    exact hratio

/-- A uniform response-matrix norm bound yields a uniform dissimilarity
bound.  This packages the elementary triangle inequality used to discharge the
bounded-dissimilarity side condition of the CMDS bridge. -/
noncomputable def responseDistBound (m : Nat) (B : Real) : Real :=
  (m : Real)⁻¹ * (2 * B)

theorem abs_responseDist_le_of_norm_le
    {n m p : Nat} (X : Fin n → Mat m p) {B : Real}
    (hX : ∀ i, ‖X i‖ ≤ B) (i j : Fin n) :
    |responseDist X i j| ≤ responseDistBound m B := by
  have hm : 0 ≤ (m : Real)⁻¹ := inv_nonneg.mpr (by positivity)
  have hdist : 0 ≤ responseDist X i j := by
    exact mul_nonneg hm (norm_nonneg _)
  rw [abs_of_nonneg hdist]
  calc
    responseDist X i j
        = (m : Real)⁻¹ * ‖X i - X j‖ := rfl
    _ ≤ (m : Real)⁻¹ * (‖X i‖ + ‖X j‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hm
    _ ≤ (m : Real)⁻¹ * (B + B) :=
      mul_le_mul_of_nonneg_left (add_le_add (hX i) (hX j)) hm
    _ = responseDistBound m B := by
      simp [responseDistBound, two_mul]

/-- Response-mean closeness at one growing stage propagates to entrywise
closeness of the associated classical-MDS matrices. -/
theorem cmdsEntrywise_of_responseMeanClose
    {n m p : Nat} (hn : 0 < n)
    (Xbar μ : Fin n → Mat m p) {η R : Real}
    (hmean : UniformResponseMeanClose Xbar μ η)
    (hsample : ∀ i j, |responseDist Xbar i j| ≤ R)
    (hpopulation : ∀ i j, |responseDist μ i j| ≤ R) :
    EntrywiseClose
      (classicalMDSMatrix (responseDist Xbar))
      (classicalMDSMatrix (responseDist μ))
      (cmdsEntrywiseRate n m R η) := by
  have hentry := response_mean_close_event_to_entrywise_event Xbar μ hmean
  simpa [cmdsEntrywiseRate] using
    entrywise_close_to_cmds_entrywise_close_of_bounded
      hn hentry hsample hpopulation

/-- Norm-bounded form of the response-mean to CMDS-entrywise bridge. -/
theorem cmdsEntrywise_of_responseMeanClose_of_norm_le
    {n m p : Nat} (hn : 0 < n)
    (Xbar μ : Fin n → Mat m p) {η B : Real}
    (hmean : UniformResponseMeanClose Xbar μ η)
    (hXbar : ∀ i, ‖Xbar i‖ ≤ B)
    (hμ : ∀ i, ‖μ i‖ ≤ B) :
    EntrywiseClose
      (classicalMDSMatrix (responseDist Xbar))
      (classicalMDSMatrix (responseDist μ))
      (cmdsEntrywiseRate n m (responseDistBound m B) η) := by
  exact cmdsEntrywise_of_responseMeanClose hn Xbar μ hmean
    (abs_responseDist_le_of_norm_le Xbar hXbar)
    (abs_responseDist_le_of_norm_le μ hμ)

/-- Uniform response-mean closeness and a population norm bound control the
sample-response norm on the same event.  This avoids asking downstream callers
for a separate global bound on every random sample response. -/
theorem norm_le_add_of_uniformResponseMeanClose
    {n m p : Nat} {Xbar μ : Fin n → Mat m p} {η B : Real}
    (hmean : UniformResponseMeanClose Xbar μ η)
    (hμ : ∀ i, ‖μ i‖ ≤ B) (i : Fin n) :
    ‖Xbar i‖ ≤ B + η := by
  calc
    ‖Xbar i‖ = ‖(Xbar i - μ i) + μ i‖ := by rw [sub_add_cancel]
    _ ≤ ‖Xbar i - μ i‖ + ‖μ i‖ := norm_add_le _ _
    _ ≤ η + B := add_le_add (hmean i) (hμ i)
    _ = B + η := add_comm _ _

/-- Population response norms and the response-mean event are enough to derive
both sample and population dissimilarity bounds needed by the CMDS bridge.
The resulting bound is event-local, so no all-outcomes sample norm hypothesis is
required. -/
theorem cmdsEntrywise_of_responseMeanClose_of_population_norm
    {n m p : Nat} (hn : 0 < n)
    (Xbar μ : Fin n → Mat m p) {η B : Real}
    (hη : 0 ≤ η)
    (hmean : UniformResponseMeanClose Xbar μ η)
    (hμ : ∀ i, ‖μ i‖ ≤ B) :
    EntrywiseClose
      (classicalMDSMatrix (responseDist Xbar))
      (classicalMDSMatrix (responseDist μ))
      (cmdsEntrywiseRate n m (responseDistBound m (B + η)) η) := by
  apply cmdsEntrywise_of_responseMeanClose_of_norm_le hn Xbar μ hmean
  · exact fun i => norm_le_add_of_uniformResponseMeanClose hmean hμ i
  · exact fun i => (hμ i).trans (le_add_of_nonneg_right hη)

/-- High-probability stage-dependent response-mean concentration propagates to
stage-dependent CMDS-entrywise concentration. -/
theorem highProb_cmdsEntrywise_of_growing_response_mean
    (P : Nat → Measure Ω)
    {m p : Nat} (count : Nat → Nat) (hcount : ∀ u, 0 < count u)
    (Xbar μ : ∀ u, Ω → Fin (count u) → Mat m p)
    (η R : Nat → Real)
    (hmean : HighProbAtTop P
      (GrowingUniformResponseMeanClose count Xbar μ η))
    (hsample : ∀ u ω i j, |responseDist (Xbar u ω) i j| ≤ R u)
    (hpopulation : ∀ u ω i j, |responseDist (μ u ω) i j| ≤ R u) :
    HighProbAtTop P (fun u => {ω |
      EntrywiseClose
        (classicalMDSMatrix (responseDist (Xbar u ω)))
        (classicalMDSMatrix (responseDist (μ u ω)))
        (cmdsEntrywiseRate (count u) m (R u) (η u))}) := by
  exact HighProbAtTop.mono hmean fun u ω hω =>
    cmdsEntrywise_of_responseMeanClose (hcount u)
      (Xbar u ω) (μ u ω) hω
      (hsample u ω) (hpopulation u ω)

/-- Measurability of a finite-target uniform response-mean event. -/
theorem measurableSet_uniformTargetResponseMeanClose
    {T : Type*} [Fintype T]
    {n m p : Nat}
    (Xbar μ : Ω → T → Fin n → Mat m p)
    (η : Real)
    (hX : ∀ t i, Measurable fun ω => Xbar ω t i)
    (hμ : ∀ t i, Measurable fun ω => μ ω t i) :
    MeasurableSet {ω | ∀ t i,
      ‖Xbar ω t i - μ ω t i‖ ≤ η} := by
  classical
  have heq : {ω | ∀ t i, ‖Xbar ω t i - μ ω t i‖ ≤ η} =
      ⋂ t : T, ⋂ i : Fin n,
        {ω | ‖Xbar ω t i - μ ω t i‖ ≤ η} := by
    ext ω
    simp
  rw [heq]
  refine MeasurableSet.iInter fun t => MeasurableSet.iInter fun i => ?_
  exact ((hX t i).sub (hμ t i)).norm measurableSet_Iic

/-- Finite-target version of the growing union bound.  This is the fully
uniform theorem needed when the target class itself is finite. -/
theorem highProb_uniformTargetResponseMeanClose_of_secondMoment
    {T : Type*} [Fintype T]
    (P : Nat → Measure Ω) [∀ u, IsProbabilityMeasure (P u)]
    {m p : Nat} (count : Nat → Nat)
    (Xbar μ : ∀ u, Ω → T → Fin (count u) → Mat m p)
    (σ2 η : Nat → Real)
    (hint : ∀ u t (i : Fin (count u)),
      Integrable (fun ω => ‖Xbar u ω t i - μ u ω t i‖ ^ 2) (P u))
    (hσ2 : ∀ u t (i : Fin (count u)),
      ∫ ω, ‖Xbar u ω t i - μ u ω t i‖ ^ 2 ∂(P u) ≤ σ2 u)
    (hη_pos : ∀ u, 0 < η u)
    (hratio : Tendsto
      (fun u => (Fintype.card T : Real) * (count u : Real) *
        σ2 u / (η u) ^ 2)
      atTop (𝓝 0)) :
    HighProbAtTop P (fun u => {ω | ∀ t i,
      ‖Xbar u ω t i - μ u ω t i‖ ≤ η u}) := by
  apply highProbAtTop_of_tendsto_compl_zero
  have hbound : ∀ u,
      P u ({ω | ∀ t i,
        ‖Xbar u ω t i - μ u ω t i‖ ≤ η u}ᶜ)
        ≤ ENNReal.ofReal
          ((Fintype.card T : Real) * (count u : Real) *
            σ2 u / (η u) ^ 2) := by
    intro u
    have hincl :
        {ω | ∀ t i, ‖Xbar u ω t i - μ u ω t i‖ ≤ η u}ᶜ
          ⊆ ⋃ t : T, ⋃ i : Fin (count u),
            {ω | η u < ‖Xbar u ω t i - μ u ω t i‖} := by
      intro ω hω
      by_contra hnot
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
      exact hω (fun t i => hnot t i)
    have hcheb : ∀ t (i : Fin (count u)),
        P u {ω | η u < ‖Xbar u ω t i - μ u ω t i‖}
          ≤ ENNReal.ofReal (σ2 u / (η u) ^ 2) := fun t i =>
      TauCeti.meas_gt_le_ofReal_integral_sq_div_sq
        (P u) (hint u t i) (hη_pos u) (hσ2 u t i)
    calc
      P u ({ω | ∀ t i,
          ‖Xbar u ω t i - μ u ω t i‖ ≤ η u}ᶜ)
          ≤ P u (⋃ t : T, ⋃ i : Fin (count u),
              {ω | η u < ‖Xbar u ω t i - μ u ω t i‖}) :=
            measure_mono hincl
      _ ≤ ∑ t : T, P u (⋃ i : Fin (count u),
              {ω | η u < ‖Xbar u ω t i - μ u ω t i‖}) :=
            measure_iUnion_fintype_le (μ := P u) _
      _ ≤ ∑ t : T, ∑ i : Fin (count u),
              P u {ω | η u < ‖Xbar u ω t i - μ u ω t i‖} := by
            exact Finset.sum_le_sum fun t _ =>
              measure_iUnion_fintype_le (μ := P u) _
      _ ≤ ∑ _t : T, ∑ _i : Fin (count u),
              ENNReal.ofReal (σ2 u / (η u) ^ 2) :=
            Finset.sum_le_sum fun t _ =>
              Finset.sum_le_sum fun i _ => hcheb t i
      _ = (Fintype.card T : ENNReal) *
          ((count u : ENNReal) *
            ENNReal.ofReal (σ2 u / (η u) ^ 2)) := by
            simp [Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
      _ = (Fintype.card T : ENNReal) *
          ENNReal.ofReal
            ((count u : Real) * (σ2 u / (η u) ^ 2)) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg (count u)),
              ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal
          ((Fintype.card T : Real) * ((count u : Real) *
            (σ2 u / (η u) ^ 2))) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card T)),
              ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal
          ((Fintype.card T : Real) * (count u : Real) *
            σ2 u / (η u) ^ 2) := by
            congr 1
            ring
  have hub : Tendsto
      (fun u => ENNReal.ofReal
        ((Fintype.card T : Real) * (count u : Real) *
          σ2 u / (η u) ^ 2))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hratio
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hub (fun _ => zero_le) hbound

end Acharyya2025.GrowingResponse
