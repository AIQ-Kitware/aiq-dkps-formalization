/-
Probability step for the fixed-model / growing-query regime of

Acharyya, Trosset, Priebe, Helm.
"Consistent estimation of generative model representations in the data kernel
perspective space"
arXiv:2409.17308, Theorem 2 and Appendix A.2.

This file proves the TRUE, paper-faithful probabilistic step that
`Acharyya2024.Consistency.growing_queries_dissimilarity_converges` only sketches
(that theorem is stated without hypotheses and is false as written). Here we make
the second-moment hypothesis explicit: if the per-model mean-squared response
errors `E‖Xbar(r) i − μ i‖²` are bounded by `v r → 0`, then the Frobenius
distance between the empirical and population response-dissimilarity matrices
converges to zero in probability.

The proof chains:
  * a Chebyshev/Markov inequality (`meas_gt_le_ofReal_secondMoment_div_sq`),
  * a finite union bound over the `Fin n` models, and
  * the deterministic Appendix A.2 reduction
    `frobSub_responseDist_le_of_uniform_errors` from `Acharyya2024.Common`.
-/

import Acharyya2024.Common
import Acharyya2024.SecondMoment
import ForTauCeti.Probability.Moments.Variance
import ForTauCeti.Probability.ProductConvergence

open scoped BigOperators Topology ProbabilityTheory
open Filter MeasureTheory

namespace Acharyya2024.Probability

open Acharyya2024

variable {Ω : Type} [MeasurableSpace Ω]

/--
Chebyshev/Markov inequality in second-moment form, packaged for `ENNReal`.

For a nonnegative measurable function `Y` with `∫ Y² ≤ v` and `0 < η`,
the probability of `{ω | η < Y ω}` is at most `ENNReal.ofReal (v / η²)`.

Thin wrapper around the Mathlib-staged
`TauCeti.meas_gt_le_ofReal_integral_sq_div_sq`; kept under its original
name for downstream call-sites.

Internal tooling: this is the standard Chebyshev/Markov second-moment bound (it
is the inequality applied to each model in the proof of Theorem 2); it is not a
separately numbered statement in the paper.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem meas_gt_le_ofReal_secondMoment_div_sq
    (P : Measure Ω) [IsProbabilityMeasure P]   -- probability measure (total mass 1)
    {Y : Ω → Real}
    (hY_int : Integrable (fun ω => (Y ω) ^ 2) P)  -- finite second moment ∫ Y² < ∞
    {v η : Real} (hη : 0 < η)                      -- positive threshold η
    (hmoment : ∫ ω, (Y ω) ^ 2 ∂P ≤ v) :            -- second moment bounded by v
    -- Conclusion: the tail probability P(Y > η) is at most v/η² (Chebyshev/Markov).
    P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2) :=
  TauCeti.meas_gt_le_ofReal_integral_sq_div_sq P hY_int hη hmoment

/--
Main probabilistic theorem (paper Theorem 2 / Appendix A.2).

Let `Xbar r ω : Fin n → Mat m p` be sample-average response matrices and
`μ : Fin n → Mat m p` the population means. If each per-model mean-squared error
`∫ ‖Xbar r ω i − μ i‖² ∂P` is bounded by `v r` with `v r → 0`, then the Frobenius
distance between the empirical and population response-dissimilarity matrices
converges to `0` in probability.

The second-moment bound `hmoment`, together with integrability of the squared
errors, is the only probabilistic hypothesis; in the paper it is established by the iid variance/trace computation `v r = (1/r)·Σγ`.
We take it as a hypothesis to separate the concentration step from the variance
algebra.

PAPER CORRESPONDENCE: this is the concentration conclusion of Theorem 2 (the
`‖D − ∆⁽∞⁾‖_F →P 0` statement). The hypothesis `hmoment` with `hv : v r → 0`
encodes the paper's condition `(1/m) Σⱼ γ_ij / r → 0`; the variance/trace
identity that produces `v r = γ_ij/r` is supplied separately in
`SecondMoment.lean`. The matrices `Xbar r` correspond to the sample-average
response matrices `X̄_i`, `μ` to the population means, and `v` to the per-model
mean-squared-error rate.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem dissimilarity_convergesInProbability_of_secondMoment
    (P : Measure Ω) [IsProbabilityMeasure P]   -- probability measure (total mass 1)
    {n m p : Nat}                               -- n models, response matrices of size m×p
    (Xbar : Nat → Ω → Fin n → Mat m p)          -- empirical sample-mean responses X̄_i (indexed by sample size r)
    (μ : Fin n → Mat m p)                        -- population mean responses μ_i
    (v : Nat → Real)                                    -- per-model mean-squared-error rate (paper: γ_ij/r)
    (hint : ∀ r i, Integrable (fun ω => ‖Xbar r ω i - μ i‖ ^ 2) P)  -- finite second moment per model
    -- core hypotheses (the paper's γ condition):
    (hmoment : ∀ r i, ∫ ω, ‖Xbar r ω i - μ i‖ ^ 2 ∂P ≤ v r)  -- mean-squared error bounded by v r
    (hv : Tendsto v atTop (𝓝 0)) :                            -- v r → 0 as r → ∞ (paper's γ/r → 0)
    -- Conclusion: the Frobenius distance between the empirical and population
    -- response-dissimilarity matrices converges to 0 in probability (Theorem 2's ‖D − ∆‖_F →P 0).
    ConvergesInProbabilityZero P
      (fun r ω => frobSub (responseDist (Xbar r ω)) (responseDist μ)) := by
  intro ε hε
  -- Reduce the metric goal to a measure-of-bad-set statement.
  -- dist (frobSub ...) 0 = |frobSub ... - 0| = frobSub ... (it is a sqrt, ≥ 0).
  have hfrob_nonneg : ∀ r ω,
      0 ≤ frobSub (responseDist (Xbar r ω)) (responseDist μ) := by
    intro r ω; exact Real.sqrt_nonneg _
  -- Rewrite the bad set into the clean `{ε < frobSub}` form.
  have hset_eq : ∀ r,
      {ω | dist (frobSub (responseDist (Xbar r ω)) (responseDist μ)) (0 : Real) > ε}
        = {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)} := by
    intro r
    ext ω
    simp only [Set.mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs, gt_iff_lt,
      abs_of_nonneg (hfrob_nonneg r ω)]
  -- Degenerate case n = 0: frobSub is sqrt of an empty sum = 0 < ε, bad set empty.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hzero : ∀ r ω, frobSub (responseDist (Xbar r ω)) (responseDist μ) = 0 := by
      intro r ω
      simp [frobSub, frob, frobSq]
    have : ∀ r,
        {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)} = (∅ : Set Ω) := by
      intro r; ext ω
      simp only [hzero r ω, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hε.le
    simp only [hset_eq, this]
    simp only [measure_empty]
    exact tendsto_const_nhds
  -- Degenerate case m = 0: (m:ℝ)⁻¹ = 0, so both dissimilarity matrices are 0.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hzero : ∀ r ω, frobSub (responseDist (Xbar r ω)) (responseDist μ) = 0 := by
      intro r ω
      simp [frobSub, frob, frobSq, responseDist, responseDistEntry]
    have : ∀ r,
        {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)} = (∅ : Set Ω) := by
      intro r; ext ω
      simp only [hzero r ω, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hε.le
    simp only [hset_eq, this]
    simp only [measure_empty]
    exact tendsto_const_nhds
  -- Main (nondegenerate) case.
  -- Per-model threshold: if ‖Xbar r ω i − μ i‖ ≤ η for all i then frobSub ≤ ε.
  set η : Real := ε * (m : Real) / (2 * (n : Real) * (n : Real)) with hη_def
  have hn_pos : (0 : Real) < (n : Real) := by exact_mod_cast hnpos
  have hm_pos : (0 : Real) < (m : Real) := by exact_mod_cast hmpos
  have hη_pos : 0 < η := by
    rw [hη_def]; positivity
  -- The deterministic reduction: uniform error η gives frobSub ≤ ε.
  have hdet : ∀ r ω,
      (∀ i : Fin n, ‖Xbar r ω i - μ i‖ ≤ η) →
        frobSub (responseDist (Xbar r ω)) (responseDist μ) ≤ ε := by
    intro r ω hbound
    have hle := frobSub_responseDist_le_of_uniform_errors (Xbar r ω) μ hbound
    refine hle.trans ?_
    have hval : ((n : Real) * (n : Real)) * (((m : Real))⁻¹ * (2 * η)) = ε := by
      rw [hη_def]
      field_simp
    exact hval.le
  -- Chebyshev for each per-model error.
  have hcheb : ∀ (r : Nat) (i : Fin n),
      P {ω | η < ‖Xbar r ω i - μ i‖} ≤ ENNReal.ofReal (v r / η ^ 2) := by
    intro r i
    exact meas_gt_le_ofReal_secondMoment_div_sq P
      (hint r i) hη_pos (hmoment r i)
  -- The bad event is contained in the union of per-model bad events.
  have hincl : ∀ r : Nat,
      {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)}
        ⊆ ⋃ i : Fin n, {ω | η < ‖Xbar r ω i - μ i‖} := by
    intro r ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
    exact absurd (hdet r ω hnot) (not_le.mpr hω)
  -- Union bound.
  have hbad : ∀ r : Nat,
      P {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)}
        ≤ (n : ENNReal) * ENNReal.ofReal (v r / η ^ 2) := by
    intro r
    calc
      P {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)}
          ≤ P (⋃ i : Fin n, {ω | η < ‖Xbar r ω i - μ i‖}) :=
            measure_mono (hincl r)
      _ ≤ ∑ i : Fin n, P {ω | η < ‖Xbar r ω i - μ i‖} :=
            measure_iUnion_fintype_le (μ := P)
              (fun i => {ω | η < ‖Xbar r ω i - μ i‖})
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (v r / η ^ 2) :=
            Finset.sum_le_sum fun i _ => hcheb r i
      _ = (n : ENNReal) * ENNReal.ofReal (v r / η ^ 2) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- The upper bound tends to zero.
  have hub : Tendsto (fun r => (n : ENNReal) * ENNReal.ofReal (v r / η ^ 2))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun r => v r / η ^ 2) atTop (𝓝 0) := by
      simpa using hv.div_const (η ^ 2)
    have h2 : Tendsto (fun r => ENNReal.ofReal (v r / η ^ 2)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    have h3 := ENNReal.Tendsto.const_mul h2
      (Or.inr (ENNReal.natCast_ne_top n))
    simpa using h3
  -- Squeeze.
  have hsqueeze :
      Tendsto (fun r =>
        P {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist μ)})
        atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
      (fun r => zero_le) hbad
  simpa only [hset_eq] using hsqueeze

/--
**Theorem 2 with the number of queries growing with the number of replicates.**

The fixed-`m` form above takes the number of queries as a constant.  The source lets `m` grow
with `r` -- that is the whole point of the theorem, which is a sufficient condition for *how
fast* `m` may grow -- so the response matrices live in a different space at every stage.  This
is that statement, with `m : ℕ → ℕ`.

The threshold `η r = ε · m r / (2 n²)` now moves with the stage, and the Chebyshev bound needs
`v r / (m r)² → 0`.  The degenerate stages where `m r = 0` need no separate treatment: the
dissimilarities are then identically zero and the bad event is empty, while `v r / (η r)^2` is
`v r / 0 = 0`, so the same inequality holds at those stages too.
-/
theorem dissimilarity_convergesInProbability_of_secondMoment_growing
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Ω → Fin n → Mat (m r) p)
    (μ : ∀ r, Fin n → Mat (m r) p)
    (v : Nat → Real)
    (hint : ∀ r i, Integrable (fun ω => ‖Xbar r ω i - μ r i‖ ^ 2) P)
    (hmoment : ∀ i, ∀ᶠ r in atTop, ∫ ω, ‖Xbar r ω i - μ r i‖ ^ 2 ∂P ≤ v r)
    (hv : Tendsto (fun r => v r / ((m r : Real)) ^ 2) atTop (𝓝 0)) :
    ConvergesInProbabilityZero P
      (fun r ω => frobSub (responseDist (Xbar r ω)) (responseDist (μ r))) := by
  -- the queries are finitely many, so per-query thresholds combine into one
  replace hmoment : ∀ᶠ r in atTop, ∀ i, ∫ ω, ‖Xbar r ω i - μ r i‖ ^ 2 ∂P ≤ v r :=
    Filter.eventually_all.2 hmoment
  intro ε hε
  have hfrob_nonneg : ∀ r ω,
      0 ≤ frobSub (responseDist (Xbar r ω)) (responseDist (μ r)) := by
    intro r ω; exact Real.sqrt_nonneg _
  have hset_eq : ∀ r,
      {ω | dist (frobSub (responseDist (Xbar r ω)) (responseDist (μ r))) (0 : Real) > ε}
        = {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist (μ r))} := by
    intro r
    ext ω
    simp only [Set.mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs, gt_iff_lt,
      abs_of_nonneg (hfrob_nonneg r ω)]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hzero : ∀ r ω, frobSub (responseDist (Xbar r ω)) (responseDist (μ r)) = 0 := by
      intro r ω
      simp [frobSub, frob, frobSq]
    have hempty : ∀ r,
        {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist (μ r))} = (∅ : Set Ω) := by
      intro r; ext ω
      simp only [hzero r ω, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hε.le
    simp only [hset_eq, hempty, measure_empty]
    exact tendsto_const_nhds
  have hn_pos : (0 : Real) < (n : Real) := by exact_mod_cast hnpos
  set η : Nat → Real := fun r => ε * ((m r : Real)) / (2 * (n : Real) * (n : Real)) with hη_def
  have hη_nonneg : ∀ r, 0 ≤ η r := by
    intro r
    rw [hη_def]
    positivity
  -- the deterministic reduction, valid at every stage including `m r = 0`
  have hdet : ∀ r ω, (∀ i : Fin n, ‖Xbar r ω i - μ r i‖ ≤ η r) →
      frobSub (responseDist (Xbar r ω)) (responseDist (μ r)) ≤ ε := by
    intro r ω hbound
    refine (frobSub_responseDist_le_of_uniform_errors (Xbar r ω) (μ r) hbound).trans ?_
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · rw [hm0]
      simp only [Nat.cast_zero, inv_zero, zero_mul, mul_zero]
      exact hε.le
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      have hval : ((n : Real) * (n : Real)) * ((((m r : Real))⁻¹) * (2 * η r)) = ε := by
        rw [hη_def]
        field_simp
      exact hval.le
  -- the per-stage bound, uniform in the degenerate case
  have hbad : ∀ᶠ r in atTop,
      P {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist (μ r))}
        ≤ (n : ENNReal) * ENNReal.ofReal (v r / (η r) ^ 2) := by
    filter_upwards [hmoment] with r hmr
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · have hzero : ∀ ω, frobSub (responseDist (Xbar r ω)) (responseDist (μ r)) = 0 := by
        intro ω
        simp [frobSub, frob, frobSq, responseDist, responseDistEntry, hm0]
      have hempty :
          {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist (μ r))} = (∅ : Set Ω) := by
        ext ω
        simp only [hzero ω, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact hε.le
      rw [hempty, measure_empty]
      exact bot_le
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      have hη_pos : 0 < η r := by
        rw [hη_def]
        positivity
      have hcheb : ∀ i : Fin n,
          P {ω | η r < ‖Xbar r ω i - μ r i‖} ≤ ENNReal.ofReal (v r / (η r) ^ 2) :=
        fun i => meas_gt_le_ofReal_secondMoment_div_sq P (hint r i) hη_pos (hmr i)
      have hincl :
          {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist (μ r))}
            ⊆ ⋃ i : Fin n, {ω | η r < ‖Xbar r ω i - μ r i‖} := by
        intro ω hω
        by_contra hnot
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
        exact absurd (hdet r ω hnot) (not_le.mpr hω)
      calc
        P {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist (μ r))}
            ≤ P (⋃ i : Fin n, {ω | η r < ‖Xbar r ω i - μ r i‖}) :=
              measure_mono hincl
        _ ≤ ∑ i : Fin n, P {ω | η r < ‖Xbar r ω i - μ r i‖} :=
              measure_iUnion_fintype_le (μ := P)
                (fun i => {ω | η r < ‖Xbar r ω i - μ r i‖})
        _ ≤ ∑ _i : Fin n, ENNReal.ofReal (v r / (η r) ^ 2) :=
              Finset.sum_le_sum fun i _ => hcheb i
        _ = (n : ENNReal) * ENNReal.ofReal (v r / (η r) ^ 2) := by
              simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the upper bound vanishes
  have hratio : ∀ r, v r / (η r) ^ 2
      = (4 * (n : Real) ^ 4 / ε ^ 2) * (v r / ((m r : Real)) ^ 2) := by
    intro r
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · rw [hη_def]
      simp [hm0]
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      rw [hη_def]
      field_simp
      ring
  have hub : Tendsto (fun r => (n : ENNReal) * ENNReal.ofReal (v r / (η r) ^ 2))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun r => v r / (η r) ^ 2) atTop (𝓝 0) := by
      have := hv.const_mul (4 * (n : Real) ^ 4 / ε ^ 2)
      simpa only [mul_zero, hratio] using this
    have h2 : Tendsto (fun r => ENNReal.ofReal (v r / (η r) ^ 2)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr (ENNReal.natCast_ne_top n))
    simpa using h3
  have hsqueeze :
      Tendsto (fun r =>
        P {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist (μ r))})
        atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
      (Filter.Eventually.of_forall fun r => bot_le) hbad
  simpa only [hset_eq] using hsqueeze

/-- The source's replicate condition `((1/m) * S)/r -> 0` implies the second-moment rate
`(S/r)/m^2 -> 0` that the Chebyshev step needs; the difference is a spare factor of `1/m`. -/
theorem sourceGammaRate_imp_secondMomentRate {m : Nat → Nat} {S : Nat → Real}
    (hS : ∀ r, 0 ≤ S r)
    (h : Tendsto (fun r => ((m r : Real))⁻¹ * S r / (r : Real)) atTop (𝓝 0)) :
    Tendsto (fun r => (S r / (r : Real)) / ((m r : Real)) ^ 2) atTop (𝓝 0) := by
  have hnn : ∀ r, 0 ≤ S r / (r : Real) := by
    intro r
    have := hS r
    positivity
  refine squeeze_zero (fun r => div_nonneg (hnn r) (by positivity)) (fun r => ?_) h
  rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
  · simp [hm0]
  · have hm_one : (1 : Real) ≤ ((m r : Real)) := by exact_mod_cast hmpos
    have hm_pos : (0 : Real) < ((m r : Real)) := by linarith
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · simp [hr0]
    · have hr_pos : (0 : Real) < (r : Real) := by exact_mod_cast hrpos
      have h1 : S r / (r : Real) / ((m r : Real)) ^ 2
          = S r / ((r : Real) * ((m r : Real)) ^ 2) := by rw [div_div]
      have h2 : ((m r : Real))⁻¹ * S r / (r : Real)
          = S r / ((r : Real) * ((m r : Real))) := by field_simp
      rw [h1, h2, div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : ((m r : Real)) ≤ ((m r : Real)) ^ 2 := by nlinarith [hm_one]
      have hkey : (S r * (r : Real)) * ((m r : Real))
          ≤ (S r * (r : Real)) * ((m r : Real)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg (hS r) hr_pos.le)
      calc S r * ((r : Real) * ((m r : Real)))
          = (S r * (r : Real)) * ((m r : Real)) := by ring
        _ ≤ (S r * (r : Real)) * ((m r : Real)) ^ 2 := hkey
        _ = S r * ((r : Real) * ((m r : Real)) ^ 2) := by ring

/--
**Theorem 2, in the source's own terms.**

`γ r i j` is the trace of the covariance of the response distribution of model `i` to query `j`
at stage `r`, so the sample-mean second moment is `∑_j γ_ij / r`.  The hypothesis
`hγ` is the source's condition, `((1/m) ∑_j γ_ij)/r → 0`, aggregated over the fixed model
collection -- for finitely many nonnegative sequences that is equivalent to the per-model form
the paper writes.
-/
theorem dissimilarity_convergesInProbability_of_gamma
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Ω → Fin n → Mat (m r) p)
    (μ : ∀ r, Fin n → Mat (m r) p)
    (γ : ∀ r, Fin n → Fin (m r) → Real)
    (hγnonneg : ∀ r i j, 0 ≤ γ r i j)
    (hint : ∀ r i, Integrable (fun ω => ‖Xbar r ω i - μ r i‖ ^ 2) P)
    (hmoment : ∀ i, ∀ᶠ r in atTop, ∫ ω, ‖Xbar r ω i - μ r i‖ ^ 2 ∂P
      ≤ (∑ i', ∑ j, γ r i' j) / (r : Real))
    (hγ : Tendsto (fun r => ((m r : Real))⁻¹ * (∑ i, ∑ j, γ r i j) / (r : Real))
      atTop (𝓝 0)) :
    ConvergesInProbabilityZero P
      (fun r ω => frobSub (responseDist (Xbar r ω)) (responseDist (μ r))) := by
  refine dissimilarity_convergesInProbability_of_secondMoment_growing P m Xbar μ
    (fun r => (∑ i, ∑ j, γ r i j) / (r : Real)) hint hmoment ?_
  exact sourceGammaRate_imp_secondMomentRate
    (fun r => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hγnonneg r i j) hγ

/--
**Theorem 4: pointwise dissimilarity concentration with the model count growing too.**

Theorem 4 lets `n` grow along with `m`, and in exchange asks only for *pointwise* convergence:
for each fixed pair of models, the sample dissimilarity approaches the population one.  That is
what makes the growing model count harmless -- no union bound over `n` is taken, only over the
two models in the pair -- so the condition on the replicate budget is the same one Theorem 2
needs.

The models are indexed by `ℕ` here rather than by `Fin (n r)`: a growing family is exactly a
family indexed by all of `ℕ`, and a fixed pair `(i, i')` is then literally a pair of natural
numbers, as in the source.

The bound `v` is indexed by the model as well as by the stage, and each model's bound is only
required to hold eventually, at a stage of its own choosing.  A single sequence bounding every
model in the collection would be a uniformity the source does not state -- the paper attaches
`(1/m) ∑_j γ_ij` to the model `i` -- and it would also be the wrong shape for the reason the
theorem is pointwise: only the two models of the pair are ever used.
-/
theorem pointwise_dissimilarity_convergesInProbability_of_secondMoment_growing
    (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Ω → Nat → Mat (m r) p)
    (μ : ∀ r, Nat → Mat (m r) p)
    (v : Nat → Nat → Real) (i i' : Nat)
    (hint : ∀ r, ∀ k ∈ ({i, i'} : Set Nat),
      Integrable (fun ω => ‖Xbar r ω k - μ r k‖ ^ 2) P)
    (hmoment : ∀ k ∈ ({i, i'} : Set Nat),
      ∀ᶠ r in atTop, ∫ ω, ‖Xbar r ω k - μ r k‖ ^ 2 ∂P ≤ v r k)
    (hv : ∀ k ∈ ({i, i'} : Set Nat),
      Tendsto (fun r => v r k / ((m r : Real)) ^ 2) atTop (𝓝 0)) :
    ConvergesInProbabilityZero P (fun r ω =>
      ((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
        - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖) := by
  intro ε hε
  set η : Nat → Real := fun r => ε * ((m r : Real)) / 2 with hη_def
  -- the deterministic reduction: two uniform errors control the dissimilarity entry
  have hdet : ∀ r ω, ‖Xbar r ω i - μ r i‖ ≤ η r → ‖Xbar r ω i' - μ r i'‖ ≤ η r →
      |((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
        - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖| ≤ ε := by
    intro r ω h1 h2
    have hrev : |‖Xbar r ω i - Xbar r ω i'‖ - ‖μ r i - μ r i'‖|
        ≤ ‖Xbar r ω i - μ r i‖ + ‖Xbar r ω i' - μ r i'‖ := by
      have hsub : (Xbar r ω i - Xbar r ω i') - (μ r i - μ r i')
          = (Xbar r ω i - μ r i) - (Xbar r ω i' - μ r i') := by abel
      calc |‖Xbar r ω i - Xbar r ω i'‖ - ‖μ r i - μ r i'‖|
          ≤ ‖(Xbar r ω i - Xbar r ω i') - (μ r i - μ r i')‖ := abs_norm_sub_norm_le _ _
        _ = ‖(Xbar r ω i - μ r i) - (Xbar r ω i' - μ r i')‖ := by rw [hsub]
        _ ≤ ‖Xbar r ω i - μ r i‖ + ‖Xbar r ω i' - μ r i'‖ := norm_sub_le _ _
    have hmul : |((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
        - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖|
        = ((m r : Real))⁻¹ * |‖Xbar r ω i - Xbar r ω i'‖ - ‖μ r i - μ r i'‖| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:Real) ≤ ((m r : Real))⁻¹)]
    rw [hmul]
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · simp [hm0, hε.le]
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      have hbound : |‖Xbar r ω i - Xbar r ω i'‖ - ‖μ r i - μ r i'‖| ≤ 2 * η r := by
        linarith [hrev, h1, h2]
      calc ((m r : Real))⁻¹ * |‖Xbar r ω i - Xbar r ω i'‖ - ‖μ r i - μ r i'‖|
          ≤ ((m r : Real))⁻¹ * (2 * η r) := by
            exact mul_le_mul_of_nonneg_left hbound (by positivity)
        _ = ε := by rw [hη_def]; field_simp
  -- the per-stage bound, valid once both models' second moments have reached their own bounds
  have hbad : ∀ᶠ r in atTop,
      P {ω | dist (((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
          - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖) (0 : Real) > ε}
        ≤ ENNReal.ofReal (v r i / (η r) ^ 2) + ENNReal.ofReal (v r i' / (η r) ^ 2) := by
    filter_upwards [hmoment i (by simp), hmoment i' (by simp)] with r hri hri'
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · have hempty : {ω | dist (((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
          - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖) (0 : Real) > ε} = (∅ : Set Ω) := by
        ext ω
        simp [hm0, Real.dist_eq, not_lt.mpr hε.le]
      rw [hempty, measure_empty]
      exact bot_le
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      have hη_pos : 0 < η r := by rw [hη_def]; positivity
      have hincl : {ω | dist (((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
            - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖) (0 : Real) > ε}
          ⊆ {ω | η r < ‖Xbar r ω i - μ r i‖} ∪ {ω | η r < ‖Xbar r ω i' - μ r i'‖} := by
        intro ω hω
        by_contra hnot
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
        simp only [Set.mem_ofPred_eq, gt_iff_lt, Real.dist_eq, sub_zero] at hω
        exact absurd (hdet r ω hnot.1 hnot.2) (not_le.mpr hω)
      calc P {ω | dist (((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
              - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖) (0 : Real) > ε}
          ≤ P ({ω | η r < ‖Xbar r ω i - μ r i‖} ∪ {ω | η r < ‖Xbar r ω i' - μ r i'‖}) :=
            measure_mono hincl
        _ ≤ P {ω | η r < ‖Xbar r ω i - μ r i‖} + P {ω | η r < ‖Xbar r ω i' - μ r i'‖} :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal (v r i / (η r) ^ 2) + ENNReal.ofReal (v r i' / (η r) ^ 2) :=
            add_le_add
              (meas_gt_le_ofReal_secondMoment_div_sq P (hint r i (by simp)) hη_pos hri)
              (meas_gt_le_ofReal_secondMoment_div_sq P (hint r i' (by simp)) hη_pos hri')
  -- each model's bound vanishes at its own rate; no rate common to the collection is used
  have hratio : ∀ (k r : Nat),
      v r k / (η r) ^ 2 = (4 / ε ^ 2) * (v r k / ((m r : Real)) ^ 2) := by
    intro k r
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · rw [hη_def]; simp [hm0]
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      rw [hη_def]; field_simp; ring
  have hone : ∀ k ∈ ({i, i'} : Set Nat),
      Tendsto (fun r => ENNReal.ofReal (v r k / (η r) ^ 2)) atTop (𝓝 0) := by
    intro k hk
    have h1 : Tendsto (fun r => v r k / (η r) ^ 2) atTop (𝓝 0) := by
      have := (hv k hk).const_mul (4 / ε ^ 2)
      simpa only [mul_zero, hratio k] using this
    simpa using ENNReal.tendsto_ofReal h1
  have hub : Tendsto (fun r => ENNReal.ofReal (v r i / (η r) ^ 2)
      + ENNReal.ofReal (v r i' / (η r) ^ 2)) atTop (𝓝 0) := by
    simpa using (hone i (by simp)).add (hone i' (by simp))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
    (Filter.Eventually.of_forall fun r => bot_le) hbad

/--
**Theorem 4 when the models are random too.**

`pointwise_dissimilarity_convergesInProbability_of_secondMoment_growing` treats the model
population means as fixed, which is how Theorem 4 is stated: the models are given and the
replicates are random.  Lemma 2 then *draws* the models, so composing the two needs the means to
be random as well.  Nothing in the argument used their determinism -- the reduction to two
uniform errors is pointwise in the sample, and Chebyshev is applied to `‖Xbar - μ‖` whichever of
the two is random -- so this is the same theorem with `μ` allowed to depend on the sample point.

The second moment here is taken *after* integrating over the model draw, which is what makes
this the wrong route to Theorem 5: see the section below.  It is not used there.
-/
theorem pointwise_dissimilarity_convergesInProbability_of_secondMoment_random
    (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Ω → Nat → Mat (m r) p)
    (μ : ∀ r, Ω → Nat → Mat (m r) p)
    (v : Nat → Nat → Real) (i i' : Nat)
    (hint : ∀ r, ∀ k ∈ ({i, i'} : Set Nat),
      Integrable (fun ω => ‖Xbar r ω k - μ r ω k‖ ^ 2) P)
    (hmoment : ∀ k ∈ ({i, i'} : Set Nat),
      ∀ᶠ r in atTop, ∫ ω, ‖Xbar r ω k - μ r ω k‖ ^ 2 ∂P ≤ v r k)
    (hv : ∀ k ∈ ({i, i'} : Set Nat),
      Tendsto (fun r => v r k / ((m r : Real)) ^ 2) atTop (𝓝 0)) :
    ConvergesInProbabilityZero P (fun r ω =>
      ((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
        - ((m r : Real))⁻¹ * ‖μ r ω i - μ r ω i'‖) := by
  intro ε hε
  set η : Nat → Real := fun r => ε * ((m r : Real)) / 2 with hη_def
  -- the deterministic reduction: two uniform errors control the dissimilarity entry
  have hdet : ∀ r ω, ‖Xbar r ω i - μ r ω i‖ ≤ η r → ‖Xbar r ω i' - μ r ω i'‖ ≤ η r →
      |((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
        - ((m r : Real))⁻¹ * ‖μ r ω i - μ r ω i'‖| ≤ ε := by
    intro r ω h1 h2
    have hrev : |‖Xbar r ω i - Xbar r ω i'‖ - ‖μ r ω i - μ r ω i'‖|
        ≤ ‖Xbar r ω i - μ r ω i‖ + ‖Xbar r ω i' - μ r ω i'‖ := by
      have hsub : (Xbar r ω i - Xbar r ω i') - (μ r ω i - μ r ω i')
          = (Xbar r ω i - μ r ω i) - (Xbar r ω i' - μ r ω i') := by abel
      calc |‖Xbar r ω i - Xbar r ω i'‖ - ‖μ r ω i - μ r ω i'‖|
          ≤ ‖(Xbar r ω i - Xbar r ω i') - (μ r ω i - μ r ω i')‖ := abs_norm_sub_norm_le _ _
        _ = ‖(Xbar r ω i - μ r ω i) - (Xbar r ω i' - μ r ω i')‖ := by rw [hsub]
        _ ≤ ‖Xbar r ω i - μ r ω i‖ + ‖Xbar r ω i' - μ r ω i'‖ := norm_sub_le _ _
    have hmul : |((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
        - ((m r : Real))⁻¹ * ‖μ r ω i - μ r ω i'‖|
        = ((m r : Real))⁻¹ * |‖Xbar r ω i - Xbar r ω i'‖ - ‖μ r ω i - μ r ω i'‖| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:Real) ≤ ((m r : Real))⁻¹)]
    rw [hmul]
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · simp [hm0, hε.le]
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      have hbound : |‖Xbar r ω i - Xbar r ω i'‖ - ‖μ r ω i - μ r ω i'‖| ≤ 2 * η r := by
        linarith [hrev, h1, h2]
      calc ((m r : Real))⁻¹ * |‖Xbar r ω i - Xbar r ω i'‖ - ‖μ r ω i - μ r ω i'‖|
          ≤ ((m r : Real))⁻¹ * (2 * η r) := by
            exact mul_le_mul_of_nonneg_left hbound (by positivity)
        _ = ε := by rw [hη_def]; field_simp
  -- the per-stage bound, valid once both models' second moments have reached their own bounds
  have hbad : ∀ᶠ r in atTop,
      P {ω | dist (((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
          - ((m r : Real))⁻¹ * ‖μ r ω i - μ r ω i'‖) (0 : Real) > ε}
        ≤ ENNReal.ofReal (v r i / (η r) ^ 2) + ENNReal.ofReal (v r i' / (η r) ^ 2) := by
    filter_upwards [hmoment i (by simp), hmoment i' (by simp)] with r hri hri'
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · have hempty : {ω | dist (((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
          - ((m r : Real))⁻¹ * ‖μ r ω i - μ r ω i'‖) (0 : Real) > ε} = (∅ : Set Ω) := by
        ext ω
        simp [hm0, Real.dist_eq, not_lt.mpr hε.le]
      rw [hempty, measure_empty]
      exact bot_le
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      have hη_pos : 0 < η r := by rw [hη_def]; positivity
      have hincl : {ω | dist (((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
            - ((m r : Real))⁻¹ * ‖μ r ω i - μ r ω i'‖) (0 : Real) > ε}
          ⊆ {ω | η r < ‖Xbar r ω i - μ r ω i‖} ∪ {ω | η r < ‖Xbar r ω i' - μ r ω i'‖} := by
        intro ω hω
        by_contra hnot
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
        simp only [Set.mem_ofPred_eq, gt_iff_lt, Real.dist_eq, sub_zero] at hω
        exact absurd (hdet r ω hnot.1 hnot.2) (not_le.mpr hω)
      calc P {ω | dist (((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
              - ((m r : Real))⁻¹ * ‖μ r ω i - μ r ω i'‖) (0 : Real) > ε}
          ≤ P ({ω | η r < ‖Xbar r ω i - μ r ω i‖} ∪ {ω | η r < ‖Xbar r ω i' - μ r ω i'‖}) :=
            measure_mono hincl
        _ ≤ P {ω | η r < ‖Xbar r ω i - μ r ω i‖} + P {ω | η r < ‖Xbar r ω i' - μ r ω i'‖} :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal (v r i / (η r) ^ 2) + ENNReal.ofReal (v r i' / (η r) ^ 2) :=
            add_le_add
              (meas_gt_le_ofReal_secondMoment_div_sq P (hint r i (by simp)) hη_pos hri)
              (meas_gt_le_ofReal_secondMoment_div_sq P (hint r i' (by simp)) hη_pos hri')
  -- each model's bound vanishes at its own rate
  have hratio : ∀ (k r : Nat),
      v r k / (η r) ^ 2 = (4 / ε ^ 2) * (v r k / ((m r : Real)) ^ 2) := by
    intro k r
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · rw [hη_def]; simp [hm0]
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      rw [hη_def]; field_simp; ring
  have hone : ∀ k ∈ ({i, i'} : Set Nat),
      Tendsto (fun r => ENNReal.ofReal (v r k / (η r) ^ 2)) atTop (𝓝 0) := by
    intro k hk
    have h1 : Tendsto (fun r => v r k / (η r) ^ 2) atTop (𝓝 0) := by
      have := (hv k hk).const_mul (4 / ε ^ 2)
      simpa only [mul_zero, hratio k] using this
    simpa using ENNReal.tendsto_ofReal h1
  have hub : Tendsto (fun r => ENNReal.ofReal (v r i / (η r) ^ 2)
      + ENNReal.ofReal (v r i' / (η r) ^ 2)) atTop (𝓝 0) := by
    simpa using (hone i (by simp)).add (hone i' (by simp))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
    (Filter.Eventually.of_forall fun r => bot_le) hbad


/--
**Theorem 4, in the source's own terms.**

The same trace-covariance condition as Theorem 2, with the model collection now growing as well:
models are indexed by `ℕ`, the pair `(i, i')` is fixed, and the conclusion is pointwise
convergence of that entry of the dissimilarity matrix.

`S k` is model `k`'s own `∑_j γ_kj`, and `hγ` is the source's condition for that model alone:
"for all `i`, `(1/m) ∑_j γ_ij = o(r)`" is a statement about each model, not a rate shared by the
collection, and the proof uses it only at `i` and `i'`.
-/
theorem pointwise_dissimilarity_convergesInProbability_of_gamma
    (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Ω → Nat → Mat (m r) p)
    (μ : ∀ r, Nat → Mat (m r) p)
    (S : Nat → Nat → Real) (i i' : Nat)
    (hSnonneg : ∀ k ∈ ({i, i'} : Set Nat), ∀ r, 0 ≤ S k r)
    (hint : ∀ r, ∀ k ∈ ({i, i'} : Set Nat),
      Integrable (fun ω => ‖Xbar r ω k - μ r k‖ ^ 2) P)
    (hmoment : ∀ k ∈ ({i, i'} : Set Nat), ∀ᶠ r in atTop,
      ∫ ω, ‖Xbar r ω k - μ r k‖ ^ 2 ∂P ≤ S k r / (r : Real))
    (hγ : ∀ k ∈ ({i, i'} : Set Nat),
      Tendsto (fun r => ((m r : Real))⁻¹ * S k r / (r : Real)) atTop (𝓝 0)) :
    ConvergesInProbabilityZero P (fun r ω =>
      ((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
        - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖) :=
  pointwise_dissimilarity_convergesInProbability_of_secondMoment_growing P m Xbar μ
    (fun r k => S k r / (r : Real)) i i' hint hmoment
    (fun k hk => sourceGammaRate_imp_secondMomentRate (hSnonneg k hk) (hγ k hk))

/-! ### Appendix A.2, as the hypothesis the concentration theorems consume

Every theorem above takes a bound on `∫ ‖Xbar - μ‖²`.  The source does not assume that bound; it
derives it, in Appendix A.2, from the sampling model: for each query the `r` replicates are iid
with trace-covariance `γ_ij`, so the replicate average has mean-squared error `γ_ij / r`, and the
Frobenius error of the response matrix is the sum of the row errors.

`eventually_integral_norm_sq_le_sum_gamma` is that derivation, in the form the concentration
theorems consume.  It assumes replicate independence for each fixed query and nothing across
queries -- the row split is an identity, so the queries never need to be independent of one
another.  The bound holds for every positive `r`, hence eventually, which is why the concentration
theorems ask for their moment hypothesis eventually rather than at every stage: at `r = 0` the
printed rate `γ/r` is not a bound on anything.
-/

/--
**The source's `γ` condition delivers the second-moment hypothesis.**

`Y r j t` is the `t`-th replicate of the response to query `j` at stage `r`, `mu r j` its mean and
`γ r j` its trace-covariance; `Xbar r` is the response matrix of replicate averages and `μ r` the
matrix of means.  The conclusion is the hypothesis `hmoment` of the concentration theorems, with
the paper's own `∑_j γ_ij` in place of an assumed bound.
-/
theorem eventually_integral_norm_sq_le_sum_gamma
    (P : Measure Ω) [IsProbabilityMeasure P] {p : Nat} (m : Nat → Nat)
    (Y : ∀ r : Nat, Fin (m r) → Fin r → Ω → Rvec p)
    (mu : ∀ r : Nat, Fin (m r) → Rvec p)
    (γ : ∀ r : Nat, Fin (m r) → Real)
    (Xbar : ∀ r, Ω → Mat (m r) p) (μ : ∀ r, Mat (m r) p)
    (hXbar : ∀ r ω (j : Fin (m r)) (c : Fin p),
      Xbar r ω (j, c) = ((r : Real)⁻¹ • ∑ t, Y r j t ω) c)
    (hμ : ∀ r (j : Fin (m r)) (c : Fin p), μ r (j, c) = mu r j c)
    (hL2 : ∀ r j t, MemLp (Y r j t) 2 P)
    (hmean : ∀ r j t (c : Fin p), ∫ ω, Y r j t ω c ∂P = mu r j c)
    (hindep : ∀ r (j : Fin (m r)), Set.Pairwise (Set.univ : Set (Fin r))
      fun t t' => ProbabilityTheory.IndepFun (Y r j t) (Y r j t') P)
    (hγ : ∀ r j t, ∫ ω, ‖Y r j t ω - mu r j‖ ^ 2 ∂P ≤ γ r j)
    (hintcoord : ∀ r (q : Fin (m r) × Fin p),
      Integrable (fun ω => (Xbar r ω q - μ r q) ^ 2) P) :
    ∀ᶠ r in atTop, ∫ ω, ‖Xbar r ω - μ r‖ ^ 2 ∂P ≤ (∑ j, γ r j) / (r : Real) := by
  filter_upwards [eventually_gt_atTop 0] with r hr
  exact Acharyya2024.SecondMoment.integral_norm_sq_matrix_le_sum_row_bounds P hr (Y r) (mu r) (γ r)
    (hL2 r) (hmean r) (hindep r) (hγ r) (Xbar r) (μ r) (hXbar r) (hμ r) (hintcoord r)

/--
**Theorem 2 from the source's sampling model.**

The same statement as `dissimilarity_convergesInProbability_of_gamma`, with the second-moment
hypothesis discharged rather than assumed: what is given is the sampling model -- `r` replicates
per query, independent for each fixed query, with trace-covariance `γ_ij` -- and the paper's
condition `((1/m) ∑_i ∑_j γ_ij)/r → 0`.
-/
theorem dissimilarity_convergesInProbability_of_replicates
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n p : Nat} (m : Nat → Nat)
    (Y : ∀ r : Nat, Fin n → Fin (m r) → Fin r → Ω → Rvec p)
    (mu : ∀ r : Nat, Fin n → Fin (m r) → Rvec p)
    (γ : ∀ r : Nat, Fin n → Fin (m r) → Real)
    (Xbar : ∀ r, Ω → Fin n → Mat (m r) p) (μ : ∀ r, Fin n → Mat (m r) p)
    (hXbar : ∀ r ω i (j : Fin (m r)) (c : Fin p),
      Xbar r ω i (j, c) = ((r : Real)⁻¹ • ∑ t, Y r i j t ω) c)
    (hμ : ∀ r i (j : Fin (m r)) (c : Fin p), μ r i (j, c) = mu r i j c)
    (hL2 : ∀ r i j t, MemLp (Y r i j t) 2 P)
    (hmean : ∀ r i j t (c : Fin p), ∫ ω, Y r i j t ω c ∂P = mu r i j c)
    (hindep : ∀ r i (j : Fin (m r)), Set.Pairwise (Set.univ : Set (Fin r))
      fun t t' => ProbabilityTheory.IndepFun (Y r i j t) (Y r i j t') P)
    (hγbound : ∀ r i j t, ∫ ω, ‖Y r i j t ω - mu r i j‖ ^ 2 ∂P ≤ γ r i j)
    (hγnonneg : ∀ r i j, 0 ≤ γ r i j)
    (hintcoord : ∀ r i (q : Fin (m r) × Fin p),
      Integrable (fun ω => (Xbar r ω i q - μ r i q) ^ 2) P)
    (hγ : Tendsto (fun r => ((m r : Real))⁻¹ * (∑ i, ∑ j, γ r i j) / (r : Real))
      atTop (𝓝 0)) :
    ConvergesInProbabilityZero P
      (fun r ω => frobSub (responseDist (Xbar r ω)) (responseDist (μ r))) := by
  refine dissimilarity_convergesInProbability_of_gamma P m Xbar μ γ hγnonneg
    (fun r i => Acharyya2024.SecondMoment.integrable_norm_sq_of_coord P
      (fun ω => Xbar r ω i) (μ r i) (hintcoord r i)) ?_ hγ
  intro i
  filter_upwards [eventually_gt_atTop 0] with r hr
  refine le_trans (Acharyya2024.SecondMoment.integral_norm_sq_matrix_le_sum_row_bounds P hr
    (Y r i) (mu r i) (γ r i) (hL2 r i) (hmean r i) (hindep r i) (hγbound r i)
    (fun ω => Xbar r ω i) (μ r i) (fun ω => hXbar r ω i) (hμ r i) (hintcoord r i)) ?_
  have hle : (∑ j, γ r i j) ≤ ∑ i', ∑ j, γ r i' j :=
    Finset.single_le_sum (f := fun i' => ∑ j, γ r i' j)
      (fun i' _ => Finset.sum_nonneg fun j _ => hγnonneg r i' j) (Finset.mem_univ i)
  gcongr

/--
**Theorem 4 from the source's sampling model.**

The same statement as `pointwise_dissimilarity_convergesInProbability_of_gamma`, with the
second-moment hypothesis discharged rather than assumed.  Models are indexed by `ℕ` and each
carries its own `∑_j γ_kj` and its own rate; nothing here is shared across the collection.
-/
theorem pointwise_dissimilarity_convergesInProbability_of_replicates
    (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Nat} (m : Nat → Nat)
    (Y : ∀ r : Nat, Nat → Fin (m r) → Fin r → Ω → Rvec p)
    (mu : ∀ r : Nat, Nat → Fin (m r) → Rvec p)
    (γ : ∀ r : Nat, Nat → Fin (m r) → Real)
    (Xbar : ∀ r, Ω → Nat → Mat (m r) p) (μ : ∀ r, Nat → Mat (m r) p)
    (i i' : Nat)
    (hXbar : ∀ r ω k (j : Fin (m r)) (c : Fin p),
      Xbar r ω k (j, c) = ((r : Real)⁻¹ • ∑ t, Y r k j t ω) c)
    (hμ : ∀ r k (j : Fin (m r)) (c : Fin p), μ r k (j, c) = mu r k j c)
    (hL2 : ∀ r k j t, MemLp (Y r k j t) 2 P)
    (hmean : ∀ r k j t (c : Fin p), ∫ ω, Y r k j t ω c ∂P = mu r k j c)
    (hindep : ∀ r k (j : Fin (m r)), Set.Pairwise (Set.univ : Set (Fin r))
      fun t t' => ProbabilityTheory.IndepFun (Y r k j t) (Y r k j t') P)
    (hγbound : ∀ r k j t, ∫ ω, ‖Y r k j t ω - mu r k j‖ ^ 2 ∂P ≤ γ r k j)
    (hγnonneg : ∀ r k j, 0 ≤ γ r k j)
    (hintcoord : ∀ r k (q : Fin (m r) × Fin p),
      Integrable (fun ω => (Xbar r ω k q - μ r k q) ^ 2) P)
    (hγ : ∀ k, Tendsto (fun r => ((m r : Real))⁻¹ * (∑ j, γ r k j) / (r : Real))
      atTop (𝓝 0)) :
    ConvergesInProbabilityZero P (fun r ω =>
      ((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
        - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖) :=
  pointwise_dissimilarity_convergesInProbability_of_gamma P m Xbar μ
    (fun k r => ∑ j, γ r k j) i i'
    (fun k _ r => Finset.sum_nonneg fun j _ => hγnonneg r k j)
    (fun r k _ => Acharyya2024.SecondMoment.integrable_norm_sq_of_coord P
      (fun ω => Xbar r ω k) (μ r k) (hintcoord r k))
    (fun k _ => eventually_integral_norm_sq_le_sum_gamma P m (fun r => Y r k) (fun r => mu r k)
      (fun r => γ r k) (fun r ω => Xbar r ω k) (fun r => μ r k)
      (fun r ω => hXbar r ω k) (fun r => hμ r k) (fun r => hL2 r k) (fun r => hmean r k)
      (fun r => hindep r k) (fun r => hγbound r k) (fun r => hintcoord r k))
    (fun k _ => hγ k)

/-! ### Theorem 4 when the models are drawn, without a uniform rate

Lemma 2 draws the models, so composing it with Theorem 4 needs the Theorem 4 conclusion under
the *joint* law of the model draw and the replicates.  There is a tempting way to get it and a
correct way to get it, and they do not prove the same theorem.

The tempting way is to bound the second moment `∫ ‖Xbar - μ‖²` after integrating over the model
draw, which is what `pointwise_dissimilarity_convergesInProbability_of_secondMoment_random` does.
That theorem is true; but deducing its hypothesis from the paper's condition needs the *expected*
value of `(1/m) ∑_j γ_ij` to be `o(r)`, and the paper states only that `(1/m) ∑_j γ_ij` is `o(r)`
for each model -- an almost-sure statement about the drawn models, which does not imply the
statement about its mean without a uniform integrability assumption the source never makes.

The correct way needs no such assumption.  Theorem 4 already gives, for *each fixed* model
configuration, that the bad-event probability tends to zero.  Bad-event probabilities lie in
`[0, 1]`, so the constant `1` dominates them and the model integral may be taken through the
limit (`TauCeti.tendsto_measure_compProd_gt_of_ae_tendsto_measure_slice`).  What comes out is
joint convergence in probability from hypotheses that are exactly the printed ones, read almost
surely in the model draw.

The composition is stated with a *kernel* rather than a product because that is the source's
sampling model: the response distributions `F_ij` belong to the model `f_i`, so the law of the
replicates depends on which models were drawn.  A product would assume them independent of the
draw, which the source does not say.
-/

/--
**Theorem 4 with the models drawn, from the source's own condition.**

The model configuration is a point `l` of `Λ`; given it, the replicates are drawn from `κ l`,
which is how the source's model-specific response distributions `F_ij` enter.  The paper's
condition becomes a hypothesis holding for almost every drawn configuration, which is how
"for all `i`, `(1/m) ∑_j γ_ij = o(r)`" reads once the models are random.  The conclusion is
convergence in probability under the joint law `Pmod ⊗ₘ κ`.

No bound uniform over the model population appears, in the hypotheses or in the proof.  The
integration over the model draw is justified by domination by `1`, not by a rate.
-/
theorem pointwise_dissimilarity_convergesInProbability_of_gamma_kernel
    {Λ : Type} [MeasurableSpace Λ]
    (Pmod : Measure Λ) [IsProbabilityMeasure Pmod]
    (κ : ProbabilityTheory.Kernel Λ Ω) [ProbabilityTheory.IsMarkovKernel κ]
    {p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Λ → Ω → Nat → Mat (m r) p)
    (μ : ∀ r, Λ → Nat → Mat (m r) p)
    (S : Λ → Nat → Nat → Real) (i i' : Nat)
    (hmeasX : ∀ r, Measurable fun z : Λ × Ω =>
      ((m r : Real))⁻¹ * ‖Xbar r z.1 z.2 i - Xbar r z.1 z.2 i'‖
        - ((m r : Real))⁻¹ * ‖μ r z.1 i - μ r z.1 i'‖)
    (hS : ∀ᵐ l ∂Pmod, ∀ k ∈ ({i, i'} : Set Nat), ∀ r, 0 ≤ S l k r)
    (hint : ∀ᵐ l ∂Pmod, ∀ r, ∀ k ∈ ({i, i'} : Set Nat),
      Integrable (fun ω => ‖Xbar r l ω k - μ r l k‖ ^ 2) (κ l))
    (hmoment : ∀ᵐ l ∂Pmod, ∀ k ∈ ({i, i'} : Set Nat), ∀ᶠ r in atTop,
      ∫ ω, ‖Xbar r l ω k - μ r l k‖ ^ 2 ∂(κ l) ≤ S l k r / (r : Real))
    (hγ : ∀ᵐ l ∂Pmod, ∀ k ∈ ({i, i'} : Set Nat),
      Tendsto (fun r => ((m r : Real))⁻¹ * S l k r / (r : Real)) atTop (𝓝 0)) :
    ConvergesInProbabilityZero (Pmod ⊗ₘ κ) (fun r z =>
      ((m r : Real))⁻¹ * ‖Xbar r z.1 z.2 i - Xbar r z.1 z.2 i'‖
        - ((m r : Real))⁻¹ * ‖μ r z.1 i - μ r z.1 i'‖) := by
  intro ε hε
  have key : Tendsto (fun r => (Pmod ⊗ₘ κ)
      {z : Λ × Ω | ε < |((m r : Real))⁻¹ * ‖Xbar r z.1 z.2 i - Xbar r z.1 z.2 i'‖
        - ((m r : Real))⁻¹ * ‖μ r z.1 i - μ r z.1 i'‖|}) atTop (𝓝 0) := by
    refine TauCeti.tendsto_measure_compProd_gt_of_ae_tendsto_measure_slice Pmod κ
      (fun r z => ((m r : Real))⁻¹ * ‖Xbar r z.1 z.2 i - Xbar r z.1 z.2 i'‖
        - ((m r : Real))⁻¹ * ‖μ r z.1 i - μ r z.1 i'‖) hmeasX ?_
    -- for almost every drawn model configuration, this is Theorem 4 with the models fixed
    filter_upwards [hS, hint, hmoment, hγ] with l hSl hintl hmomentl hγl
    have h := pointwise_dissimilarity_convergesInProbability_of_gamma (κ l) m
      (fun r => Xbar r l) (fun r => μ r l) (S l) i i' hSl hintl hmomentl hγl ε hε
    refine h.congr fun r => congrArg _ ?_
    ext ω
    simp
  refine key.congr fun r => congrArg _ ?_
  ext z
  simp

/--
**Theorem 4 with the models drawn**, in the special case where the replicate law does not depend
on the draw.

This is `pointwise_dissimilarity_convergesInProbability_of_gamma_kernel` with a constant kernel;
it is the statement to use when the model draw and the replicate randomness are independent.
-/
theorem pointwise_dissimilarity_convergesInProbability_of_gamma_random
    {Λ : Type} [MeasurableSpace Λ]
    (Pmod : Measure Λ) [IsProbabilityMeasure Pmod]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Λ → Ω → Nat → Mat (m r) p)
    (μ : ∀ r, Λ → Nat → Mat (m r) p)
    (S : Λ → Nat → Nat → Real) (i i' : Nat)
    (hmeasX : ∀ r, Measurable fun z : Λ × Ω =>
      ((m r : Real))⁻¹ * ‖Xbar r z.1 z.2 i - Xbar r z.1 z.2 i'‖
        - ((m r : Real))⁻¹ * ‖μ r z.1 i - μ r z.1 i'‖)
    (hS : ∀ᵐ l ∂Pmod, ∀ k ∈ ({i, i'} : Set Nat), ∀ r, 0 ≤ S l k r)
    (hint : ∀ᵐ l ∂Pmod, ∀ r, ∀ k ∈ ({i, i'} : Set Nat),
      Integrable (fun ω => ‖Xbar r l ω k - μ r l k‖ ^ 2) P)
    (hmoment : ∀ᵐ l ∂Pmod, ∀ k ∈ ({i, i'} : Set Nat), ∀ᶠ r in atTop,
      ∫ ω, ‖Xbar r l ω k - μ r l k‖ ^ 2 ∂P ≤ S l k r / (r : Real))
    (hγ : ∀ᵐ l ∂Pmod, ∀ k ∈ ({i, i'} : Set Nat),
      Tendsto (fun r => ((m r : Real))⁻¹ * S l k r / (r : Real)) atTop (𝓝 0)) :
    ConvergesInProbabilityZero (Pmod.prod P) (fun r z =>
      ((m r : Real))⁻¹ * ‖Xbar r z.1 z.2 i - Xbar r z.1 z.2 i'‖
        - ((m r : Real))⁻¹ * ‖μ r z.1 i - μ r z.1 i'‖) := by
  have h := pointwise_dissimilarity_convergesInProbability_of_gamma_kernel Pmod
    (ProbabilityTheory.Kernel.const Λ P) m Xbar μ S i i' hmeasX hS hint hmoment hγ
  rwa [Measure.compProd_const] at h

/-! ### The two models of a pair, drawn independently

Lemma 2 consumes convergence for a pair of *independently drawn* models.  Both members carry
their own replicate data, so the joint law on `(model × data) × (model × data)` is a product of
two two-stage experiments; regrouping it as one two-stage experiment on the pair of models
(`TauCeti.map_shuffle_prod_compProd`) is what lets the conditioning above be applied, with the
pair of models as the parameter and the two data sets conditionally independent given it.
-/

omit [MeasurableSpace Ω] in
private theorem integral_comp_fst_prod {Λ : Type} [MeasurableSpace Λ] [MeasurableSpace Ω]
    {μ : Measure Λ} [IsProbabilityMeasure μ] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {f : Λ → Real} (hf : Integrable f μ) :
    ∫ z : Λ × Ω, f z.1 ∂(μ.prod ν) = ∫ x, f x ∂μ := by
  rw [integral_prod _ (hf.comp_fst ν)]
  simp

omit [MeasurableSpace Ω] in
private theorem integral_comp_snd_prod {Λ : Type} [MeasurableSpace Λ] [MeasurableSpace Ω]
    {μ : Measure Λ} [IsProbabilityMeasure μ] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {f : Ω → Real} (hf : Integrable f ν) :
    ∫ z : Λ × Ω, f z.2 ∂(μ.prod ν) = ∫ x, f x ∂ν := by
  rw [integral_prod_symm _ (hf.comp_snd μ)]
  simp

/--
**Theorem 4 for an independently drawn pair of models.**

Each model is drawn from `Pmod` and, given it, its replicate data from `κ`; the two draws are
independent.  The hypotheses are the source's, per model: a second-moment bound with the model's
own `∑_j γ_ij` and the `o(r)` rate for it.  The conclusion is convergence in probability, under
the joint law of the two models and their data, of the sample dissimilarity to the dissimilarity
of the population means.

This is the form Lemma 2 consumes.  As in
`pointwise_dissimilarity_convergesInProbability_of_gamma_kernel`, no bound uniform over the model
population is used: the two drawn models carry their own bounds `S L.1` and `S L.2`, and they are
combined only after the pair is fixed.
-/
theorem pairwise_dissimilarity_convergesInProbability_of_gamma
    {Λ : Type} [MeasurableSpace Λ]
    (Pmod : Measure Λ) [IsProbabilityMeasure Pmod]
    (κ : ProbabilityTheory.Kernel Λ Ω) [ProbabilityTheory.IsMarkovKernel κ]
    {p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Λ × Ω → Mat (m r) p) (mu : ∀ r, Λ → Mat (m r) p)
    (S : Λ → Nat → Real)
    (hmeasX : ∀ r, Measurable (Xbar r)) (hmeasMu : ∀ r, Measurable (mu r))
    (hS : ∀ᵐ l ∂Pmod, ∀ r, 0 ≤ S l r)
    (hint : ∀ᵐ l ∂Pmod, ∀ r, Integrable (fun ω => ‖Xbar r (l, ω) - mu r l‖ ^ 2) (κ l))
    (hmoment : ∀ᵐ l ∂Pmod, ∀ᶠ r in atTop,
      ∫ ω, ‖Xbar r (l, ω) - mu r l‖ ^ 2 ∂(κ l) ≤ S l r / (r : Real))
    (hγ : ∀ᵐ l ∂Pmod,
      Tendsto (fun r => ((m r : Real))⁻¹ * S l r / (r : Real)) atTop (𝓝 0)) :
    ConvergesInProbabilityZero ((Pmod ⊗ₘ κ).prod (Pmod ⊗ₘ κ)) (fun r z =>
      ((m r : Real))⁻¹ * ‖Xbar r z.1 - Xbar r z.2‖
        - ((m r : Real))⁻¹ * ‖mu r z.1.1 - mu r z.2.1‖) := by
  classical
  -- the pair experiment, with the two models as the parameter
  set X2 : ∀ r, (Λ × Λ) → (Ω × Ω) → Nat → Mat (m r) p :=
    fun r L W k => if k = 0 then Xbar r (L.1, W.1) else Xbar r (L.2, W.2) with hX2
  set M2 : ∀ r, (Λ × Λ) → Nat → Mat (m r) p :=
    fun r L k => if k = 0 then mu r L.1 else mu r L.2 with hM2
  set S2 : (Λ × Λ) → Nat → Nat → Real :=
    fun L k r => if k = 0 then S L.1 r else S L.2 r with hS2
  have hX0 : ∀ (r : Nat) (L : Λ × Λ) (W : Ω × Ω), X2 r L W 0 = Xbar r (L.1, W.1) := by
    intro r L W; simp [hX2]
  have hX1 : ∀ (r : Nat) (L : Λ × Λ) (W : Ω × Ω), X2 r L W 1 = Xbar r (L.2, W.2) := by
    intro r L W; simp [hX2]
  have hM0 : ∀ (r : Nat) (L : Λ × Λ), M2 r L 0 = mu r L.1 := by intro r L; simp [hM2]
  have hM1 : ∀ (r : Nat) (L : Λ × Λ), M2 r L 1 = mu r L.2 := by intro r L; simp [hM2]
  -- the two coordinatewise almost-everywhere hypotheses, on the pair
  have hfst : ∀ {q : Λ → Prop}, (∀ᵐ l ∂Pmod, q l) → ∀ᵐ L ∂(Pmod.prod Pmod), q L.1 := fun h =>
    (Measure.quasiMeasurePreserving_fst (μ := Pmod) (ν := Pmod)).ae h
  have hsnd : ∀ {q : Λ → Prop}, (∀ᵐ l ∂Pmod, q l) → ∀ᵐ L ∂(Pmod.prod Pmod), q L.2 := fun h =>
    (Measure.quasiMeasurePreserving_snd (μ := Pmod) (ν := Pmod)).ae h
  have hpair : ∀ (L : Λ × Λ), (ProbabilityTheory.Kernel.parallelComp κ κ) L
      = (κ L.1).prod (κ L.2) := fun L => ProbabilityTheory.Kernel.parallelComp_apply κ κ L
  have hkey := pointwise_dissimilarity_convergesInProbability_of_gamma_kernel
    (Pmod.prod Pmod) (ProbabilityTheory.Kernel.parallelComp κ κ) m X2 M2 S2 0 1 ?_ ?_ ?_ ?_ ?_
  · -- transport the conclusion back along the regrouping of coordinates
    intro ε hε
    have hF : ∀ r, Measurable fun w : (Λ × Λ) × (Ω × Ω) =>
        ((m r : Real))⁻¹ * ‖X2 r w.1 w.2 0 - X2 r w.1 w.2 1‖
          - ((m r : Real))⁻¹ * ‖M2 r w.1 0 - M2 r w.1 1‖ := by
      intro r
      simp only [hX0, hX1, hM0, hM1]
      fun_prop
    have hshuffle : Measurable
        fun z : (Λ × Ω) × (Λ × Ω) => ((z.1.1, z.2.1), (z.1.2, z.2.2)) :=
      (measurable_fst.fst.prodMk measurable_snd.fst).prodMk
        (measurable_fst.snd.prodMk measurable_snd.snd)
    refine (hkey ε hε).congr fun r => ?_
    rw [← TauCeti.map_shuffle_prod_compProd Pmod Pmod κ κ,
      Measure.map_apply hshuffle
        (measurableSet_lt measurable_const
          (Measurable.dist (hF r) measurable_const) : MeasurableSet
            {w : (Λ × Λ) × (Ω × Ω) | dist
              (((m r : Real))⁻¹ * ‖X2 r w.1 w.2 0 - X2 r w.1 w.2 1‖
                - ((m r : Real))⁻¹ * ‖M2 r w.1 0 - M2 r w.1 1‖) (0 : Real) > ε})]
    congr 1
  · -- measurability of the pair statistic
    intro r
    simp only [hX0, hX1, hM0, hM1]
    fun_prop
  · filter_upwards [hfst hS, hsnd hS] with L h1 h2
    intro k _ r
    simp only [hS2]
    by_cases hk : k = 0 <;> simp only [hk, ↓reduceIte]
    · exact h1 r
    · exact h2 r
  · filter_upwards [hfst hint, hsnd hint] with L h1 h2
    intro r k _
    rw [hpair]
    by_cases hk : k = 0
    · simp only [hX2, hM2, hk, ↓reduceIte]
      exact (h1 r).comp_fst _
    · simp only [hX2, hM2, hk, ↓reduceIte]
      exact (h2 r).comp_snd _
  · filter_upwards [hfst hint, hsnd hint, hfst hmoment, hsnd hmoment] with L h1 h2 g1 g2
    intro k _
    by_cases hk : k = 0
    · filter_upwards [g1] with r gr
      rw [hpair]
      simp only [hX2, hM2, hS2, hk, ↓reduceIte]
      rw [integral_comp_fst_prod (h1 r)]
      exact gr
    · filter_upwards [g2] with r gr
      rw [hpair]
      simp only [hX2, hM2, hS2, hk, ↓reduceIte]
      rw [integral_comp_snd_prod (h2 r)]
      exact gr
  · filter_upwards [hfst hγ, hsnd hγ] with L h1 h2
    intro k _
    simp only [hS2]
    by_cases hk : k = 0 <;> simp only [hk, ↓reduceIte]
    · exact h1
    · exact h2

end Acharyya2024.Probability
