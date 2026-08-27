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

No added axioms, no open proof obligations.
-/

import Acharyya2024.Common
import ForTauCeti.Probability.Moments.Variance

open scoped BigOperators Topology
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
    (hmoment : ∀ r i, ∫ ω, ‖Xbar r ω i - μ r i‖ ^ 2 ∂P ≤ v r)
    (hv : Tendsto (fun r => v r / ((m r : Real)) ^ 2) atTop (𝓝 0)) :
    ConvergesInProbabilityZero P
      (fun r ω => frobSub (responseDist (Xbar r ω)) (responseDist (μ r))) := by
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
  have hbad : ∀ r : Nat,
      P {ω | ε < frobSub (responseDist (Xbar r ω)) (responseDist (μ r))}
        ≤ (n : ENNReal) * ENNReal.ofReal (v r / (η r) ^ 2) := by
    intro r
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
        fun i => meas_gt_le_ofReal_secondMoment_div_sq P (hint r i) hη_pos (hmoment r i)
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
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
      (fun r => bot_le) hbad
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
    (hmoment : ∀ r i, ∫ ω, ‖Xbar r ω i - μ r i‖ ^ 2 ∂P
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
-/
theorem pointwise_dissimilarity_convergesInProbability_of_secondMoment_growing
    (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Ω → Nat → Mat (m r) p)
    (μ : ∀ r, Nat → Mat (m r) p)
    (v : Nat → Real) (i i' : Nat)
    (hint : ∀ r k, Integrable (fun ω => ‖Xbar r ω k - μ r k‖ ^ 2) P)
    (hmoment : ∀ r k, ∫ ω, ‖Xbar r ω k - μ r k‖ ^ 2 ∂P ≤ v r)
    (hv : Tendsto (fun r => v r / ((m r : Real)) ^ 2) atTop (𝓝 0)) :
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
  -- the per-stage bound
  have hbad : ∀ r : Nat,
      P {ω | dist (((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
          - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖) (0 : Real) > ε}
        ≤ 2 * ENNReal.ofReal (v r / (η r) ^ 2) := by
    intro r
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
        _ ≤ ENNReal.ofReal (v r / (η r) ^ 2) + ENNReal.ofReal (v r / (η r) ^ 2) :=
            add_le_add
              (meas_gt_le_ofReal_secondMoment_div_sq P (hint r i) hη_pos (hmoment r i))
              (meas_gt_le_ofReal_secondMoment_div_sq P (hint r i') hη_pos (hmoment r i'))
        _ = 2 * ENNReal.ofReal (v r / (η r) ^ 2) := by rw [two_mul]
  -- the bound vanishes
  have hratio : ∀ r, v r / (η r) ^ 2 = (4 / ε ^ 2) * (v r / ((m r : Real)) ^ 2) := by
    intro r
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · rw [hη_def]; simp [hm0]
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      rw [hη_def]; field_simp; ring
  have hub : Tendsto (fun r => 2 * ENNReal.ofReal (v r / (η r) ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r => v r / (η r) ^ 2) atTop (𝓝 0) := by
      have := hv.const_mul (4 / ε ^ 2)
      simpa only [mul_zero, hratio] using this
    have h2 : Tendsto (fun r => ENNReal.ofReal (v r / (η r) ^ 2)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr (by simp : (2 : ENNReal) ≠ ⊤))
    simpa using h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
    (fun r => bot_le) hbad

/--
**Theorem 4 when the models are random too.**

`pointwise_dissimilarity_convergesInProbability_of_secondMoment_growing` treats the model
population means as fixed, which is how Theorem 4 is stated: the models are given and the
replicates are random.  Lemma 2 then *draws* the models, so composing the two needs the means to
be random as well.  Nothing in the argument used their determinism -- the reduction to two
uniform errors is pointwise in the sample, and Chebyshev is applied to `‖Xbar - μ‖` whichever of
the two is random -- so this is the same theorem with `μ` allowed to depend on the sample point.
-/
theorem pointwise_dissimilarity_convergesInProbability_of_secondMoment_random
    (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Ω → Nat → Mat (m r) p)
    (μ : ∀ r, Ω → Nat → Mat (m r) p)
    (v : Nat → Real) (i i' : Nat)
    (hint : ∀ r k, Integrable (fun ω => ‖Xbar r ω k - μ r ω k‖ ^ 2) P)
    (hmoment : ∀ r k, ∫ ω, ‖Xbar r ω k - μ r ω k‖ ^ 2 ∂P ≤ v r)
    (hv : Tendsto (fun r => v r / ((m r : Real)) ^ 2) atTop (𝓝 0)) :
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
  -- the per-stage bound
  have hbad : ∀ r : Nat,
      P {ω | dist (((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
          - ((m r : Real))⁻¹ * ‖μ r ω i - μ r ω i'‖) (0 : Real) > ε}
        ≤ 2 * ENNReal.ofReal (v r / (η r) ^ 2) := by
    intro r
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
        _ ≤ ENNReal.ofReal (v r / (η r) ^ 2) + ENNReal.ofReal (v r / (η r) ^ 2) :=
            add_le_add
              (meas_gt_le_ofReal_secondMoment_div_sq P (hint r i) hη_pos (hmoment r i))
              (meas_gt_le_ofReal_secondMoment_div_sq P (hint r i') hη_pos (hmoment r i'))
        _ = 2 * ENNReal.ofReal (v r / (η r) ^ 2) := by rw [two_mul]
  -- the bound vanishes
  have hratio : ∀ r, v r / (η r) ^ 2 = (4 / ε ^ 2) * (v r / ((m r : Real)) ^ 2) := by
    intro r
    rcases Nat.eq_zero_or_pos (m r) with hm0 | hmpos
    · rw [hη_def]; simp [hm0]
    · have hm_pos : (0 : Real) < ((m r : Real)) := by exact_mod_cast hmpos
      rw [hη_def]; field_simp; ring
  have hub : Tendsto (fun r => 2 * ENNReal.ofReal (v r / (η r) ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r => v r / (η r) ^ 2) atTop (𝓝 0) := by
      have := hv.const_mul (4 / ε ^ 2)
      simpa only [mul_zero, hratio] using this
    have h2 : Tendsto (fun r => ENNReal.ofReal (v r / (η r) ^ 2)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr (by simp : (2 : ENNReal) ≠ ⊤))
    simpa using h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
    (fun r => bot_le) hbad


/--
**Theorem 4, in the source's own terms.**

The same trace-covariance condition as Theorem 2, with the model collection now growing as well:
models are indexed by `ℕ`, the pair `(i, i')` is fixed, and the conclusion is pointwise
convergence of that entry of the dissimilarity matrix.
-/
theorem pointwise_dissimilarity_convergesInProbability_of_gamma
    (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Nat} (m : Nat → Nat)
    (Xbar : ∀ r, Ω → Nat → Mat (m r) p)
    (μ : ∀ r, Nat → Mat (m r) p)
    (S : Nat → Real) (i i' : Nat)
    (hSnonneg : ∀ r, 0 ≤ S r)
    (hint : ∀ r k, Integrable (fun ω => ‖Xbar r ω k - μ r k‖ ^ 2) P)
    (hmoment : ∀ r k, ∫ ω, ‖Xbar r ω k - μ r k‖ ^ 2 ∂P ≤ S r / (r : Real))
    (hγ : Tendsto (fun r => ((m r : Real))⁻¹ * S r / (r : Real)) atTop (𝓝 0)) :
    ConvergesInProbabilityZero P (fun r ω =>
      ((m r : Real))⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖
        - ((m r : Real))⁻¹ * ‖μ r i - μ r i'‖) :=
  pointwise_dissimilarity_convergesInProbability_of_secondMoment_growing P m Xbar μ
    (fun r => S r / (r : Real)) i i' hint hmoment
    (sourceGammaRate_imp_secondMomentRate hSnonneg hγ)

end Acharyya2024.Probability
