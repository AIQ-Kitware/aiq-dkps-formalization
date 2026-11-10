/-
DKPS / Quench: integrating a target-by-target error bound into a mean squared
error bound.

Theorem 2 of the paper bounds `MSE(ŷ_NN) = E_{P_f}[(ŷ_NN - y)²]`, an average over
the target model.  The proof printed in the paper controls the error of one fixed
target with high probability and then states the MSE bound.  Making that step
rigorous by requiring the error bound *simultaneously for every target* on one
high-probability event is what forced the earlier capstones onto a finite or
compact model class.

This module takes the other route, which needs neither.  The paper types the
score as `y : F × 2^{Q*} → [0,1]`, so every squared error is at most `1`.  If for
each target `f` the good event `{ω | (f, ω) ∈ G n}` has high probability, then the
mean squared error is at most `t` plus the `P_f`-mass of the targets that are bad
at `ω`, and that mass is small in `μ n`-probability by Tonelli, dominated
convergence and Markov's inequality.  The only requirement on the good sets is
joint measurability in the target and the sample.

## Main results

* `mse_le_add_measure_compl`: at one sample point, the mean squared error is at
  most `t` plus the mass of the targets on which the squared error may exceed `t`.
* `highProb_mse_le_of_targetwise`: target-by-target high-probability good events
  give a high-probability mean-squared-error bound.
-/
module

public import DkpsQuench2026.Core.ProofEngine
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib
public section

open scoped BigOperators Real Nat Classical Pointwise Topology ENNReal
open Filter MeasureTheory

noncomputable section

universe u v w

namespace DkpsQuench2026

variable {Q : Type u}
variable {X : Type v} [MeasurableSpace X]
variable {Ω : Type w} [MeasurableSpace Ω]

/-- The squared difference of two numbers in `[0, 1]` is at most `1`. -/
theorem sqLoss_le_one_of_mem_Icc {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    sqLoss a b ≤ 1 := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  unfold sqLoss
  nlinarith [mul_nonneg ha0 hb0, mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hb1)]

/-- **Mean squared error from a good set of targets.**

If the target and the estimate take values in `[0, 1]` and the squared error is at
most `t` on a measurable set `S` of targets, then the mean squared error is at most
`t` plus the probability of the complement of `S`.

No integrability of the squared error is assumed: the bound is proved by
domination by the integrable function `t + 𝟙_{Sᶜ}`. -/
theorem mse_le_add_measure_compl
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (y yhat : Model Q X → ℝ)
    (hy : ∀ f, y f ∈ Set.Icc (0 : ℝ) 1)
    (hyhat : ∀ f, yhat f ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) {S : Set (Model Q X)} (hS : MeasurableSet S)
    (herr : ∀ f ∈ S, sqLoss (yhat f) (y f) ≤ t) :
    MSE Pf y yhat ≤ t + (Pf Sᶜ).toReal := by
  have hdom : ∀ f, sqLoss (yhat f) (y f) ≤ t + Sᶜ.indicator (fun _ => (1 : ℝ)) f := by
    intro f
    by_cases hf : f ∈ S
    · have hnot : f ∉ Sᶜ := fun h => h hf
      rw [Set.indicator_of_notMem hnot, add_zero]
      exact herr f hf
    · rw [Set.indicator_of_mem (show f ∈ Sᶜ from hf)]
      linarith [sqLoss_le_one_of_mem_Icc (hyhat f) (hy f)]
  have hint : Integrable (fun f => t + Sᶜ.indicator (fun _ => (1 : ℝ)) f) Pf :=
    (integrable_const t).add ((integrable_const (1 : ℝ)).indicator hS.compl)
  calc
    MSE Pf y yhat = ∫ f, sqLoss (yhat f) (y f) ∂Pf := rfl
    _ ≤ ∫ f, (t + Sᶜ.indicator (fun _ => (1 : ℝ)) f) ∂Pf :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun f => by unfold sqLoss; positivity)
        hint (Eventually.of_forall hdom)
    _ = t + (Pf Sᶜ).toReal := by
      rw [integral_add (integrable_const t)
          ((integrable_const (1 : ℝ)).indicator hS.compl),
        integral_const, integral_indicator_const _ hS.compl]
      simp [Measure.real]

/-- A high-probability measurable event has complement probability tending to
zero. -/
theorem tendsto_measure_compl_of_highProbAtTop
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    {E : ℕ → Set Ω} (hEmeas : ∀ n, MeasurableSet (E n))
    (hE : HighProbAtTop μ hμ E) :
    Tendsto (fun n => μ n (E n)ᶜ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨N, hN⟩ := hE δ hδ
  rw [eventually_atTop]
  refine ⟨N + 1, fun n hn => ?_⟩
  have := hμ n
  have hge := hN n (by omega)
  rw [prob_compl_eq_one_sub (hEmeas n)]
  exact tsub_le_iff_tsub_le.mp hge

/-- A sequence of sets whose outer probabilities are dominated by a sequence
tending to zero holds with complementary high probability. -/
theorem highProbAtTop_of_measure_compl_le
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    {E : ℕ → Set Ω} {u : ℕ → ℝ≥0∞}
    (hu : Tendsto u atTop (𝓝 0))
    (hle : ∀ n, μ n (E n)ᶜ ≤ u n) :
    HighProbAtTop μ hμ E := by
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu.eventually (ge_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  have hcompl : μ n (E n)ᶜ ≤ δ := (hle n).trans (hN n hn.le)
  exact (tsub_le_tsub_left hcompl 1).trans
    (Measure.one_sub_measure_compl_le (μ n) (E n))

/-- **Target-by-target good events give a high-probability MSE bound.**

Let `G n ⊆ Model × Ω` be jointly measurable, with the squared error of the stage-`n`
estimate at most `t` on `G n`, and suppose that for every fixed target `f` the
section `{ω | (f, ω) ∈ G n}` holds with high probability.  If the target and the
estimates take values in `[0, 1]`, then for every `δ > 0` the mean squared error is
at most `t + δ` with high probability.

The good sets are not required to hold uniformly in the target, so no finiteness,
compactness, or regularity of the model class enters.  Proof: at each `ω` the mean
squared error is at most `t` plus the `P_f`-mass of the bad section
(`mse_le_add_measure_compl`); by Tonelli the `μ n`-expectation of that mass equals
`∫ μ n (bad section at f) dP_f`, which tends to zero by dominated convergence; and
Markov's inequality concludes. -/
theorem highProb_mse_le_of_targetwise
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (y : Model Q X → ℝ) (yhat : ℕ → Ω → Model Q X → ℝ)
    (hy : ∀ f, y f ∈ Set.Icc (0 : ℝ) 1)
    (hyhat : ∀ n ω f, yhat n ω f ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t)
    (G : ℕ → Set (Model Q X × Ω))
    (hGmeas : ∀ n, MeasurableSet (G n))
    (herr : ∀ n f ω, (f, ω) ∈ G n → sqLoss (yhat n ω f) (y f) ≤ t)
    (hG : ∀ f, HighProbAtTop μ hμ (fun n => Prod.mk f ⁻¹' G n))
    {δ : ℝ} (hδ : 0 < δ) :
    HighProbAtTop μ hμ (fun n => {ω | MSE Pf y (yhat n ω) ≤ t + δ}) := by
  -- The `P_f`-mass of the targets that are bad at the sample point `ω`.
  let bad : ℕ → Ω → ℝ≥0∞ := fun n ω => Pf ((fun f => (f, ω)) ⁻¹' (G n)ᶜ)
  have hbadMeas : ∀ n, Measurable (bad n) := fun n =>
    measurable_measure_prodMk_right (hGmeas n).compl
  -- Pointwise: a large mean squared error forces a large bad mass.
  have hincl : ∀ n, {ω | MSE Pf y (yhat n ω) ≤ t + δ}ᶜ ⊆
      {ω | ENNReal.ofReal δ ≤ bad n ω} := by
    intro n ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    have hS : MeasurableSet ((fun f => (f, ω)) ⁻¹' G n) :=
      measurable_prodMk_right (hGmeas n)
    have hmse := mse_le_add_measure_compl Pf y (yhat n ω) hy (hyhat n ω) ht hS
      (fun f hf => herr n f ω hf)
    have hlt : δ < (bad n ω).toReal := by
      have : (Pf ((fun f => (f, ω)) ⁻¹' G n)ᶜ).toReal = (bad n ω).toReal := rfl
      linarith
    exact ENNReal.ofReal_le_of_le_toReal hlt.le
  -- The expected bad mass is the product measure of the bad set, integrated over targets.
  have hswap : ∀ n, ∫⁻ ω, bad n ω ∂(μ n) =
      ∫⁻ f, μ n (Prod.mk f ⁻¹' (G n)ᶜ) ∂Pf := by
    intro n
    have := hμ n
    rw [← Measure.prod_apply_symm (μ := Pf) (ν := μ n) (hGmeas n).compl,
      Measure.prod_apply (hGmeas n).compl]
  -- Dominated convergence: each target is eventually good with high probability.
  have hlim : Tendsto (fun n => ∫⁻ f, μ n (Prod.mk f ⁻¹' (G n)ᶜ) ∂Pf)
      atTop (𝓝 0) := by
    have hzero : (∫⁻ _f : Model Q X, (0 : ℝ≥0∞) ∂Pf) = 0 := lintegral_zero
    rw [← hzero]
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1)
      (fun n => ?_) (fun n => Eventually.of_forall fun f => ?_) (by simp)
      (Eventually.of_forall fun f => ?_)
    · have := hμ n
      exact measurable_measure_prodMk_left (hGmeas n).compl
    · have := hμ n
      exact prob_le_one
    · have hsec : ∀ n, MeasurableSet (Prod.mk f ⁻¹' G n) := fun n =>
        measurable_prodMk_left (hGmeas n)
      simpa only [Set.preimage_compl] using
        tendsto_measure_compl_of_highProbAtTop μ hμ hsec (hG f)
  -- Markov's inequality on the bad mass.
  have hδE : ENNReal.ofReal δ ≠ 0 := by simpa using hδ
  have hmarkov : ∀ n, μ n {ω | ENNReal.ofReal δ ≤ bad n ω} ≤
      (∫⁻ f, μ n (Prod.mk f ⁻¹' (G n)ᶜ) ∂Pf) / ENNReal.ofReal δ := by
    intro n
    rw [← hswap n]
    exact meas_ge_le_lintegral_div (hbadMeas n).aemeasurable hδE ENNReal.ofReal_ne_top
  have hupper : Tendsto
      (fun n => (∫⁻ f, μ n (Prod.mk f ⁻¹' (G n)ᶜ) ∂Pf) / ENNReal.ofReal δ)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const hlim (Or.inr hδE)
  exact highProbAtTop_of_measure_compl_le μ hμ hupper fun n =>
    (measure_mono (hincl n)).trans (hmarkov n)

end DkpsQuench2026
