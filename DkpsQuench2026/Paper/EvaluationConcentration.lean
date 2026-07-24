/-
Concrete finite-sample concentration for the Quench/MAGNET evaluation layer.

The earlier `EvaluationBridges` file isolates the deterministic arithmetic that
turns population margins into finite card verdicts.  This file discharges the
corresponding deviation premises from pairwise-independent replicate losses by
combining the exact variance-of-the-mean identity with uncentered Chebyshev.

The result is intentionally finite and quantitative.  It does not pretend that
32 evaluation replicates make a statement asymptotically certain; instead it
returns an explicit upper bound on the probability that the finite card verdict
fails.  An additional generic theorem converts vanishing failure bounds into the
repository's `HighProbAtTop` interface when the replicate schedule grows.
-/
import DkpsQuench2026.Paper.EvaluationBridges
import ForTauCeti.Probability.Moments.SampleMean
import ForTauCeti.Probability.Moments.Variance
import ForTauCeti.MeasureTheory.Measure.Typeclasses.Probability

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology ENNReal
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

universe u v w

namespace DkpsQuench2026.Paper.TheoryPractice

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ω : Type w} [MeasurableSpace Ω]

/-! ## Generic replicate-average concentration -/

/-- Random empirical average of `r` scalar replicate statistics. -/
def randomEmpiricalMean {r : ℕ} (Z : Fin r → Ω → ℝ) (ω : Ω) : ℝ :=
  empiricalMean fun i => Z i ω

/-- The exact sample-mean second-moment machinery gives the usual `γ / r`
bound for a pairwise-independent family with common mean. -/
theorem integral_sq_randomEmpiricalMean_sub_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r)
    (Z : Fin r → Ω → ℝ) (center γ : ℝ)
    (hL2 : ∀ i, MemLp (Z i) 2 P)
    (hmean : ∀ i, ∫ ω, Z i ω ∂P = center)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (Z i) (Z j) P)
    (hsecond : ∀ i, ∫ ω, (Z i ω - center) ^ 2 ∂P ≤ γ) :
    ∫ ω, (randomEmpiricalMean Z ω - center) ^ 2 ∂P ≤ γ / r := by
  have hsecondNorm : ∀ i, ∫ ω, ‖Z i ω - center‖ ^ 2 ∂P ≤ γ := by
    intro i
    simpa [Real.norm_eq_abs, sq_abs] using hsecond i
  have h := TauCeti.integral_norm_sq_average_sub_le_of_bound
    P hr Z center hL2 hmean hindep hsecondNorm
  simpa [randomEmpiricalMean, empiricalMean, smul_eq_mul,
    Real.norm_eq_abs, sq_abs] using h

/-- Chebyshev bound for a finite replicate average. -/
theorem measure_randomEmpiricalMean_deviation_gt_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r)
    (Z : Fin r → Ω → ℝ) (center γ ε : ℝ)
    (hε : 0 < ε)
    (hL2 : ∀ i, MemLp (Z i) 2 P)
    (hmean : ∀ i, ∫ ω, Z i ω ∂P = center)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (Z i) (Z j) P)
    (hsecond : ∀ i, ∫ ω, (Z i ω - center) ^ 2 ∂P ≤ γ) :
    P {ω | ε < |randomEmpiricalMean Z ω - center|} ≤
      ENNReal.ofReal ((γ / r) / ε ^ 2) := by
  have hsumL2 : MemLp (fun ω => ∑ i, Z i ω) 2 P :=
    memLp_finsetSum (Finset.univ : Finset (Fin r))
      (fun i _hi => hL2 i)
  have havgL2 : MemLp (randomEmpiricalMean Z) 2 P := by
    change MemLp (fun ω => (r : ℝ)⁻¹ * ∑ i, Z i ω) 2 P
    exact hsumL2.const_mul ((r : ℝ)⁻¹)
  have hdevInt : Integrable
      (fun ω => |randomEmpiricalMean Z ω - center| ^ 2) P := by
    simpa [sq_abs] using
      ((havgL2.sub (memLp_const center)).integrable_sq)
  have hmoment :
      ∫ ω, |randomEmpiricalMean Z ω - center| ^ 2 ∂P ≤ γ / r := by
    simpa [sq_abs] using
      integral_sq_randomEmpiricalMean_sub_le
        P hr Z center γ hL2 hmean hindep hsecond
  exact TauCeti.meas_gt_le_ofReal_integral_sq_div_sq
    P hdevInt hε hmoment

/-- If both the statistic and its mean lie in `[0,1]`, its centered second
moment is at most one.  This deliberately uses the simple universal bound one;
the sharper Bernoulli bound `p(1-p) ≤ 1/4` is unnecessary for the logical
bridge and would add avoidable algebra. -/
theorem centeredSecondMoment_le_one_of_unitInterval
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (center : ℝ)
    (hL2 : MemLp Z 2 P)
    (hcenter : 0 ≤ center ∧ center ≤ 1)
    (hunit : ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ 1) :
    ∫ ω, (Z ω - center) ^ 2 ∂P ≤ 1 := by
  have hint : Integrable (fun ω => (Z ω - center) ^ 2) P :=
    (hL2.sub (memLp_const center)).integrable_sq
  calc
    ∫ ω, (Z ω - center) ^ 2 ∂P ≤ ∫ _ω, (1 : ℝ) ∂P := by
      apply integral_mono_ae
      · exact hint
      · exact integrable_const _
      · filter_upwards [hunit] with ω hω
        have habs : |Z ω - center| ≤ 1 := by
          apply abs_le.mpr
          constructor <;> linarith [hω.1, hω.2, hcenter.1, hcenter.2]
        have hsquare := pow_le_pow_left₀
          (abs_nonneg (Z ω - center)) habs 2
        simpa [sq_abs] using hsquare
    _ = 1 := by simp

/-- A vanishing upper bound on failure probabilities yields the development's
high-probability-at-top predicate.  No event measurability is needed. -/
theorem highProbAtTop_of_failure_bound_tendsto_zero
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (event : ℕ → Set Ω) (bound : ℕ → ENNReal)
    (hfailure : ∀ k, μ k (event k)ᶜ ≤ bound k)
    (hbound : Tendsto bound atTop (𝓝 0)) :
    HighProbAtTop μ hμ event := by
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero] at hbound
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hbound δ hδ)
  refine ⟨N, fun k hk => ?_⟩
  have hfailδ : μ k (event k)ᶜ ≤ δ :=
    (hfailure k).trans (hN k (le_of_lt hk))
  exact (tsub_le_tsub_left hfailδ 1).trans
    (TauCeti.one_sub_measure_compl_le (μ k) (event k))


/-- A finite failure-probability upper bound is equivalently a lower confidence
bound for the success event.  This form is convenient for evaluation reports. -/
theorem one_sub_failureBound_le_successProbability
    (P : Measure Ω) [IsProbabilityMeasure P]
    (event : Set Ω) (failureBound : ENNReal)
    (hfailure : P eventᶜ ≤ failureBound) :
    1 - failureBound ≤ P event := by
  exact (tsub_le_tsub_left hfailure 1).trans
    (TauCeti.one_sub_measure_compl_le P event)

/-- Stage-dependent Chebyshev concentration promoted to `HighProbAtTop` whenever
its explicit second-moment bound vanishes.  The replicate count may grow with
the stage. -/
theorem highProb_randomEmpiricalMean_deviation_of_secondMoment
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (replicates : ℕ → ℕ) (hreplicates : ∀ k, 0 < replicates k)
    (Z : ∀ k, Fin (replicates k) → Ω → ℝ)
    (center gamma : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hL2 : ∀ k i, MemLp (Z k i) 2 (μ k))
    (hmean : ∀ k i, ∫ ω, Z k i ω ∂(μ k) = center k)
    (hindep : ∀ k, Set.Pairwise (Set.univ : Set (Fin (replicates k)))
      fun i j => IndepFun (Z k i) (Z k j) (μ k))
    (hsecond : ∀ k i,
      ∫ ω, (Z k i ω - center k) ^ 2 ∂(μ k) ≤ gamma k)
    (hvanish : Tendsto
      (fun k => ENNReal.ofReal
        (((gamma k) / (replicates k)) / ε ^ 2)) atTop (𝓝 0)) :
    HighProbAtTop μ hμ (fun k => {ω |
      |randomEmpiricalMean (Z k) ω - center k| ≤ ε}) := by
  apply highProbAtTop_of_failure_bound_tendsto_zero
    μ hμ
    (fun k => {ω | |randomEmpiricalMean (Z k) ω - center k| ≤ ε})
    (fun k => ENNReal.ofReal
      (((gamma k) / (replicates k)) / ε ^ 2))
  · intro k
    letI : IsProbabilityMeasure (μ k) := hμ k
    have htail := measure_randomEmpiricalMean_deviation_gt_le
      (μ k) (hreplicates k) (Z k) (center k) (gamma k) ε hε
      (hL2 k) (hmean k) (hindep k) (hsecond k)
    have hset :
        ({ω | |randomEmpiricalMean (Z k) ω - center k| ≤ ε} : Set Ω)ᶜ =
          {ω | ε < |randomEmpiricalMean (Z k) ω - center k|} := by
      ext ω
      simp [not_le]
    rw [hset]
    exact htail
  · exact hvanish

/-! ## Finite MAE concentration -/

/-- A clipped prediction and a unit-interval truth have absolute loss in
`[0,1]`. -/
theorem absLoss_clipUnit_mem_Icc
    (prediction truth : ℝ) (htruth : truth ∈ Set.Icc (0 : ℝ) 1) :
    absLoss (clipUnit prediction) truth ∈ Set.Icc (0 : ℝ) 1 := by
  have hclip0 : 0 ≤ clipUnit prediction := by
    simp [clipUnit]
  have hclip1 : clipUnit prediction ≤ 1 := by
    simp [clipUnit]
  constructor
  · exact abs_nonneg _
  · unfold absLoss
    exact abs_le.mpr ⟨by linarith [hclip0, htruth.2],
      by linarith [hclip1, htruth.1]⟩

/-- Quantitative concentration of finite empirical MAE around its population
mean, from pairwise independence and a common second-moment bound. -/
theorem measure_empiricalMAE_deviation_gt_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r)
    (truth prediction : Fin r → Ω → ℝ)
    (populationMAE γ ε : ℝ) (hε : 0 < ε)
    (hL2 : ∀ i, MemLp
      (fun ω => absLoss (prediction i ω) (truth i ω)) 2 P)
    (hmean : ∀ i,
      ∫ ω, absLoss (prediction i ω) (truth i ω) ∂P = populationMAE)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r)) fun i j =>
      IndepFun
        (fun ω => absLoss (prediction i ω) (truth i ω))
        (fun ω => absLoss (prediction j ω) (truth j ω)) P)
    (hsecond : ∀ i,
      ∫ ω, (absLoss (prediction i ω) (truth i ω) - populationMAE) ^ 2 ∂P ≤ γ) :
    P {ω | ε < abs (
      empiricalMAE (fun i => truth i ω) (fun i => prediction i ω) -
        populationMAE)} ≤
      ENNReal.ofReal ((γ / r) / ε ^ 2) := by
  simpa [randomEmpiricalMean, empiricalMAE] using
    measure_randomEmpiricalMean_deviation_gt_le
      P hr
      (fun i ω => absLoss (prediction i ω) (truth i ω))
      populationMAE γ ε hε hL2 hmean hindep hsecond

/-- The same MAE concentration theorem with the universal unit-interval second
moment bound. -/
theorem measure_empiricalMAE_deviation_gt_le_of_unitInterval
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r)
    (truth prediction : Fin r → Ω → ℝ)
    (populationMAE ε : ℝ) (hε : 0 < ε)
    (hpopulation : 0 ≤ populationMAE ∧ populationMAE ≤ 1)
    (hL2 : ∀ i, MemLp
      (fun ω => absLoss (prediction i ω) (truth i ω)) 2 P)
    (hmean : ∀ i,
      ∫ ω, absLoss (prediction i ω) (truth i ω) ∂P = populationMAE)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r)) fun i j =>
      IndepFun
        (fun ω => absLoss (prediction i ω) (truth i ω))
        (fun ω => absLoss (prediction j ω) (truth j ω)) P)
    (hunit : ∀ i, ∀ᵐ ω ∂P,
      absLoss (prediction i ω) (truth i ω) ∈ Set.Icc (0 : ℝ) 1) :
    P {ω | ε < abs (
      empiricalMAE (fun i => truth i ω) (fun i => prediction i ω) -
        populationMAE)} ≤
      ENNReal.ofReal (((1 : ℝ) / r) / ε ^ 2) := by
  apply measure_empiricalMAE_deviation_gt_le
    P hr truth prediction populationMAE 1 ε hε hL2 hmean hindep
  intro i
  exact centeredSecondMoment_le_one_of_unitInterval
    P (fun ω => absLoss (prediction i ω) (truth i ω))
    populationMAE (hL2 i) hpopulation (hunit i)

/-- Explicit finite confidence bound for the cross-budget MAE card.  Candidate
and baseline replicates need not be independent of each other; only each
within-estimator family is required to be pairwise independent. -/
theorem measure_not_empiricalCrossBudgetMAEClaim_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r)
    (truth candidate baseline : Fin r → Ω → ℝ)
    (candidatePopulation baselinePopulation : ℝ)
    (candidateGamma baselineGamma candidateError baselineError : ℝ)
    (hcandidateError : 0 < candidateError)
    (hbaselineError : 0 < baselineError)
    (hmargin : candidatePopulation + candidateError + baselineError ≤
      baselinePopulation)
    (hcandidateL2 : ∀ i, MemLp
      (fun ω => absLoss (candidate i ω) (truth i ω)) 2 P)
    (hcandidateMean : ∀ i,
      ∫ ω, absLoss (candidate i ω) (truth i ω) ∂P = candidatePopulation)
    (hcandidateIndep : Set.Pairwise (Set.univ : Set (Fin r)) fun i j =>
      IndepFun
        (fun ω => absLoss (candidate i ω) (truth i ω))
        (fun ω => absLoss (candidate j ω) (truth j ω)) P)
    (hcandidateSecond : ∀ i,
      ∫ ω, (absLoss (candidate i ω) (truth i ω) -
        candidatePopulation) ^ 2 ∂P ≤ candidateGamma)
    (hbaselineL2 : ∀ i, MemLp
      (fun ω => absLoss (baseline i ω) (truth i ω)) 2 P)
    (hbaselineMean : ∀ i,
      ∫ ω, absLoss (baseline i ω) (truth i ω) ∂P = baselinePopulation)
    (hbaselineIndep : Set.Pairwise (Set.univ : Set (Fin r)) fun i j =>
      IndepFun
        (fun ω => absLoss (baseline i ω) (truth i ω))
        (fun ω => absLoss (baseline j ω) (truth j ω)) P)
    (hbaselineSecond : ∀ i,
      ∫ ω, (absLoss (baseline i ω) (truth i ω) -
        baselinePopulation) ^ 2 ∂P ≤ baselineGamma) :
    P {ω | ¬ EmpiricalCrossBudgetMAEClaim
      (fun i => truth i ω) (fun i => candidate i ω)
      (fun i => baseline i ω)} ≤
      ENNReal.ofReal ((candidateGamma / r) / candidateError ^ 2) +
      ENNReal.ofReal ((baselineGamma / r) / baselineError ^ 2) := by
  let candidateBad : Set Ω := {ω | candidateError < abs (
    empiricalMAE (fun i => truth i ω) (fun i => candidate i ω) -
      candidatePopulation)}
  let baselineBad : Set Ω := {ω | baselineError < abs (
    empiricalMAE (fun i => truth i ω) (fun i => baseline i ω) -
      baselinePopulation)}
  have hc := measure_empiricalMAE_deviation_gt_le
    P hr truth candidate candidatePopulation candidateGamma candidateError
    hcandidateError hcandidateL2 hcandidateMean hcandidateIndep hcandidateSecond
  have hb := measure_empiricalMAE_deviation_gt_le
    P hr truth baseline baselinePopulation baselineGamma baselineError
    hbaselineError hbaselineL2 hbaselineMean hbaselineIndep hbaselineSecond
  have hsubset :
      {ω | ¬ EmpiricalCrossBudgetMAEClaim
        (fun i => truth i ω) (fun i => candidate i ω)
        (fun i => baseline i ω)} ⊆ candidateBad ∪ baselineBad := by
    intro ω hfail
    by_contra hnot
    have hnot' : ω ∉ candidateBad ∧ ω ∉ baselineBad := by
      simpa [Set.mem_union] using hnot
    have hcnot : ¬ candidateError < abs (
        empiricalMAE (fun i => truth i ω) (fun i => candidate i ω) -
          candidatePopulation) := by
      simpa [candidateBad] using hnot'.1
    have hbnot : ¬ baselineError < abs (
        empiricalMAE (fun i => truth i ω) (fun i => baseline i ω) -
          baselinePopulation) := by
      simpa [baselineBad] using hnot'.2
    have hcdev : EmpiricalMAEDeviation
        (fun i => truth i ω) (fun i => candidate i ω)
        candidatePopulation candidateError := by
      unfold EmpiricalMAEDeviation
      exact not_lt.mp hcnot
    have hbdev : EmpiricalMAEDeviation
        (fun i => truth i ω) (fun i => baseline i ω)
        baselinePopulation baselineError := by
      unfold EmpiricalMAEDeviation
      exact not_lt.mp hbnot
    exact hfail (empiricalCrossBudgetMAEClaim_of_deviations
      (fun i => truth i ω) (fun i => candidate i ω)
      (fun i => baseline i ω)
      candidatePopulation baselinePopulation candidateError baselineError
      hcdev hbdev hmargin)
  calc
    P {ω | ¬ EmpiricalCrossBudgetMAEClaim
        (fun i => truth i ω) (fun i => candidate i ω)
        (fun i => baseline i ω)}
        ≤ P (candidateBad ∪ baselineBad) := measure_mono hsubset
    _ ≤ P candidateBad + P baselineBad := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((candidateGamma / r) / candidateError ^ 2) +
        ENNReal.ofReal ((baselineGamma / r) / baselineError ^ 2) := by
      exact add_le_add (by simpa [candidateBad] using hc)
        (by simpa [baselineBad] using hb)

/-! ## Finite replicate-win concentration -/

/-- Every strict-win indicator lies in `[0,1]`. -/
theorem strictAbsoluteErrorWin_mem_Icc
    (truth candidate baseline : ℝ) :
    strictAbsoluteErrorWin truth candidate baseline ∈ Set.Icc (0 : ℝ) 1 := by
  unfold strictAbsoluteErrorWin
  split_ifs <;> norm_num

/-- Quantitative concentration of the observed strict-win fraction around its
population win probability. -/
theorem measure_empiricalWinFraction_deviation_gt_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r)
    (truth candidate baseline : Fin r → Ω → ℝ)
    (populationWinRate γ ε : ℝ) (hε : 0 < ε)
    (hL2 : ∀ i, MemLp
      (fun ω => strictAbsoluteErrorWin
        (truth i ω) (candidate i ω) (baseline i ω)) 2 P)
    (hmean : ∀ i,
      ∫ ω, strictAbsoluteErrorWin
        (truth i ω) (candidate i ω) (baseline i ω) ∂P = populationWinRate)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r)) fun i j =>
      IndepFun
        (fun ω => strictAbsoluteErrorWin
          (truth i ω) (candidate i ω) (baseline i ω))
        (fun ω => strictAbsoluteErrorWin
          (truth j ω) (candidate j ω) (baseline j ω)) P)
    (hsecond : ∀ i,
      ∫ ω, (strictAbsoluteErrorWin
        (truth i ω) (candidate i ω) (baseline i ω) -
          populationWinRate) ^ 2 ∂P ≤ γ) :
    P {ω | ε < abs (
      empiricalWinFraction (fun i => truth i ω) (fun i => candidate i ω)
        (fun i => baseline i ω) - populationWinRate)} ≤
      ENNReal.ofReal ((γ / r) / ε ^ 2) := by
  simpa [randomEmpiricalMean, empiricalWinFraction] using
    measure_randomEmpiricalMean_deviation_gt_le
      P hr
      (fun i ω => strictAbsoluteErrorWin
        (truth i ω) (candidate i ω) (baseline i ω))
      populationWinRate γ ε hε hL2 hmean hindep hsecond

/-- Win-fraction concentration with the automatic universal second-moment bound
for Bernoulli indicators. -/
theorem measure_empiricalWinFraction_deviation_gt_le_one
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r)
    (truth candidate baseline : Fin r → Ω → ℝ)
    (populationWinRate ε : ℝ) (hε : 0 < ε)
    (hpopulation : 0 ≤ populationWinRate ∧ populationWinRate ≤ 1)
    (hL2 : ∀ i, MemLp
      (fun ω => strictAbsoluteErrorWin
        (truth i ω) (candidate i ω) (baseline i ω)) 2 P)
    (hmean : ∀ i,
      ∫ ω, strictAbsoluteErrorWin
        (truth i ω) (candidate i ω) (baseline i ω) ∂P = populationWinRate)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r)) fun i j =>
      IndepFun
        (fun ω => strictAbsoluteErrorWin
          (truth i ω) (candidate i ω) (baseline i ω))
        (fun ω => strictAbsoluteErrorWin
          (truth j ω) (candidate j ω) (baseline j ω)) P) :
    P {ω | ε < abs (
      empiricalWinFraction (fun i => truth i ω) (fun i => candidate i ω)
        (fun i => baseline i ω) - populationWinRate)} ≤
      ENNReal.ofReal (((1 : ℝ) / r) / ε ^ 2) := by
  apply measure_empiricalWinFraction_deviation_gt_le
    P hr truth candidate baseline populationWinRate 1 ε hε
    hL2 hmean hindep
  intro i
  apply centeredSecondMoment_le_one_of_unitInterval
    P
    (fun ω => strictAbsoluteErrorWin
      (truth i ω) (candidate i ω) (baseline i ω))
    populationWinRate (hL2 i) hpopulation
  exact Filter.Eventually.of_forall fun ω =>
    strictAbsoluteErrorWin_mem_Icc
      (truth i ω) (candidate i ω) (baseline i ω)

/-- Explicit finite confidence bound for the practical replicate-win card. -/
theorem measure_not_empiricalWinRateClaim_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r)
    (threshold populationWinRate γ ε : ℝ)
    (truth candidate baseline : Fin r → Ω → ℝ)
    (hε : 0 < ε)
    (hmargin : threshold + ε ≤ populationWinRate)
    (hL2 : ∀ i, MemLp
      (fun ω => strictAbsoluteErrorWin
        (truth i ω) (candidate i ω) (baseline i ω)) 2 P)
    (hmean : ∀ i,
      ∫ ω, strictAbsoluteErrorWin
        (truth i ω) (candidate i ω) (baseline i ω) ∂P = populationWinRate)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r)) fun i j =>
      IndepFun
        (fun ω => strictAbsoluteErrorWin
          (truth i ω) (candidate i ω) (baseline i ω))
        (fun ω => strictAbsoluteErrorWin
          (truth j ω) (candidate j ω) (baseline j ω)) P)
    (hsecond : ∀ i,
      ∫ ω, (strictAbsoluteErrorWin
        (truth i ω) (candidate i ω) (baseline i ω) -
          populationWinRate) ^ 2 ∂P ≤ γ) :
    P {ω | ¬ EmpiricalWinRateClaim threshold
      (fun i => truth i ω) (fun i => candidate i ω)
      (fun i => baseline i ω)} ≤
      ENNReal.ofReal ((γ / r) / ε ^ 2) := by
  have htail := measure_empiricalWinFraction_deviation_gt_le
    P hr truth candidate baseline populationWinRate γ ε hε
    hL2 hmean hindep hsecond
  apply le_trans (measure_mono ?_) htail
  intro ω hfail
  change ¬ EmpiricalWinRateClaim threshold
    (fun i => truth i ω) (fun i => candidate i ω)
    (fun i => baseline i ω) at hfail
  by_contra hnot
  have hnot' : ¬ ε < abs (
      empiricalWinFraction (fun i => truth i ω) (fun i => candidate i ω)
        (fun i => baseline i ω) - populationWinRate) := by
    exact hnot
  have hdev : EmpiricalWinFractionDeviation
      (fun i => truth i ω) (fun i => candidate i ω)
      (fun i => baseline i ω) populationWinRate ε := by
    unfold EmpiricalWinFractionDeviation
    exact not_lt.mp hnot'
  exact hfail (empiricalWinRateClaim_of_deviation
    threshold populationWinRate ε
    (fun i => truth i ω) (fun i => candidate i ω)
    (fun i => baseline i ω) hdev hmargin)

end DkpsQuench2026.Paper.TheoryPractice
