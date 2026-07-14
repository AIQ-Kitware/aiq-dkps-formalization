/-
Finite-evaluation and replicate-win bridges for Quench/MAGNET.

These statements keep three layers distinct:

* population risk of the trained estimator;
* finite empirical MAE measured by an evaluation card;
* fraction of individual trials on which the estimator wins.

The file proves the exact margin arithmetic needed to pass between the layers
once concentration/deviation premises are available, and records explicit
counterexamples to invalid converse implications.
-/
import DkpsQuench2026.Paper.OLSPerturbation

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory

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

/-! ## Population MAE to finite measured MAE -/

/-- A measured finite MAE is within `ε` of a specified population value. -/
def EmpiricalMAEDeviation {r : ℕ}
    (truth prediction : Fin r → ℝ) (population ε : ℝ) : Prop :=
  |empiricalMAE truth prediction - population| ≤ ε

/-- A strict population-MAE margin survives finite evaluation whenever the two
empirical deviations fit inside the margin. -/
theorem empiricalCrossBudgetMAEClaim_of_deviations {r : ℕ}
    (truth candidate baseline : Fin r → ℝ)
    (candidatePopulation baselinePopulation candidateError baselineError : ℝ)
    (hcandidate : EmpiricalMAEDeviation truth candidate
      candidatePopulation candidateError)
    (hbaseline : EmpiricalMAEDeviation truth baseline
      baselinePopulation baselineError)
    (hmargin : candidatePopulation + candidateError + baselineError ≤
      baselinePopulation) :
    EmpiricalCrossBudgetMAEClaim truth candidate baseline := by
  have hc := (abs_le.mp hcandidate).2
  have hb := (abs_le.mp hbaseline).1
  unfold EmpiricalCrossBudgetMAEClaim
  linarith

/-- High-probability simultaneous finite-MAE approximation for candidate and
baseline. -/
def HighProbEmpiricalMAEApproximation {r : ℕ}
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (truth candidate baseline : ℕ → Ω → Fin r → ℝ)
    (candidatePopulation baselinePopulation : ℕ → Ω → ℝ)
    (candidateError baselineError : ℝ) : Prop :=
  HighProbAtTop μ hμ (fun k => {ω |
    EmpiricalMAEDeviation (truth k ω) (candidate k ω)
      (candidatePopulation k ω) candidateError ∧
    EmpiricalMAEDeviation (truth k ω) (baseline k ω)
      (baselinePopulation k ω) baselineError})

/-- Population MAE superiority plus high-probability finite-sample deviations
implies the card's finite empirical MAE comparison with high probability. -/
theorem highProb_empiricalCrossBudgetMAEClaim_of_deviations {r : ℕ}
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (truth candidate baseline : ℕ → Ω → Fin r → ℝ)
    (candidatePopulation baselinePopulation : ℕ → Ω → ℝ)
    (candidateError baselineError : ℝ)
    (happrox : HighProbEmpiricalMAEApproximation μ hμ
      truth candidate baseline candidatePopulation baselinePopulation
      candidateError baselineError)
    (hmargin : ∀ k ω,
      candidatePopulation k ω + candidateError + baselineError ≤
        baselinePopulation k ω) :
    HighProbAtTop μ hμ (fun k => {ω |
      EmpiricalCrossBudgetMAEClaim
        (truth k ω) (candidate k ω) (baseline k ω)}) := by
  apply HighProbAtTop.mono happrox
  intro k ω hω
  exact empiricalCrossBudgetMAEClaim_of_deviations
    (truth k ω) (candidate k ω) (baseline k ω)
    (candidatePopulation k ω) (baselinePopulation k ω)
    candidateError baselineError hω.1 hω.2 (hmargin k ω)

/-- Algebraic margin bridge used when the available theoretical
control is in MSE but the finite card is evaluated in MAE. -/
theorem mae_add_margin_le_of_mse_le_sub_sq
    (candidateMAE baselineMAE candidateMSE margin : ℝ)
    (hcandidate0 : 0 ≤ candidateMAE)
    (hremaining0 : 0 ≤ baselineMAE - margin)
    (hsq : candidateMAE ^ 2 ≤ candidateMSE)
    (hmse : candidateMSE ≤ (baselineMAE - margin) ^ 2) :
    candidateMAE + margin ≤ baselineMAE := by
  nlinarith

/-- Direct theory-to-card arithmetic: an MSE upper bound below the squared
MAE margin, together with finite MAE deviation certificates, proves the
empirical cross-budget MAE card. -/
theorem empiricalCrossBudgetMAEClaim_of_populationMSEMargin {r : ℕ}
    (truth candidate baseline : Fin r → ℝ)
    (candidatePopulationMAE baselinePopulationMAE candidatePopulationMSE : ℝ)
    (candidateError baselineError : ℝ)
    (hcandidateMAE0 : 0 ≤ candidatePopulationMAE)
    (hremaining0 :
      0 ≤ baselinePopulationMAE - (candidateError + baselineError))
    (hMAEMSE : candidatePopulationMAE ^ 2 ≤ candidatePopulationMSE)
    (hMSEMargin : candidatePopulationMSE ≤
      (baselinePopulationMAE - (candidateError + baselineError)) ^ 2)
    (hcandidate : EmpiricalMAEDeviation truth candidate
      candidatePopulationMAE candidateError)
    (hbaseline : EmpiricalMAEDeviation truth baseline
      baselinePopulationMAE baselineError) :
    EmpiricalCrossBudgetMAEClaim truth candidate baseline := by
  have hmargin : candidatePopulationMAE + candidateError + baselineError ≤
      baselinePopulationMAE := by
    have h := mae_add_margin_le_of_mse_le_sub_sq
      candidatePopulationMAE baselinePopulationMAE candidatePopulationMSE
      (candidateError + baselineError)
      hcandidateMAE0 hremaining0 hMAEMSE hMSEMargin
    linarith
  exact empiricalCrossBudgetMAEClaim_of_deviations
    truth candidate baseline candidatePopulationMAE baselinePopulationMAE
    candidateError baselineError hcandidate hbaseline hmargin

/-! ## Exact finite win-count interpretation -/

/-- Number of evaluation units on which the candidate has strictly smaller
absolute error than the baseline. -/
def strictWinCount {r : ℕ}
    (truth candidate baseline : Fin r → ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin r)).filter fun i =>
    absLoss (candidate i) (truth i) < absLoss (baseline i) (truth i)).card

/-- The numerical win fraction is exactly the strict-win count divided by the
number of evaluation units. -/
theorem empiricalWinFraction_eq_strictWinCount {r : ℕ}
    (truth candidate baseline : Fin r → ℝ) :
    empiricalWinFraction truth candidate baseline =
      (r : ℝ)⁻¹ * (strictWinCount truth candidate baseline : ℝ) := by
  unfold empiricalWinFraction empiricalMean strictWinCount
  congr 1
  unfold strictAbsoluteErrorWin
  rw [← Finset.sum_filter]
  simp

/-- For the practical 32-replicate threshold `0.65 = 13/20`, passing the card is
exactly the requirement that the candidate win at least 21 replicates. -/
theorem empiricalWinRateClaim_65_iff_twentyOne_le_strictWinCount
    (truth candidate baseline : Fin 32 → ℝ) :
    EmpiricalWinRateClaim (13 / 20 : ℝ) truth candidate baseline ↔
      21 ≤ strictWinCount truth candidate baseline := by
  rw [EmpiricalWinRateClaim, empiricalWinFraction_eq_strictWinCount]
  constructor
  · intro h
    by_contra hcount
    have hle : strictWinCount truth candidate baseline ≤ 20 := by omega
    have hleReal :
        (strictWinCount truth candidate baseline : ℝ) ≤ 20 := by
      exact_mod_cast hle
    norm_num at h
    linarith
  · intro hcount
    have hcountReal :
        (21 : ℝ) ≤ strictWinCount truth candidate baseline := by
      exact_mod_cast hcount
    norm_num
    linarith

/-! ## Population win probability to finite replicate fraction -/

/-- A finite observed win fraction is within `ε` of a target population win
probability. -/
def EmpiricalWinFractionDeviation {r : ℕ}
    (truth candidate baseline : Fin r → ℝ)
    (populationWinRate ε : ℝ) : Prop :=
  |empiricalWinFraction truth candidate baseline - populationWinRate| ≤ ε

/-- A population win-rate margin survives a finite replicate evaluation. -/
theorem empiricalWinRateClaim_of_deviation {r : ℕ}
    (threshold populationWinRate ε : ℝ)
    (truth candidate baseline : Fin r → ℝ)
    (hdev : EmpiricalWinFractionDeviation truth candidate baseline
      populationWinRate ε)
    (hmargin : threshold + ε ≤ populationWinRate) :
    EmpiricalWinRateClaim threshold truth candidate baseline := by
  have hlow := (abs_le.mp hdev).1
  unfold EmpiricalWinRateClaim
  linarith

/-- High-probability finite-replicate approximation of a population win rate. -/
def HighProbEmpiricalWinApproximation {r : ℕ}
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (truth candidate baseline : ℕ → Ω → Fin r → ℝ)
    (populationWinRate : ℕ → Ω → ℝ) (ε : ℝ) : Prop :=
  HighProbAtTop μ hμ (fun k => {ω |
    EmpiricalWinFractionDeviation
      (truth k ω) (candidate k ω) (baseline k ω)
      (populationWinRate k ω) ε})

/-- Population win probability above the threshold by a concentration margin
implies the finite replicate-win card with high probability. -/
theorem highProb_empiricalWinRateClaim_of_deviation {r : ℕ}
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (threshold ε : ℝ)
    (truth candidate baseline : ℕ → Ω → Fin r → ℝ)
    (populationWinRate : ℕ → Ω → ℝ)
    (happrox : HighProbEmpiricalWinApproximation μ hμ
      truth candidate baseline populationWinRate ε)
    (hmargin : ∀ k ω, threshold + ε ≤ populationWinRate k ω) :
    HighProbAtTop μ hμ (fun k => {ω |
      EmpiricalWinRateClaim threshold
        (truth k ω) (candidate k ω) (baseline k ω)}) := by
  apply HighProbAtTop.mono happrox
  intro k ω hω
  exact empiricalWinRateClaim_of_deviation
    threshold (populationWinRate k ω) ε
    (truth k ω) (candidate k ω) (baseline k ω)
    hω (hmargin k ω)

/-- Population mass of models on which the candidate has strictly smaller
absolute error than the baseline. -/
noncomputable def populationWinMass
    (Pf : Measure (Model Q X))
    (truth candidate baseline : Model Q X → ℝ) : ENNReal :=
  Pf {f | absLoss (candidate f) (truth f) <
    absLoss (baseline f) (truth f)}

/-- Population mass on which the baseline error is separated from zero by more
than `η`. -/
noncomputable def baselineMarginMass
    (Pf : Measure (Model Q X))
    (truth baseline : Model Q X → ℝ) (η : ℝ) : ENNReal :=
  Pf {f | η < absLoss (baseline f) (truth f)}

/-- Uniform candidate accuracy makes every model with baseline error greater
than `η` a strict candidate win. -/
theorem baselineMarginMass_le_populationWinMass
    (Pf : Measure (Model Q X))
    (truth candidate baseline : Model Q X → ℝ)
    (η : ℝ)
    (hcandidate : ∀ f, absLoss (candidate f) (truth f) ≤ η) :
    baselineMarginMass Pf truth baseline η ≤
      populationWinMass Pf truth candidate baseline := by
  unfold baselineMarginMass populationWinMass
  apply measure_mono
  intro f hf
  exact lt_of_le_of_lt (hcandidate f) hf

/-- High-probability uniform convergence of candidate absolute error. -/
def HighProbUniformAbsoluteAccuracy
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (truth : Model Q X → ℝ)
    (candidate : ℕ → Ω → Model Q X → ℝ)
    (η : ℝ) : Prop :=
  HighProbAtTop μ hμ (fun k => {ω |
    ∀ f, absLoss (candidate k ω f) (truth f) ≤ η})

/-- Uniform consistency supplies a lower bound on the population pointwise-win
probability in terms of the baseline's nonzero-error mass. -/
theorem highProb_populationWinMass_of_uniformAccuracy
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X))
    (truth baseline : Model Q X → ℝ)
    (candidate : ℕ → Ω → Model Q X → ℝ)
    (η : ℝ)
    (haccuracy : HighProbUniformAbsoluteAccuracy μ hμ truth candidate η) :
    HighProbAtTop μ hμ (fun k => {ω |
      baselineMarginMass Pf truth baseline η ≤
        populationWinMass Pf truth (candidate k ω) baseline}) := by
  apply HighProbAtTop.mono haccuracy
  intro k ω hω
  exact baselineMarginMass_le_populationWinMass
    Pf truth (candidate k ω) baseline η hω

/-! ## Explicit boundaries and non-implications -/

/-- Same-budget superiority does not logically imply superiority against a
stronger, larger-budget baseline.  The three numbers represent candidate risk,
same-budget baseline risk, and larger-budget baseline risk. -/
theorem sameBudgetComparison_not_crossBudgetComparison :
    (1 / 2 : ℝ) ≤ 1 ∧ ¬ (1 / 2 : ℝ) ≤ 0 := by
  norm_num

/-- Constant affine approximation used to show that exact affine realizability
is sufficient but not necessary for an affine-risk gap. -/
def threePointAffineApproximation (_i : Fin 3) : ℝ := 2 / 3

/-- Zero baseline for the same example. -/
def threePointZeroBaseline (_i : Fin 3) : ℝ := 0

theorem threePointAffineApproximation_mse :
    empiricalMSE OLS.threePointTarget threePointAffineApproximation = 2 / 9 := by
  norm_num [empiricalMSE, empiricalMean, sqLoss,
    OLS.threePointTarget, OLS.threePointFeature,
    threePointAffineApproximation, Fin.sum_univ_succ]

theorem threePointZeroBaseline_mse :
    empiricalMSE OLS.threePointTarget threePointZeroBaseline = 2 / 3 := by
  norm_num [empiricalMSE, empiricalMean, sqLoss,
    OLS.threePointTarget, OLS.threePointFeature,
    threePointZeroBaseline, Fin.sum_univ_succ]

/-- Exact affine realizability is not necessary: the nonlinear Lipschitz target
has a strict affine-risk advantage over a sufficiently poor baseline. -/
theorem affineRiskGap_without_affineRealizability :
    (¬ ∃ a b : ℝ, ∀ i : Fin 3,
      OLS.threePointTarget i = a + b * OLS.threePointFeature i) ∧
    empiricalMSE OLS.threePointTarget threePointAffineApproximation <
      empiricalMSE OLS.threePointTarget threePointZeroBaseline := by
  constructor
  · exact OLS.threePointTarget_not_affine
  · rw [threePointAffineApproximation_mse, threePointZeroBaseline_mse]
    norm_num

/-- Full-population data for a finite-batch reversal example. -/
def finiteReversalTruth (_i : Fin 3) : ℝ := 0

def finiteReversalCandidate (i : Fin 3) : ℝ :=
  if i.val = 2 then 1 else 0

def finiteReversalBaseline (_i : Fin 3) : ℝ := 1 / 2

/-- A one-element evaluation batch selecting the exceptional third point. -/
def finiteReversalSampleTruth (_i : Fin 1) : ℝ := 0

def finiteReversalSampleCandidate (_i : Fin 1) : ℝ := 1

def finiteReversalSampleBaseline (_i : Fin 1) : ℝ := 1 / 2

/-- Better full finite-population MAE does not force better MAE on every finite
sample.  Concentration or a deterministic deviation certificate is necessary. -/
theorem populationMAESuperiority_not_everyFiniteBatch :
    empiricalMAE finiteReversalTruth finiteReversalCandidate <
      empiricalMAE finiteReversalTruth finiteReversalBaseline ∧
    empiricalMAE finiteReversalSampleTruth finiteReversalSampleCandidate >
      empiricalMAE finiteReversalSampleTruth finiteReversalSampleBaseline := by
  constructor
  · norm_num [empiricalMAE, empiricalMean, absLoss,
      finiteReversalTruth, finiteReversalCandidate,
      finiteReversalBaseline, Fin.sum_univ_succ]
  · norm_num [empiricalMAE, empiricalMean, absLoss,
      finiteReversalSampleTruth, finiteReversalSampleCandidate,
      finiteReversalSampleBaseline, Fin.sum_univ_succ]

end DkpsQuench2026.Paper.TheoryPractice
