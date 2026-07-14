/-
DKPS / Quench theory--practice correspondence layer.

The Quench paper intentionally proves and evaluates different estimators and
claim shapes:

* theory: tie-averaged nearest-neighbor regression, population MSE, eventual
  high-probability query efficiency;
* practice: clipped ordinary least squares, finite empirical MAE, and finite
  replicate or dataset-level comparisons, sometimes across different query
  budgets.

This file gives those objects stable Lean names without identifying them.  It
also proves the exact bridge justified by the paper's clipping step: when the
true score lies in `[0,1]`, clipping a prediction to `[0,1]` cannot increase its
absolute or squared error.

Stable symbolic anchors exposed here include:

* `DkpsQuench2026.Paper.TheoryPractice.theoreticalNearestNeighbor`
* `DkpsQuench2026.Paper.TheoryPractice.practicalOLS`
* `DkpsQuench2026.Paper.TheoryPractice.PopulationMSEQueryEfficiency`
* `DkpsQuench2026.Paper.TheoryPractice.EmpiricalCrossBudgetMAEClaim`
* `DkpsQuench2026.Paper.TheoryPractice.EmpiricalWinRateClaim`
* `DkpsQuench2026.Paper.TheoryPractice.abs_clipUnit_sub_le`
* `DkpsQuench2026.Paper.TheoryPractice.sqLoss_clipUnit_le`
* `DkpsQuench2026.Paper.TheoryPractice.empiricalMAE_clipUnit_le`
* `DkpsQuench2026.Paper.TheoryPractice.empiricalMSE_clipUnit_le`
-/
import DkpsQuench2026.Paper.QueryEfficiency
import DkpsQuench2026.Paper.OLSQueryEfficiency

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
variable {d : ℕ}
variable {Ω : Type w} [MeasurableSpace Ω]

/-! ## Stable estimator anchors -/

/-- Stable paper-facing name for the full benchmark score. -/
def fullBenchmarkScore
    (score : Model Q X → Finset Q → ℝ) (Qstar : Finset Q) :
    Model Q X → ℝ :=
  yFull score Qstar

/-- Stable paper-facing name for the direct subset-score baseline. -/
def subsetScoreBaseline
    (score : Model Q X → Finset Q → ℝ) (Qsub : Finset Q) :
    Model Q X → ℝ :=
  yQ score Qsub

/-- Stable name for the estimator proved query-efficient in the paper-facing
nearest-neighbor theory. -/
noncomputable def theoreticalNearestNeighbor
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (n : ℕ) (ω : Ω) (f : Model Q X) : ℝ :=
  yNNTieAverage_paper ψHat f_ref score Qstar Qsub n ω f

/-- Stable name for the ordinary-least-squares estimator used by the empirical
method and formalized under its additional affine-risk assumptions. -/
def practicalOLS
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (fit : ∀ n ω, OLS.OLSFit
      (fun i => ψHat n ω Qsub (f_ref n ω i))
      (fun i => score (f_ref n ω i) Qstar))
    (n : ℕ) (ω : Ω) (f : Model Q X) : ℝ :=
  OLS.yOLS_paper ψHat f_ref score Qstar Qsub fit n ω f

/-! ## Distinct claim shapes -/

/-- The population-MSE, eventual high-probability claim shape used by the
paper's theory and by the OLS risk-gap theorem.

This definition does not specify an estimator.  Supplying
`theoreticalNearestNeighbor` recovers the theoretical claim shape; supplying
`practicalOLS` requires the additional OLS assumptions proved in
`OLSQueryEfficiency`. -/
def PopulationMSEQueryEfficiency
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (truth : Model Q X → ℝ)
    (candidate baseline : ℕ → Ω → Model Q X → ℝ) : Prop :=
  HighProbQQueryEfficient (Q := Q) (X := X)
    μ hμ Pf sqLoss truth candidate baseline

/-- Absolute-error loss used by the empirical MAE evaluation. -/
def absLoss (prediction truth : ℝ) : ℝ :=
  |prediction - truth|

/-- Arithmetic mean of a finite family of real values.

At `n = 0` this is defined to be zero through the convention `0⁻¹ = 0`. -/
def empiricalMean {n : ℕ} (value : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, value i

/-- Finite empirical mean absolute error. -/
def empiricalMAE {n : ℕ}
    (truth prediction : Fin n → ℝ) : ℝ :=
  empiricalMean fun i => absLoss (prediction i) (truth i)

/-- Finite empirical mean squared error. -/
def empiricalMSE {n : ℕ}
    (truth prediction : Fin n → ℝ) : ℝ :=
  empiricalMean fun i => sqLoss (prediction i) (truth i)

/-- Indicator that the candidate has strictly smaller absolute error than the
baseline on one finite evaluation unit. -/
def strictAbsoluteErrorWin
    (truth candidate baseline : ℝ) : ℝ :=
  if absLoss candidate truth < absLoss baseline truth then 1 else 0

/-- Fraction of finite evaluation units on which the candidate has strictly
smaller absolute error than the baseline. -/
def empiricalWinFraction {n : ℕ}
    (truth candidate baseline : Fin n → ℝ) : ℝ :=
  empiricalMean fun i =>
    strictAbsoluteErrorWin (truth i) (candidate i) (baseline i)

/-- Finite empirical MAE comparison.  The query subsets are deliberately not
arguments: they belong to the construction of `candidate` and `baseline`.
Keeping this proposition purely numerical makes explicit that it is not the
same proposition as `PopulationMSEQueryEfficiency`. -/
def EmpiricalCrossBudgetMAEClaim {n : ℕ}
    (truth candidate baseline : Fin n → ℝ) : Prop :=
  empiricalMAE truth candidate ≤ empiricalMAE truth baseline

/-- Finite strict-win-rate comparison, such as the practical claim that the
candidate wins on at least 65 percent of replicates. -/
def EmpiricalWinRateClaim {n : ℕ}
    (threshold : ℝ)
    (truth candidate baseline : Fin n → ℝ) : Prop :=
  threshold ≤ empiricalWinFraction truth candidate baseline

/-- A symbolic witness that the candidate uses fewer queries than its baseline.
The population theorem does not derive this inequality; the practical
cross-budget evaluation records it separately. -/
structure CrossBudgetQuerySets (Q : Type u) [DecidableEq Q] where
  candidateQueries : Finset Q
  baselineQueries : Finset Q
  fewerQueries : candidateQueries.card < baselineQueries.card

/-! ## Clipping bridge -/

/-- Clip a real prediction to the benchmark-score interval `[0,1]`. -/
def clipUnit (x : ℝ) : ℝ :=
  min 1 (max 0 x)

@[simp] theorem clipUnit_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    clipUnit x = 0 := by
  simp [clipUnit, max_eq_left hx]

@[simp] theorem clipUnit_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    clipUnit x = 1 := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  simp [clipUnit, max_eq_right hx0, min_eq_left hx]

@[simp] theorem clipUnit_eq_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    clipUnit x = x := by
  simp [clipUnit, max_eq_right hx0, min_eq_right hx1]

/-- Clipping to `[0,1]` cannot increase absolute error when the true score lies
in `[0,1]`. -/
theorem abs_clipUnit_sub_le
    (prediction truth : ℝ)
    (htruth0 : 0 ≤ truth) (htruth1 : truth ≤ 1) :
    |clipUnit prediction - truth| ≤ |prediction - truth| := by
  by_cases hlow : prediction ≤ 0
  · rw [clipUnit_of_nonpos hlow]
    rw [abs_of_nonpos (by linarith : 0 - truth ≤ 0)]
    rw [abs_of_nonpos (by linarith : prediction - truth ≤ 0)]
    linarith
  · have hprediction0 : 0 ≤ prediction := le_of_not_ge hlow
    by_cases hhigh : 1 ≤ prediction
    · rw [clipUnit_of_one_le hhigh]
      rw [abs_of_nonneg (by linarith : 0 ≤ 1 - truth)]
      rw [abs_of_nonneg (by linarith : 0 ≤ prediction - truth)]
      linarith
    · have hprediction1 : prediction ≤ 1 := le_of_not_ge hhigh
      rw [clipUnit_eq_self hprediction0 hprediction1]

/-- Clipping to `[0,1]` cannot increase squared error when the true score lies
in `[0,1]`. -/
theorem sqLoss_clipUnit_le
    (prediction truth : ℝ)
    (htruth0 : 0 ≤ truth) (htruth1 : truth ≤ 1) :
    sqLoss (clipUnit prediction) truth ≤ sqLoss prediction truth := by
  have habs := abs_clipUnit_sub_le prediction truth htruth0 htruth1
  have hpow := pow_le_pow_left₀
    (abs_nonneg (clipUnit prediction - truth)) habs 2
  simpa [sqLoss] using hpow

/-- Pointwise clipping cannot increase finite empirical MAE. -/
theorem empiricalMAE_clipUnit_le {n : ℕ}
    (truth prediction : Fin n → ℝ)
    (htruth : ∀ i, 0 ≤ truth i ∧ truth i ≤ 1) :
    empiricalMAE truth (fun i => clipUnit (prediction i)) ≤
      empiricalMAE truth prediction := by
  unfold empiricalMAE empiricalMean
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro i _hi
    exact abs_clipUnit_sub_le
      (prediction i) (truth i) (htruth i).1 (htruth i).2
  · positivity

/-- Pointwise clipping cannot increase finite empirical MSE. -/
theorem empiricalMSE_clipUnit_le {n : ℕ}
    (truth prediction : Fin n → ℝ)
    (htruth : ∀ i, 0 ≤ truth i ∧ truth i ≤ 1) :
    empiricalMSE truth (fun i => clipUnit (prediction i)) ≤
      empiricalMSE truth prediction := by
  unfold empiricalMSE empiricalMean
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro i _hi
    exact sqLoss_clipUnit_le
      (prediction i) (truth i) (htruth i).1 (htruth i).2
  · positivity


/-! ## Finite MSE-to-MAE bridge -/

/-- Finite empirical MAE is nonnegative. -/
theorem empiricalMAE_nonneg {n : ℕ}
    (truth prediction : Fin n → ℝ) :
    0 ≤ empiricalMAE truth prediction := by
  unfold empiricalMAE empiricalMean absLoss
  positivity

/-- Finite empirical MSE is nonnegative. -/
theorem empiricalMSE_nonneg {n : ℕ}
    (truth prediction : Fin n → ℝ) :
    0 ≤ empiricalMSE truth prediction := by
  unfold empiricalMSE empiricalMean sqLoss
  positivity

/-- On a nonempty finite evaluation sample, empirical MAE squared is bounded
by empirical MSE.  This is the exact finite Cauchy--Schwarz bridge between the
paper theorem's squared-error language and the card's absolute-error language. -/
theorem empiricalMAE_sq_le_empiricalMSE {n : ℕ}
    (hn : 0 < n)
    (truth prediction : Fin n → ℝ) :
    (empiricalMAE truth prediction) ^ 2 ≤
      empiricalMSE truth prediction := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => |prediction i - truth i|)
  have hsum :
      (∑ i, |prediction i - truth i|) ^ 2 ≤
        (n : ℝ) * ∑ i, (prediction i - truth i) ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin, sq_abs] using hcs
  unfold empiricalMAE empiricalMSE empiricalMean absLoss sqLoss
  calc
    ((n : ℝ)⁻¹ * ∑ i, |prediction i - truth i|) ^ 2
        = ((n : ℝ)⁻¹) ^ 2 *
            (∑ i, |prediction i - truth i|) ^ 2 := by ring
    _ ≤ ((n : ℝ)⁻¹) ^ 2 *
          ((n : ℝ) * ∑ i, (prediction i - truth i) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (n : ℝ)⁻¹ * ∑ i, (prediction i - truth i) ^ 2 := by
      field_simp [ne_of_gt hnR]

/-- Equivalent square-root form of the finite MSE-to-MAE bridge. -/
theorem empiricalMAE_le_sqrt_empiricalMSE {n : ℕ}
    (hn : 0 < n)
    (truth prediction : Fin n → ℝ) :
    empiricalMAE truth prediction ≤
      Real.sqrt (empiricalMSE truth prediction) := by
  exact Real.le_sqrt_of_sq_le
    (empiricalMAE_sq_le_empiricalMSE hn truth prediction)

/-- A useful sufficient condition for the finite cross-budget MAE card:
if the candidate's empirical MSE is strictly below the square of the
baseline's empirical MAE, then the candidate has strictly smaller empirical
MAE. -/
theorem empiricalMAE_lt_of_mse_lt_baseline_mae_sq {n : ℕ}
    (hn : 0 < n)
    (truth candidate baseline : Fin n → ℝ)
    (hmargin : empiricalMSE truth candidate <
      (empiricalMAE truth baseline) ^ 2) :
    empiricalMAE truth candidate < empiricalMAE truth baseline := by
  have hsq := empiricalMAE_sq_le_empiricalMSE hn truth candidate
  have hc0 := empiricalMAE_nonneg truth candidate
  have hb0 := empiricalMAE_nonneg truth baseline
  nlinarith

/-- Proposition-level version of
`empiricalMAE_lt_of_mse_lt_baseline_mae_sq`. -/
theorem empiricalCrossBudgetMAEClaim_of_mse_margin {n : ℕ}
    (hn : 0 < n)
    (truth candidate baseline : Fin n → ℝ)
    (hmargin : empiricalMSE truth candidate <
      (empiricalMAE truth baseline) ^ 2) :
    EmpiricalCrossBudgetMAEClaim truth candidate baseline := by
  unfold EmpiricalCrossBudgetMAEClaim
  exact (empiricalMAE_lt_of_mse_lt_baseline_mae_sq
    hn truth candidate baseline hmargin).le

/-! ## MSE does not determine replicate-win rate -/

/-- Truth values for a three-replicate counterexample. -/
def mseWinCounterexampleTruth (_i : Fin 3) : ℝ := 0

/-- The candidate predicts `2 / 5` on every replicate. -/
def mseWinCounterexampleCandidate (_i : Fin 3) : ℝ := 2 / 5

/-- The baseline is exact on two replicates and predicts `1` on one. -/
def mseWinCounterexampleBaseline (i : Fin 3) : ℝ :=
  if i.val = 2 then 1 else 0

/-- In the counterexample, the candidate has empirical MSE exactly `4 / 25`. -/
theorem mseWinCounterexample_candidate_mse :
    empiricalMSE mseWinCounterexampleTruth mseWinCounterexampleCandidate = 4 / 25 := by
  norm_num [empiricalMSE, empiricalMean, sqLoss,
    mseWinCounterexampleTruth, mseWinCounterexampleCandidate,
    Fin.sum_univ_succ]

/-- In the counterexample, the baseline has empirical MSE exactly `1 / 3`. -/
theorem mseWinCounterexample_baseline_mse :
    empiricalMSE mseWinCounterexampleTruth mseWinCounterexampleBaseline = 1 / 3 := by
  norm_num [empiricalMSE, empiricalMean, sqLoss,
    mseWinCounterexampleTruth, mseWinCounterexampleBaseline,
    Fin.sum_univ_succ]
  native_decide

/-- In the counterexample, the candidate wins on only one of three replicates. -/
theorem mseWinCounterexample_winFraction :
    empiricalWinFraction mseWinCounterexampleTruth
      mseWinCounterexampleCandidate mseWinCounterexampleBaseline = 1 / 3 := by
  norm_num [empiricalWinFraction, empiricalMean, strictAbsoluteErrorWin,
    absLoss, mseWinCounterexampleTruth, mseWinCounterexampleCandidate,
    mseWinCounterexampleBaseline, Fin.sum_univ_succ]
  have hfilter :
      ({x : Fin 3 | (2 / 5 : ℝ) <
        |if x.val = 2 then (1 : ℝ) else 0|} : Finset (Fin 3)) =
        ({2} : Finset (Fin 3)) := by
    ext i
    fin_cases i <;> norm_num [Fin.ext_iff]
  rw [hfilter]
  simp

/-- Lower empirical MSE does not imply winning on a majority of individual
replicates.  A rare large baseline error can dominate MSE while the baseline
still wins pointwise most of the time. -/
theorem lowerMSE_not_sufficient_for_majorityWins :
    empiricalMSE mseWinCounterexampleTruth mseWinCounterexampleCandidate <
      empiricalMSE mseWinCounterexampleTruth mseWinCounterexampleBaseline ∧
    ¬ EmpiricalWinRateClaim (1 / 2)
      mseWinCounterexampleTruth
      mseWinCounterexampleCandidate
      mseWinCounterexampleBaseline := by
  rw [mseWinCounterexample_candidate_mse,
    mseWinCounterexample_baseline_mse]
  constructor
  · norm_num
  · unfold EmpiricalWinRateClaim
    rw [mseWinCounterexample_winFraction]
    norm_num

end DkpsQuench2026.Paper.TheoryPractice
