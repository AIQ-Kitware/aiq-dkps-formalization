/-
DKPS / Quench theory--practice bridge for ordinary least squares.

The paper deliberately separates two estimators:

* Section 3 proves query efficiency for a local nearest-neighbor estimator;
* Section 4 evaluates a clipped ordinary-least-squares (OLS) regressor.

Lipschitz regularity and support/coverage are enough for the local estimator,
but they do not force the full benchmark score to be affine in the DKPS
coordinates.  This file records the extra assumptions under which the practical
OLS estimator is query-efficient, including the cross-budget comparison used by
the MAGNET evaluation card.

Stable paper/practice anchors exposed by this module:

* `DkpsQuench2026.Paper.OLS.AffineCoefficients`
* `DkpsQuench2026.Paper.OLS.OLSFit`
* `DkpsQuench2026.Paper.OLS.HighProbAffineRiskCompetitive`
* `DkpsQuench2026.Paper.OLS.highProb_queryEfficient_crossBudget_of_affineRiskGap`
* `DkpsQuench2026.Paper.OLS.highProb_queryEfficient_crossBudget_of_affineRealizable`
* `DkpsQuench2026.Paper.OLS.lipschitz_not_sufficient_for_affineRealizability`

The principal theorem does not pretend that OLS follows from the hypotheses of
Theorem 2.  It assumes that fitted OLS asymptotically reaches the risk of an
affine witness and that this affine risk is strictly below the selected
sample-score baseline.  The second theorem specializes this to exact affine
realizability and a positive baseline risk.
-/
import DkpsQuench2026.Paper.Theorem2

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
  RealInnerProductSpace InnerProductSpace
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

namespace DkpsQuench2026.Paper.OLS

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}
variable {Ω : Type w} [MeasurableSpace Ω]

/-- Intercept and slope of an affine predictor on a `d`-dimensional DKPS.

This is the mathematical parameter object corresponding to the coefficient
vector learned by the practical linear regressor. -/
structure AffineCoefficients (d : ℕ) where
  intercept : ℝ
  slope : Vec d

/-- Evaluate an affine score predictor at one perspective vector. -/
def affinePredict (θ : AffineCoefficients d) (x : Vec d) : ℝ :=
  θ.intercept + ⟪θ.slope, x⟫_ℝ

/-- The affine model-score predictor induced by a perspective map. -/
def affineModel
    (θ : AffineCoefficients d) (ψ : Model Q X → Vec d) : Model Q X → ℝ :=
  fun f => affinePredict θ (ψ f)

/-- Unnormalized finite-sample squared-error objective minimized by OLS.

The normalization by the sample count is intentionally omitted: it does not
change the minimizers and avoids a special case at sample size zero. -/
def empiricalSquaredError {n : ℕ}
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (θ : AffineCoefficients d) : ℝ :=
  ∑ i, sqLoss (affinePredict θ (x i)) (target i)

/-- A coefficient vector is an ordinary-least-squares fit when it globally
minimizes the finite-sample squared-error objective. -/
def IsOLSFit {n : ℕ}
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (θ : AffineCoefficients d) : Prop :=
  ∀ θ' : AffineCoefficients d,
    empiricalSquaredError x target θ ≤ empiricalSquaredError x target θ'

/-- A finite OLS result, packaged with its least-squares optimality proof.

This structure is the formal seam at which a concrete solver or an exact
linear-algebra construction can later be connected.  The query-efficiency
results below therefore concern actual least-squares minimizers, not arbitrary
linear predictors. -/
structure OLSFit {n : ℕ}
    (x : Fin n → Vec d) (target : Fin n → ℝ) where
  coeff : AffineCoefficients d
  optimal : IsOLSFit x target coeff

/-- A design identifies affine coefficients when agreement on all design
points forces equality of the intercept and slope.

For the augmented design matrix `[1, x]`, this is the coordinate-free content
of full column rank. -/
def AffineIdentifyingDesign {n : ℕ} (x : Fin n → Vec d) : Prop :=
  ∀ θ θ' : AffineCoefficients d,
    (∀ i, affinePredict θ (x i) = affinePredict θ' (x i)) → θ = θ'

/-- On an affine-identifying design with exactly affine targets, every OLS fit
recovers the generating affine coefficients exactly. -/
theorem OLSFit.eq_of_affineTargets {n : ℕ}
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (θstar : AffineCoefficients d)
    (fit : OLSFit x target)
    (htarget : ∀ i, target i = affinePredict θstar (x i))
    (hidentify : AffineIdentifyingDesign x) :
    fit.coeff = θstar := by
  have hstar : empiricalSquaredError x target θstar = 0 := by
    unfold empiricalSquaredError
    apply Finset.sum_eq_zero
    intro i _hi
    rw [htarget i]
    simp [sqLoss]
  have hopt : empiricalSquaredError x target fit.coeff ≤ 0 := by
    exact (fit.optimal θstar).trans_eq hstar
  have hnonneg : 0 ≤ empiricalSquaredError x target fit.coeff := by
    unfold empiricalSquaredError
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum : empiricalSquaredError x target fit.coeff = 0 :=
    le_antisymm hopt hnonneg
  apply hidentify fit.coeff θstar
  intro i
  have hterm : sqLoss (affinePredict fit.coeff (x i)) (target i) = 0 := by
    have hall :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) =>
          sq_nonneg (affinePredict fit.coeff (x j) - target j))).mp
        (by simpa [empiricalSquaredError, sqLoss] using hsum)
    exact hall i (Finset.mem_univ i)
  have heq : affinePredict fit.coeff (x i) = target i := by
    dsimp [sqLoss] at hterm
    nlinarith
  exact heq.trans (htarget i)

/-- Predictor produced by fitting OLS to reference-model perspectives and
known full-benchmark scores, then evaluating the fit at a target perspective. -/
def fittedOLSPredictor
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (y : Model Q X → ℝ)
    (fit : ∀ n ω, OLSFit
      (fun i => ψHat n ω (f_ref n ω i))
      (fun i => y (f_ref n ω i)))
    (n : ℕ) (ω : Ω) (f : Model Q X) : ℝ :=
  affinePredict (fit n ω).coeff (ψHat n ω f)

/-- At one stage, exact perspectives, affine realizability, and an identifying
reference design force fitted OLS to equal the target on every model. -/
theorem fittedOLSPredictor_eq_target_of_exactAffine
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (y : Model Q X → ℝ)
    (fit : ∀ n ω, OLSFit
      (fun i => ψHat n ω (f_ref n ω i))
      (fun i => y (f_ref n ω i)))
    (θ : AffineCoefficients d)
    (n : ℕ) (ω : Ω)
    (halign : ∀ f, ψHat n ω f = ψ f)
    (hrealizable : ∀ f, y f = affineModel θ ψ f)
    (hidentify : AffineIdentifyingDesign
      (fun i => ψHat n ω (f_ref n ω i))) :
    fittedOLSPredictor ψHat f_ref y fit n ω = y := by
  have htarget : ∀ i,
      y (f_ref n ω i) =
        affinePredict θ (ψHat n ω (f_ref n ω i)) := by
    intro i
    rw [hrealizable (f_ref n ω i), affineModel, halign (f_ref n ω i)]
  have hcoeff : (fit n ω).coeff = θ :=
    OLSFit.eq_of_affineTargets
      (fun i => ψHat n ω (f_ref n ω i))
      (fun i => y (f_ref n ω i)) θ (fit n ω) htarget hidentify
  funext f
  rw [fittedOLSPredictor, hcoeff, halign f]
  exact (hrealizable f).symm

/-- Paper-shaped OLS estimator: fit on the estimated perspective induced by
`Qsub`, using reference models' full scores on `Qstar` as targets. -/
def yOLS_paper
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (fit : ∀ n ω, OLSFit
      (fun i => ψHat n ω Qsub (f_ref n ω i))
      (fun i => score (f_ref n ω i) Qstar))
    (n : ℕ) (ω : Ω) (f : Model Q X) : ℝ :=
  fittedOLSPredictor
    (fun n' ω' g => ψHat n' ω' Qsub g)
    f_ref (yFull score Qstar) fit n ω f

/-- The fitted predictor is eventually, with high probability, no worse than a
specified affine witness up to every positive tolerance.

For a statistically consistent OLS procedure, the natural witness is a
population-risk-minimizing affine predictor.  The definition is intentionally
slightly weaker: any affine witness with a strict risk advantage over the
baseline is sufficient. -/
def HighProbAffineRiskCompetitive
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (y : Model Q X → ℝ)
    (h : ℕ → Ω → Model Q X → ℝ)
    (ψ : Model Q X → Vec d)
    (θ : AffineCoefficients d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    HighProbAtTop μ hμ (fun n => {ω |
      MSE Pf y (h n ω) ≤ MSE Pf y (affineModel θ ψ) + ε})

/-- Generic risk-gap principle behind OLS query efficiency.

If an estimator asymptotically attains a fixed target risk and that target risk
is strictly below the baseline risk, then the estimator is eventually
query-efficient with high probability. -/
theorem highProbQQueryEfficient_of_mseAtMost_lt_baseline
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (y baseline : Model Q X → ℝ)
    (h : ℕ → Ω → Model Q X → ℝ)
    (targetRisk : ℝ)
    (h_atMost : ∀ ε : ℝ, 0 < ε →
      HighProbAtTop μ hμ (fun n => {ω |
        MSE Pf y (h n ω) ≤ targetRisk + ε}))
    (hgap : targetRisk < MSE Pf y baseline) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss y
      h (fun _ _ => baseline) := by
  unfold HighProbQQueryEfficient
  let ε : ℝ := (MSE Pf y baseline - targetRisk) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have htarget : targetRisk + ε ≤ MSE Pf y baseline := by
    dsimp [ε]
    linarith
  intro δ hδ
  obtain ⟨N, hN⟩ := h_atMost ε hε δ hδ
  refine ⟨N, ?_⟩
  intro n hn
  exact (hN n hn).trans (measure_mono (by
    intro ω hω
    exact hω.trans htarget))

/-- OLS query efficiency from the two genuinely additional assumptions:

1. fitted OLS asymptotically reaches the risk of an affine witness; and
2. that affine witness has strictly lower MSE than the chosen baseline.

The baseline is arbitrary, so it may use a different and larger query subset.
This is the abstract theorem supporting a four-query OLS versus eight-query
sample-score comparison. -/
theorem highProbQQueryEfficient_fittedOLS_of_affineRiskGap
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (y baseline : Model Q X → ℝ)
    (fit : ∀ n ω, OLSFit
      (fun i => ψHat n ω (f_ref n ω i))
      (fun i => y (f_ref n ω i)))
    (θ : AffineCoefficients d)
    (hcompetitive : HighProbAffineRiskCompetitive μ hμ Pf y
      (fittedOLSPredictor ψHat f_ref y fit) ψ θ)
    (hgap : MSE Pf y (affineModel θ ψ) < MSE Pf y baseline) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss y
      (fittedOLSPredictor ψHat f_ref y fit) (fun _ _ => baseline) := by
  exact highProbQQueryEfficient_of_mseAtMost_lt_baseline
    Pf μ hμ y baseline (fittedOLSPredictor ψHat f_ref y fit)
    (MSE Pf y (affineModel θ ψ)) hcompetitive hgap

/-- Cross-budget, paper-shaped OLS query efficiency.

`Qols` determines the DKPS used by OLS.  `Qbaseline` determines the direct
sample-score baseline.  They are deliberately separate, matching the practical
MAGNET card rather than the same-subset comparison in the printed Theorem 2.
No cardinality inequality is needed by the mathematics: a caller may separately
record `Qols.card < Qbaseline.card` as the empirical query-saving claim. -/
theorem highProb_queryEfficient_crossBudget_of_affineRiskGap
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Finset Q → Model Q X → Vec d)
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qols Qbaseline : Finset Q)
    (fit : ∀ n ω, OLSFit
      (fun i => ψHat n ω Qols (f_ref n ω i))
      (fun i => score (f_ref n ω i) Qstar))
    (θ : AffineCoefficients d)
    (hcompetitive : HighProbAffineRiskCompetitive μ hμ Pf
      (yFull score Qstar)
      (yOLS_paper ψHat f_ref score Qstar Qols fit)
      (ψ Qols) θ)
    (hgap :
      MSE Pf (yFull score Qstar) (affineModel θ (ψ Qols)) <
        MSE Pf (yFull score Qstar) (yQ score Qbaseline)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (yOLS_paper ψHat f_ref score Qstar Qols fit)
      (fun _ _ => yQ score Qbaseline) := by
  exact highProbQQueryEfficient_fittedOLS_of_affineRiskGap
    Pf μ hμ (ψ Qols)
    (fun n ω f => ψHat n ω Qols f) f_ref
    (yFull score Qstar) (yQ score Qbaseline) fit θ
    hcompetitive hgap

/-- Exact affine realizability turns the affine-risk-gap premise into the simple
condition that the selected baseline has positive MSE. -/
theorem highProb_queryEfficient_crossBudget_of_affineRealizable
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Finset Q → Model Q X → Vec d)
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qols Qbaseline : Finset Q)
    (fit : ∀ n ω, OLSFit
      (fun i => ψHat n ω Qols (f_ref n ω i))
      (fun i => score (f_ref n ω i) Qstar))
    (θ : AffineCoefficients d)
    (hrealizable : ∀ f,
      yFull score Qstar f = affineModel θ (ψ Qols) f)
    (hcompetitive : HighProbAffineRiskCompetitive μ hμ Pf
      (yFull score Qstar)
      (yOLS_paper ψHat f_ref score Qstar Qols fit)
      (ψ Qols) θ)
    (hbaseline :
      0 < MSE Pf (yFull score Qstar) (yQ score Qbaseline)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (yOLS_paper ψHat f_ref score Qstar Qols fit)
      (fun _ _ => yQ score Qbaseline) := by
  apply highProb_queryEfficient_crossBudget_of_affineRiskGap
    Pf μ hμ ψ ψHat f_ref score Qstar Qols Qbaseline fit θ hcompetitive
  have hfun : affineModel θ (ψ Qols) = yFull score Qstar := by
    funext f
    exact (hrealizable f).symm
  rw [hfun]
  simpa [MSE, sqLoss] using hbaseline

/-- A fully discharged exact-design special case.

If, after some reference-sample size, the estimated perspectives are exactly
the population perspectives and every augmented reference design identifies
its affine coefficients, then exact affine realizability makes fitted OLS equal
the full benchmark score pointwise.  It therefore beats any cross-budget
sample-score baseline with positive MSE with probability one.

This theorem is intentionally strong.  The realistic asymptotic bridge is
`highProb_queryEfficient_crossBudget_of_affineRiskGap`; this result demonstrates
that the OLS definitions themselves support a non-circular end-to-end theorem. -/
theorem highProb_queryEfficient_crossBudget_of_eventuallyExactAffine
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Finset Q → Model Q X → Vec d)
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qols Qbaseline : Finset Q)
    (fit : ∀ n ω, OLSFit
      (fun i => ψHat n ω Qols (f_ref n ω i))
      (fun i => score (f_ref n ω i) Qstar))
    (θ : AffineCoefficients d)
    (hrealizable : ∀ f,
      yFull score Qstar f = affineModel θ (ψ Qols) f)
    (N : ℕ)
    (halign : ∀ n > N, ∀ ω f, ψHat n ω Qols f = ψ Qols f)
    (hidentify : ∀ n > N, ∀ ω,
      AffineIdentifyingDesign
        (fun i => ψHat n ω Qols (f_ref n ω i)))
    (hbaseline :
      0 < MSE Pf (yFull score Qstar) (yQ score Qbaseline)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (yOLS_paper ψHat f_ref score Qstar Qols fit)
      (fun _ _ => yQ score Qbaseline) := by
  unfold HighProbQQueryEfficient HighProbAtTop
  intro δ hδ
  refine ⟨N, ?_⟩
  intro n hn
  have hpred : ∀ ω,
      yOLS_paper ψHat f_ref score Qstar Qols fit n ω =
        yFull score Qstar := by
    intro ω
    exact fittedOLSPredictor_eq_target_of_exactAffine
      (ψ Qols) (fun n' ω' f => ψHat n' ω' Qols f)
      f_ref (yFull score Qstar) fit θ n ω
      (halign n hn ω) hrealizable (hidentify n hn ω)
  have hsub : Set.univ ⊆ {ω |
      Risk (Q := Q) (X := X) Pf sqLoss (yFull score Qstar)
        (yOLS_paper ψHat f_ref score Qstar Qols fit n ω) ≤
      Risk (Q := Q) (X := X) Pf sqLoss (yFull score Qstar)
        (yQ score Qbaseline)} := by
    intro ω _hω
    change
      Risk (Q := Q) (X := X) Pf sqLoss (yFull score Qstar)
          (yOLS_paper ψHat f_ref score Qstar Qols fit n ω) ≤
        Risk (Q := Q) (X := X) Pf sqLoss (yFull score Qstar)
          (yQ score Qbaseline)
    rw [hpred ω]
    change MSE Pf (yFull score Qstar) (yFull score Qstar) ≤
      MSE Pf (yFull score Qstar) (yQ score Qbaseline)
    simpa [MSE, sqLoss] using hbaseline.le
  calc
    1 - δ ≤ 1 := tsub_le_self
    _ = (μ n) Set.univ := by simp
    _ ≤ (μ n) {ω |
      Risk (Q := Q) (X := X) Pf sqLoss (yFull score Qstar)
        (yOLS_paper ψHat f_ref score Qstar Qols fit n ω) ≤
      Risk (Q := Q) (X := X) Pf sqLoss (yFull score Qstar)
        (yQ score Qbaseline)} := measure_mono hsub

section NecessityBoundary

/-- Three compactly supported one-dimensional perspectives. -/
def threePointFeature (i : Fin 3) : ℝ :=
  if i.val = 0 then -1 else if i.val = 1 then 0 else 1

/-- A Lipschitz but nonlinear target on `threePointFeature`. -/
def threePointTarget : Fin 3 → ℝ := fun i => (threePointFeature i) ^ 2

/-- The quadratic target is `2`-Lipschitz on the three-point perspective set. -/
theorem threePointTarget_lipschitz :
    ∀ i j : Fin 3,
      |threePointTarget i - threePointTarget j| ≤
        2 * |threePointFeature i - threePointFeature j| := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [threePointTarget, threePointFeature]

/-- The same target is not affine in the perspective coordinate. -/
theorem threePointTarget_not_affine :
    ¬ ∃ a b : ℝ, ∀ i : Fin 3,
      threePointTarget i = a + b * threePointFeature i := by
  rintro ⟨a, b, h⟩
  have h0 := h (0 : Fin 3)
  have h1 := h (1 : Fin 3)
  have h2 := h (2 : Fin 3)
  norm_num [threePointTarget, threePointFeature] at h0 h1 h2
  linarith

/-- Explicit boundary result: Lipschitz regularity of the score with respect to
perspective distance does not imply affine realizability, even on a finite
compact perspective set.  This is why the nearest-neighbor theorem cannot be
reused for OLS without an additional approximation/realizability premise. -/
theorem lipschitz_not_sufficient_for_affineRealizability :
    (∀ i j : Fin 3,
      |threePointTarget i - threePointTarget j| ≤
        2 * |threePointFeature i - threePointFeature j|) ∧
    ¬ ∃ a b : ℝ, ∀ i : Fin 3,
      threePointTarget i = a + b * threePointFeature i :=
  ⟨threePointTarget_lipschitz, threePointTarget_not_affine⟩

end NecessityBoundary

end DkpsQuench2026.Paper.OLS
