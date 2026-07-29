/-
Deterministic perturbation and generalization bridge for Quench OLS.

The theorems in this file isolate the exact mathematical inputs required to
turn finite-sample OLS optimality into population-risk competitiveness:

* OLS minimizes empirical squared error;
* the fitted and witness empirical risks generalize to their population risks;
* the affine witness transfers from the estimated DKPS coordinates to the true
  perspective coordinates.

The statistical proofs of those high-probability premises may later be supplied
by concentration, conditioning, and the existing DKPS alignment results.  The
logic from those premises to query efficiency is fully discharged here.
-/
import DkpsQuench2026.Paper.TheoryPractice
import DkpsQuench2026.Paper.OLSInvariance

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
variable {d n : ℕ}
variable {Ω : Type w} [MeasurableSpace Ω]

/-- Normalized empirical risk of one affine coefficient vector. -/
def empiricalAffineRisk
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (θ : AffineCoefficients d) : ℝ :=
  TheoryPractice.empiricalMSE target (fun i => affinePredict θ (x i))

/-- OLS optimality immediately implies normalized empirical-risk optimality. -/
theorem OLSFit.empiricalAffineRisk_le
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (fit : OLSFit x target) (θ : AffineCoefficients d) :
    empiricalAffineRisk x target fit.coeff ≤
      empiricalAffineRisk x target θ := by
  have hscale : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have h := mul_le_mul_of_nonneg_left (fit.optimal θ) hscale
  simpa [empiricalAffineRisk, TheoryPractice.empiricalMSE,
    TheoryPractice.empiricalMean, empiricalSquaredError] using h

/-- Deterministic two-sided generalization data at the fitted coefficients and
at one affine witness. -/
structure GeneralizationControl
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (truth : Model Q X → ℝ)
    (feature : Model Q X → Vec d)
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (fit : OLSFit x target) (witness : AffineCoefficients d)
    (fitError witnessError : ℝ) : Prop where
  fitted_population_le :
    MSE Pf truth (affineModel fit.coeff feature) ≤
      empiricalAffineRisk x target fit.coeff + fitError
  witness_empirical_le :
    empiricalAffineRisk x target witness ≤
      MSE Pf truth (affineModel witness feature) + witnessError

/-- Empirical OLS optimality plus two one-sided generalization inequalities
bounds the fitted population risk by the witness population risk. -/
theorem populationRisk_le_witness_add_generalization
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (truth : Model Q X → ℝ)
    (feature : Model Q X → Vec d)
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (fit : OLSFit x target) (witness : AffineCoefficients d)
    (fitError witnessError : ℝ)
    (hgen : GeneralizationControl Pf truth feature x target fit witness
      fitError witnessError) :
    MSE Pf truth (affineModel fit.coeff feature) ≤
      MSE Pf truth (affineModel witness feature) +
        fitError + witnessError := by
  have hopt := OLSFit.empiricalAffineRisk_le x target fit witness
  linarith [hgen.fitted_population_le, hgen.witness_empirical_le]

/-- Difference of two affine predictions with the same coefficients is the
inner product of the slope with the coordinate displacement. -/
theorem affinePredict_sub_affinePredict
    (θ : AffineCoefficients d) (x x' : Vec d) :
    affinePredict θ x - affinePredict θ x' =
      ⟪θ.slope, x - x'⟫_ℝ := by
  unfold affinePredict
  rw [inner_sub_right]
  ring

/-- Affine predictions are Lipschitz in their coordinates with constant equal
to the norm of the slope. -/
theorem abs_affinePredict_sub_le
    (θ : AffineCoefficients d) (x x' : Vec d) :
    |affinePredict θ x - affinePredict θ x'| ≤
      ‖θ.slope‖ * ‖x - x'‖ := by
  rw [affinePredict_sub_affinePredict]
  exact abs_real_inner_le_norm _ _

/-- A uniform DKPS-coordinate error gives a uniform affine-prediction error. -/
theorem abs_affinePredict_sub_le_of_coordinate_error
    (θ : AffineCoefficients d) (x x' : Vec d)
    (η : ℝ) (hcoord : ‖x - x'‖ ≤ η) :
    |affinePredict θ x - affinePredict θ x'| ≤ ‖θ.slope‖ * η := by
  exact (abs_affinePredict_sub_le θ x x').trans
    (mul_le_mul_of_nonneg_left hcoord (norm_nonneg _))

/-- Squared loss is stable under a perturbation of the prediction.  The
reference residual is bounded by `R`, while the two predictions differ by at
most `ε`. -/
theorem sqLoss_le_sqLoss_add_of_prediction_close
    (prediction reference truth ε R : ℝ)
    (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (hclose : |prediction - reference| ≤ ε)
    (href : |reference - truth| ≤ R) :
    sqLoss prediction truth ≤
      sqLoss reference truth + 2 * R * ε + ε ^ 2 := by
  have htri : |prediction - truth| ≤ |reference - truth| + ε := by
    calc
      |prediction - truth| =
          |(prediction - reference) + (reference - truth)| := by
        congr 1
        ring
      _ ≤ |prediction - reference| + |reference - truth| := abs_add_le _ _
      _ ≤ ε + |reference - truth| :=
        add_le_add hclose (le_refl _)
      _ = |reference - truth| + ε := by ring
  have hsquare : |prediction - truth| ^ 2 ≤
      (|reference - truth| + ε) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) htri 2
  have hmul : |reference - truth| * ε ≤ R * ε :=
    mul_le_mul_of_nonneg_right href hε
  have hsquare' : (prediction - truth) ^ 2 ≤
      (|reference - truth| + ε) ^ 2 := by
    simpa only [sq_abs] using hsquare
  have hrefsq : |reference - truth| ^ 2 =
      (reference - truth) ^ 2 := sq_abs _
  unfold sqLoss
  nlinarith

/-- Coordinate perturbation bound for squared loss of an affine witness. -/
theorem sqLoss_affinePredict_le_of_coordinate_error
    (θ : AffineCoefficients d) (estimated truthCoordinate : Vec d)
    (truthScore η R : ℝ)
    (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hcoord : ‖estimated - truthCoordinate‖ ≤ η)
    (href : |affinePredict θ truthCoordinate - truthScore| ≤ R) :
    sqLoss (affinePredict θ estimated) truthScore ≤
      sqLoss (affinePredict θ truthCoordinate) truthScore +
        2 * R * (‖θ.slope‖ * η) + (‖θ.slope‖ * η) ^ 2 := by
  apply sqLoss_le_sqLoss_add_of_prediction_close
      (affinePredict θ estimated) (affinePredict θ truthCoordinate)
      truthScore (‖θ.slope‖ * η) R
  · positivity
  · exact hR
  · exact abs_affinePredict_sub_le_of_coordinate_error
      θ estimated truthCoordinate η hcoord
  · exact href

/-- Explicit population-risk penalty generated by a uniform coordinate error
`η`, a witness residual bound `R`, and the witness slope norm. -/
def affineCoordinateRiskPenalty
    (θ : AffineCoefficients d) (R η : ℝ) : ℝ :=
  2 * R * (‖θ.slope‖ * η) + (‖θ.slope‖ * η) ^ 2

/-- Integrating the pointwise coordinate perturbation estimate gives a
population-MSE transfer bound. -/
theorem mse_affineModel_le_of_uniform_coordinate_error
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (truth : Model Q X → ℝ)
    (trueFeature estimatedFeature : Model Q X → Vec d)
    (θ : AffineCoefficients d) (η R : ℝ)
    (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hcoord : ∀ f, ‖estimatedFeature f - trueFeature f‖ ≤ η)
    (href : ∀ f,
      |affineModel θ trueFeature f - truth f| ≤ R)
    (hestimated : Integrable
      (fun f => sqLoss (affineModel θ estimatedFeature f) (truth f)) Pf)
    (htrue : Integrable
      (fun f => sqLoss (affineModel θ trueFeature f) (truth f)) Pf) :
    MSE Pf truth (affineModel θ estimatedFeature) ≤
      MSE Pf truth (affineModel θ trueFeature) +
        affineCoordinateRiskPenalty θ R η := by
  let C : ℝ := affineCoordinateRiskPenalty θ R η
  have hpoint : ∀ f,
      sqLoss (affineModel θ estimatedFeature f) (truth f) ≤
        sqLoss (affineModel θ trueFeature f) (truth f) + C := by
    intro f
    change sqLoss (affinePredict θ (estimatedFeature f)) (truth f) ≤
      sqLoss (affinePredict θ (trueFeature f)) (truth f) + C
    simpa only [C, affineCoordinateRiskPenalty, add_assoc] using
      (sqLoss_affinePredict_le_of_coordinate_error
        θ (estimatedFeature f) (trueFeature f) (truth f) η R
        hη hR (hcoord f) (href f))
  unfold MSE
  calc
    (∫ f, sqLoss (affineModel θ estimatedFeature f) (truth f) ∂Pf) ≤
        ∫ f, (sqLoss (affineModel θ trueFeature f) (truth f) + C) ∂Pf := by
      apply integral_mono hestimated (htrue.add (integrable_const C))
      exact hpoint
    _ = (∫ f, sqLoss (affineModel θ trueFeature f) (truth f) ∂Pf) +
        ∫ _f, C ∂Pf := integral_add htrue (integrable_const C)
    _ = (∫ f, sqLoss (affineModel θ trueFeature f) (truth f) ∂Pf) + C := by
      simp

/-- High-probability uniform DKPS-coordinate approximation. -/
def HighProbUniformCoordinateError
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (trueFeature : Model Q X → Vec d)
    (estimatedFeature : ℕ → Ω → Model Q X → Vec d)
    (radius : ℕ → ℝ) : Prop :=
  HighProbAtTop μ hμ (fun k => {ω |
    ∀ f, ‖estimatedFeature k ω f - trueFeature f‖ ≤ radius k})

/-- High-probability transfer of one affine witness from estimated to true
DKPS coordinates. -/
def HighProbWitnessRiskTransfer
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (truth : Model Q X → ℝ)
    (trueFeature : Model Q X → Vec d)
    (estimatedFeature : ℕ → Ω → Model Q X → Vec d)
    (witness : AffineCoefficients d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    HighProbAtTop μ hμ (fun k => {ω |
      MSE Pf truth (affineModel witness (estimatedFeature k ω)) ≤
        MSE Pf truth (affineModel witness trueFeature) + ε})

/-- A vanishing uniform coordinate-error event discharges the witness-risk
transfer premise. -/
theorem highProbWitnessRiskTransfer_of_uniformCoordinateError
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (truth : Model Q X → ℝ)
    (trueFeature : Model Q X → Vec d)
    (estimatedFeature : ℕ → Ω → Model Q X → Vec d)
    (witness : AffineCoefficients d)
    (radius : ℕ → ℝ) (R : ℝ)
    (hradius : ∀ k, 0 ≤ radius k) (hR : 0 ≤ R)
    (hcoord : HighProbUniformCoordinateError μ hμ
      trueFeature estimatedFeature radius)
    (hpenalty : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k > N,
      affineCoordinateRiskPenalty witness R (radius k) ≤ ε)
    (href : ∀ f,
      |affineModel witness trueFeature f - truth f| ≤ R)
    (hestimated : ∀ k ω, Integrable
      (fun f => sqLoss
        (affineModel witness (estimatedFeature k ω) f) (truth f)) Pf)
    (htrue : Integrable
      (fun f => sqLoss (affineModel witness trueFeature f) (truth f)) Pf) :
    HighProbWitnessRiskTransfer μ hμ Pf truth trueFeature
      estimatedFeature witness := by
  intro ε hε δ hδ
  obtain ⟨Ncoord, hNcoord⟩ := hcoord δ hδ
  obtain ⟨Npenalty, hNpenalty⟩ := hpenalty ε hε
  refine ⟨max Ncoord Npenalty, ?_⟩
  intro k hk
  have hkcoord : k > Ncoord := lt_of_le_of_lt (le_max_left _ _) hk
  have hkpenalty : k > Npenalty := lt_of_le_of_lt (le_max_right _ _) hk
  calc
    1 - δ ≤ (μ k) {ω |
        ∀ f, ‖estimatedFeature k ω f - trueFeature f‖ ≤ radius k} :=
      hNcoord k hkcoord
    _ ≤ (μ k) {ω |
        MSE Pf truth (affineModel witness (estimatedFeature k ω)) ≤
          MSE Pf truth (affineModel witness trueFeature) + ε} := by
      apply measure_mono
      intro ω hω
      have hrisk := mse_affineModel_le_of_uniform_coordinate_error
        Pf truth trueFeature (estimatedFeature k ω) witness
        (radius k) R (hradius k) hR hω href
        (hestimated k ω) htrue
      change MSE Pf truth (affineModel witness (estimatedFeature k ω)) ≤
        MSE Pf truth (affineModel witness trueFeature) + ε
      exact hrisk.trans
        (add_le_add_right (hNpenalty k hkpenalty)
          (MSE Pf truth (affineModel witness trueFeature)))

/-- One-stage generalization event for fitted OLS and a fixed affine witness on
the estimated DKPS feature map. -/
def olsGeneralizationEvent
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : AffineCoefficients d)
    (ε : ℝ) (k : ℕ) : Set Ω :=
  {ω |
    MSE Pf truth (affineModel (fit k ω).coeff (ψHat k ω)) ≤
      empiricalAffineRisk
        (fun i => ψHat k ω (f_ref k ω i))
        (fun i => truth (f_ref k ω i))
        (fit k ω).coeff + ε ∧
    empiricalAffineRisk
        (fun i => ψHat k ω (f_ref k ω i))
        (fun i => truth (f_ref k ω i)) witness ≤
      MSE Pf truth (affineModel witness (ψHat k ω)) + ε}

/-- Uniform population-versus-empirical affine-risk control on a declared
admissible coefficient class at one training stage.  Restricting the class is
important: uniform convergence over the entire unbounded affine class is not a
generic statistical fact. -/
def affineGeneralizationEventOn
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (admissible : Set (AffineCoefficients d))
    (ε : ℝ) (k : ℕ) : Set Ω :=
  {ω | ∀ θ ∈ admissible,
    |MSE Pf truth (affineModel θ (ψHat k ω)) -
      empiricalAffineRisk
        (fun i => ψHat k ω (f_ref k ω i))
        (fun i => truth (f_ref k ω i)) θ| ≤ ε}

/-- Strong convenience specialization to all affine coefficients.  Downstream
statistical theorems should normally use `affineGeneralizationEventOn` with a
bounded or otherwise controlled admissible class. -/
def uniformAffineGeneralizationEvent
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (ε : ℝ) (k : ℕ) : Set Ω :=
  affineGeneralizationEventOn Pf ψHat f_ref truth Set.univ ε k

/-- Generalization on an admissible class implies the two OLS inequalities when
both the fitted coefficients and the comparison witness belong to that class. -/
theorem olsGeneralizationEvent_of_on
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : AffineCoefficients d)
    (admissible : Set (AffineCoefficients d))
    (hfit : ∀ k ω, (fit k ω).coeff ∈ admissible)
    (hwitness : witness ∈ admissible)
    (ε : ℝ) (k : ℕ) :
    affineGeneralizationEventOn Pf ψHat f_ref truth admissible ε k ⊆
      olsGeneralizationEvent Pf ψHat f_ref truth fit witness ε k := by
  intro ω hω
  have hfitRisk := abs_le.mp (hω (fit k ω).coeff (hfit k ω))
  have hwitnessRisk := abs_le.mp (hω witness hwitness)
  constructor
  · linarith [hfitRisk.2]
  · linarith [hwitnessRisk.1]

/-- The all-class specialization of `olsGeneralizationEvent_of_on`. -/
theorem olsGeneralizationEvent_of_uniform
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : AffineCoefficients d)
    (ε : ℝ) (k : ℕ) :
    uniformAffineGeneralizationEvent Pf ψHat f_ref truth ε k ⊆
      olsGeneralizationEvent Pf ψHat f_ref truth fit witness ε k := by
  intro ω hω
  apply olsGeneralizationEvent_of_on
    Pf ψHat f_ref truth fit witness Set.univ
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _) ε k
  exact hω

/-- High-probability uniform convergence on an admissible affine coefficient
class. -/
def HighProbAffineGeneralizationOn
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (admissible : Set (AffineCoefficients d)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    HighProbAtTop μ hμ
      (affineGeneralizationEventOn Pf ψHat f_ref truth admissible ε)

/-- Strong all-class specialization. -/
def HighProbUniformAffineGeneralization
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ) : Prop :=
  HighProbAffineGeneralizationOn μ hμ Pf ψHat f_ref truth Set.univ

/-- High-probability two-sided generalization control for OLS and one affine
witness. -/
def HighProbOLSGeneralization
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : AffineCoefficients d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    HighProbAtTop μ hμ
      (olsGeneralizationEvent Pf ψHat f_ref truth fit witness ε)

/-- Uniform convergence on a controlled admissible class discharges
the specialized OLS generalization premise. -/
theorem highProbOLSGeneralization_of_on
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : AffineCoefficients d)
    (admissible : Set (AffineCoefficients d))
    (hfit : ∀ k ω, (fit k ω).coeff ∈ admissible)
    (hwitness : witness ∈ admissible)
    (huniform : HighProbAffineGeneralizationOn μ hμ Pf
      ψHat f_ref truth admissible) :
    HighProbOLSGeneralization μ hμ Pf ψHat f_ref truth fit witness := by
  intro ε hε
  apply HighProbAtTop.mono (huniform ε hε)
  intro k
  exact olsGeneralizationEvent_of_on
    Pf ψHat f_ref truth fit witness admissible hfit hwitness ε k

/-- Uniform convergence of the whole affine class discharges the
specialized OLS generalization premise, including the data-dependent fitted
coefficient vector. -/
theorem highProbOLSGeneralization_of_uniform
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : AffineCoefficients d)
    (huniform : HighProbUniformAffineGeneralization μ hμ Pf
      ψHat f_ref truth) :
    HighProbOLSGeneralization μ hμ Pf ψHat f_ref truth fit witness := by
  intro ε hε
  apply HighProbAtTop.mono (huniform ε hε)
  intro k
  exact olsGeneralizationEvent_of_uniform
    Pf ψHat f_ref truth fit witness ε k

/-- The complete deterministic OLS risk bridge at one training stage.

The first two inequalities are the fitted/witness generalization bounds on the
estimated feature map.  The third transfers the witness from estimated to true
DKPS coordinates. -/
theorem fittedOLSRisk_le_trueWitness
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (truth : Model Q X → ℝ)
    (trueFeature estimatedFeature : Model Q X → Vec d)
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (fit : OLSFit x target) (witness : AffineCoefficients d)
    (fitError witnessError transferError : ℝ)
    (hgen : GeneralizationControl Pf truth estimatedFeature x target fit witness
      fitError witnessError)
    (htransfer :
      MSE Pf truth (affineModel witness estimatedFeature) ≤
        MSE Pf truth (affineModel witness trueFeature) + transferError) :
    MSE Pf truth (affineModel fit.coeff estimatedFeature) ≤
      MSE Pf truth (affineModel witness trueFeature) +
        fitError + witnessError + transferError := by
  have h := populationRisk_le_witness_add_generalization
    Pf truth estimatedFeature x target fit witness fitError witnessError hgen
  linarith

/-- One-stage event collecting exactly the three deterministic premises needed
by `fittedOLSRisk_le_trueWitness`. -/
def olsRiskBridgeEvent
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : AffineCoefficients d)
    (ε : ℝ) (k : ℕ) : Set Ω :=
  {ω |
    MSE Pf truth
        (affineModel (fit k ω).coeff (ψHat k ω)) ≤
      empiricalAffineRisk
        (fun i => ψHat k ω (f_ref k ω i))
        (fun i => truth (f_ref k ω i))
        (fit k ω).coeff + ε ∧
    empiricalAffineRisk
        (fun i => ψHat k ω (f_ref k ω i))
        (fun i => truth (f_ref k ω i)) witness ≤
      MSE Pf truth (affineModel witness (ψHat k ω)) + ε ∧
    MSE Pf truth (affineModel witness (ψHat k ω)) ≤
      MSE Pf truth (affineModel witness ψ) + ε}

/-- High-probability package of OLS generalization and DKPS witness transfer. -/
def HighProbOLSRiskBridge
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : AffineCoefficients d) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    HighProbAtTop μ hμ
      (olsRiskBridgeEvent Pf ψ ψHat f_ref truth fit witness ε)

/-- Separate high-probability OLS generalization and witness-transfer results
combine into the unified `HighProbOLSRiskBridge`. -/
theorem highProbOLSRiskBridge_of_generalization_and_transfer
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : AffineCoefficients d)
    (hgeneralization : HighProbOLSGeneralization μ hμ Pf
      ψHat f_ref truth fit witness)
    (htransfer : HighProbWitnessRiskTransfer μ hμ Pf truth
      ψ ψHat witness)
    (hgeneralizationMeasurable : ∀ ε > 0, ∀ k,
      MeasurableSet (olsGeneralizationEvent Pf ψHat f_ref truth fit witness ε k))
    (htransferMeasurable : ∀ ε > 0, ∀ k,
      MeasurableSet {ω |
        MSE Pf truth (affineModel witness (ψHat k ω)) ≤
          MSE Pf truth (affineModel witness ψ) + ε}) :
    HighProbOLSRiskBridge μ hμ Pf ψ ψHat f_ref truth fit witness := by
  intro ε hε
  have hgen := hgeneralization ε hε
  have htrans := htransfer ε hε
  have hinter := HighProbAtTop.inter hgen htrans
    (hgeneralizationMeasurable ε hε)
    (htransferMeasurable ε hε)
  apply HighProbAtTop.mono hinter
  intro k ω hω
  exact ⟨hω.1.1, hω.1.2, hω.2⟩

/-- The named high-probability bridge discharges the abstract OLS risk
competitiveness premise used by the cross-budget query-efficiency theorem. -/
theorem highProbAffineRiskCompetitive_of_olsRiskBridge
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : AffineCoefficients d)
    (hbridge : HighProbOLSRiskBridge μ hμ Pf ψ ψHat f_ref truth fit witness) :
    HighProbAffineRiskCompetitive μ hμ Pf truth
      (fittedOLSPredictor ψHat f_ref truth fit) ψ witness := by
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hp := hbridge (ε / 3) hthird
  apply HighProbAtTop.mono hp
  intro k ω hω
  rcases hω with ⟨hfit, hwitness, htransfer⟩
  change MSE Pf truth
      (fittedOLSPredictor ψHat f_ref truth fit k ω) ≤
    MSE Pf truth (affineModel witness ψ) + ε
  have hdet := fittedOLSRisk_le_trueWitness
    Pf truth ψ (ψHat k ω)
    (fun i => ψHat k ω (f_ref k ω i))
    (fun i => truth (f_ref k ω i))
    (fit k ω) witness (ε / 3) (ε / 3) (ε / 3)
    ⟨hfit, hwitness⟩ htransfer
  change MSE Pf truth
      (affineModel (fit k ω).coeff (ψHat k ω)) ≤
    MSE Pf truth (affineModel witness ψ) + ε
  linarith [hdet]

/-- End-to-end cross-budget OLS query efficiency from the explicit statistical
bridge and a strict affine-risk gap. -/
theorem highProb_queryEfficient_crossBudget_of_olsRiskBridge
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (ψ : Finset Q → Model Q X → Vec d)
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qols Qbaseline : Finset Q)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω Qols (f_ref k ω i))
      (fun i => score (f_ref k ω i) Qstar))
    (witness : AffineCoefficients d)
    (hbridge : HighProbOLSRiskBridge μ hμ Pf
      (ψ Qols) (fun k ω f => ψHat k ω Qols f)
      f_ref (yFull score Qstar) fit witness)
    (hgap :
      MSE Pf (yFull score Qstar) (affineModel witness (ψ Qols)) <
        MSE Pf (yFull score Qstar) (yQ score Qbaseline)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (yOLS_paper ψHat f_ref score Qstar Qols fit)
      (fun _ _ => yQ score Qbaseline) := by
  apply highProb_queryEfficient_crossBudget_of_affineRiskGap
    Pf μ hμ ψ ψHat f_ref score Qstar Qols Qbaseline fit witness
  · have hcomp := highProbAffineRiskCompetitive_of_olsRiskBridge
      μ hμ Pf (ψ Qols) (fun k ω f => ψHat k ω Qols f)
      f_ref (yFull score Qstar) fit witness hbridge
    change HighProbAffineRiskCompetitive μ hμ Pf (yFull score Qstar)
      (fittedOLSPredictor (fun k ω f => ψHat k ω Qols f)
        f_ref (yFull score Qstar) fit)
      (ψ Qols) witness
    exact hcomp
  · exact hgap

/-- Population-MAE cross-budget query efficiency obtained from the explicit
OLS generalization/alignment bridge.  The required risk gap is stronger than
the MSE card gap: the affine witness MSE must lie below the square of the
baseline population MAE. -/
theorem highProbMAE_queryEfficient_crossBudget_of_olsRiskBridge
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (ψ : Finset Q → Model Q X → Vec d)
    (ψHat : ℕ → Ω → Finset Q → Model Q X → Vec d)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qols Qbaseline : Finset Q)
    (fit : ∀ k ω, OLSFit
      (fun i => ψHat k ω Qols (f_ref k ω i))
      (fun i => score (f_ref k ω i) Qstar))
    (witness : AffineCoefficients d)
    (hbridge : HighProbOLSRiskBridge μ hμ Pf
      (ψ Qols) (fun k ω f => ψHat k ω Qols f)
      f_ref (yFull score Qstar) fit witness)
    (hgap :
      MSE Pf (yFull score Qstar) (affineModel witness (ψ Qols)) <
        (TheoryPractice.populationMAE Pf (yFull score Qstar)
          (yQ score Qbaseline)) ^ 2)
    (habs : ∀ k ω, Integrable
      (fun f => TheoryPractice.absLoss
        (yOLS_paper ψHat f_ref score Qstar Qols fit k ω f)
        (yFull score Qstar f)) Pf)
    (hsq : ∀ k ω, Integrable
      (fun f => sqLoss
        (yOLS_paper ψHat f_ref score Qstar Qols fit k ω f)
        (yFull score Qstar f)) Pf) :
    TheoryPractice.PopulationMAEQueryEfficiency Pf μ hμ
      (yFull score Qstar)
      (yOLS_paper ψHat f_ref score Qstar Qols fit)
      (fun _ _ => yQ score Qbaseline) := by
  apply TheoryPractice.highProbMAE_queryEfficient_crossBudget_of_affineRiskGap
    Pf μ hμ ψ ψHat f_ref score Qstar Qols Qbaseline fit witness
  · have hcomp := highProbAffineRiskCompetitive_of_olsRiskBridge
      μ hμ Pf (ψ Qols) (fun k ω f => ψHat k ω Qols f)
      f_ref (yFull score Qstar) fit witness hbridge
    change HighProbAffineRiskCompetitive μ hμ Pf (yFull score Qstar)
      (fittedOLSPredictor (fun k ω f => ψHat k ω Qols f)
        f_ref (yFull score Qstar) fit)
      (ψ Qols) witness
    exact hcomp
  · exact hgap
  · exact habs
  · exact hsq

/-! ## Necessity of an identifying design -/

/-- A one-point one-dimensional design carrying no slope information. -/
def zeroDesignOne (_i : Fin 1) : Vec 1 := 0

/-- The zero design is not affine-identifying: arbitrary slopes make the same
prediction at its sole feature vector. -/
theorem zeroDesignOne_not_affineIdentifying :
    ¬ AffineIdentifyingDesign zeroDesignOne := by
  intro hidentify
  let θzero : AffineCoefficients 1 :=
    { intercept := 0, slope := 0 }
  let θslope : AffineCoefficients 1 :=
    { intercept := 0, slope := WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)) }
  have hpredict : ∀ i : Fin 1,
      affinePredict θzero (zeroDesignOne i) =
        affinePredict θslope (zeroDesignOne i) := by
    intro i
    simp [θzero, θslope, zeroDesignOne, affinePredict]
  have heq := hidentify θzero θslope hpredict
  have hslope := congrArg (fun θ : AffineCoefficients 1 => θ.slope (0 : Fin 1)) heq
  norm_num [θzero, θslope] at hslope

end DkpsQuench2026.Paper.OLS
