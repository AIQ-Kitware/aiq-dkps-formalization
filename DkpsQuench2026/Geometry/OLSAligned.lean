/-
Composition of the existing aligned-CMDS concentration theorem with the Quench
OLS witness-transfer theorem.
-/
import DkpsQuench2026.Geometry.AlignedCMDS
import DkpsQuench2026.Paper.OLSPerturbation

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

universe u v

namespace DkpsQuench2026

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ω : Type} [MeasurableSpace Ω]

/-- Finite aligned-configuration concentration, lifted through the existing
model-space factorization theorem, supplies the coordinate premise needed for
OLS witness-risk transfer. -/
theorem highProb_olsWitnessRiskTransfer_of_finite_configError
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    {n d : ℕ}
    (indexOf : Model Q X → Fin n)
    (ψFinite : Acharyya2024.Config n d)
    (ψhatFinite : ℕ → Ω → Acharyya2024.Config n d)
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (radius : ℕ → ℝ)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ k ω f,
      ψHat k ω f = ψhatFinite k ω (indexOf f))
    (hfinite : Acharyya2024.HighProbAtTop μ
      (fun k => {ω |
        Acharyya2024.ConfigError (ψhatFinite k ω) ψFinite ≤ radius k}))
    (truth : Model Q X → ℝ)
    (witness : Paper.OLS.AffineCoefficients d)
    (R : ℝ)
    (hradius : ∀ k, 0 ≤ radius k) (hR : 0 ≤ R)
    (hpenalty : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k > N,
      Paper.OLS.affineCoordinateRiskPenalty witness R (radius k) ≤ ε)
    (href : ∀ f,
      |Paper.OLS.affineModel witness ψ f - truth f| ≤ R)
    (hestimated : ∀ k ω, Integrable
      (fun f => sqLoss
        (Paper.OLS.affineModel witness (ψHat k ω) f) (truth f)) Pf)
    (htrue : Integrable
      (fun f => sqLoss (Paper.OLS.affineModel witness ψ f) (truth f)) Pf) :
    Paper.OLS.HighProbWitnessRiskTransfer μ hμ Pf truth ψ ψHat witness := by
  have hcoord : Paper.OLS.HighProbUniformCoordinateError
      μ hμ ψ ψHat radius :=
    quench_uniform_embedding_error_of_finite_configError
      μ hμ indexOf ψFinite ψhatFinite ψ ψHat radius
      hψ hψHat hfinite
  exact Paper.OLS.highProbWitnessRiskTransfer_of_uniformCoordinateError
    μ hμ Pf truth ψ ψHat witness radius R hradius hR
    hcoord hpenalty href hestimated htrue


/-- The finite aligned-CMDS concentration theorem and uniform affine
risk generalization on a controlled coefficient class together discharge the
complete OLS risk bridge.

This is the principal Lean-side seam between the existing DKPS spectral theory
and the OLS query-efficiency theorem. -/
theorem highProb_olsRiskBridge_of_finite_configError_on
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    {n d : ℕ}
    (indexOf : Model Q X → Fin n)
    (ψFinite : Acharyya2024.Config n d)
    (ψhatFinite : ℕ → Ω → Acharyya2024.Config n d)
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (radius : ℕ → ℝ)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ k ω f,
      ψHat k ω f = ψhatFinite k ω (indexOf f))
    (hfinite : Acharyya2024.HighProbAtTop μ
      (fun k => {ω |
        Acharyya2024.ConfigError (ψhatFinite k ω) ψFinite ≤ radius k}))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, Paper.OLS.OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : Paper.OLS.AffineCoefficients d)
    (admissible : Set (Paper.OLS.AffineCoefficients d))
    (hfitAdmissible : ∀ k ω, (fit k ω).coeff ∈ admissible)
    (hwitnessAdmissible : witness ∈ admissible)
    (hgeneralization : Paper.OLS.HighProbAffineGeneralizationOn
      μ hμ Pf ψHat f_ref truth admissible)
    (R : ℝ)
    (hradius : ∀ k, 0 ≤ radius k) (hR : 0 ≤ R)
    (hpenalty : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k > N,
      Paper.OLS.affineCoordinateRiskPenalty witness R (radius k) ≤ ε)
    (href : ∀ f,
      |Paper.OLS.affineModel witness ψ f - truth f| ≤ R)
    (hestimated : ∀ k ω, Integrable
      (fun f => sqLoss
        (Paper.OLS.affineModel witness (ψHat k ω) f) (truth f)) Pf)
    (htrue : Integrable
      (fun f => sqLoss (Paper.OLS.affineModel witness ψ f) (truth f)) Pf)
    (hgeneralizationMeasurable : ∀ ε > 0, ∀ k,
      MeasurableSet (Paper.OLS.olsGeneralizationEvent
        Pf ψHat f_ref truth fit witness ε k))
    (htransferMeasurable : ∀ ε > 0, ∀ k,
      MeasurableSet {ω |
        MSE Pf truth (Paper.OLS.affineModel witness (ψHat k ω)) ≤
          MSE Pf truth (Paper.OLS.affineModel witness ψ) + ε}) :
    Paper.OLS.HighProbOLSRiskBridge
      μ hμ Pf ψ ψHat f_ref truth fit witness := by
  have hgen : Paper.OLS.HighProbOLSGeneralization
      μ hμ Pf ψHat f_ref truth fit witness :=
    Paper.OLS.highProbOLSGeneralization_of_on
      μ hμ Pf ψHat f_ref truth fit witness admissible
      hfitAdmissible hwitnessAdmissible hgeneralization
  have htransfer : Paper.OLS.HighProbWitnessRiskTransfer
      μ hμ Pf truth ψ ψHat witness :=
    highProb_olsWitnessRiskTransfer_of_finite_configError
      μ hμ Pf indexOf ψFinite ψhatFinite ψ ψHat radius
      hψ hψHat hfinite truth witness R hradius hR hpenalty
      href hestimated htrue
  exact Paper.OLS.highProbOLSRiskBridge_of_generalization_and_transfer
    μ hμ Pf ψ ψHat f_ref truth fit witness
    hgen htransfer hgeneralizationMeasurable htransferMeasurable

/-- Strong all-affine-class convenience specialization of
`highProb_olsRiskBridge_of_finite_configError_on`.  In applications the
controlled-class theorem above is normally the appropriate entry point. -/
theorem highProb_olsRiskBridge_of_finite_configError
    (μ : ℕ → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    {n d : ℕ}
    (indexOf : Model Q X → Fin n)
    (ψFinite : Acharyya2024.Config n d)
    (ψhatFinite : ℕ → Ω → Acharyya2024.Config n d)
    (ψ : Model Q X → Vec d)
    (ψHat : ℕ → Ω → Model Q X → Vec d)
    (radius : ℕ → ℝ)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ k ω f,
      ψHat k ω f = ψhatFinite k ω (indexOf f))
    (hfinite : Acharyya2024.HighProbAtTop μ
      (fun k => {ω |
        Acharyya2024.ConfigError (ψhatFinite k ω) ψFinite ≤ radius k}))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (truth : Model Q X → ℝ)
    (fit : ∀ k ω, Paper.OLS.OLSFit
      (fun i => ψHat k ω (f_ref k ω i))
      (fun i => truth (f_ref k ω i)))
    (witness : Paper.OLS.AffineCoefficients d)
    (hgeneralization : Paper.OLS.HighProbUniformAffineGeneralization
      μ hμ Pf ψHat f_ref truth)
    (R : ℝ)
    (hradius : ∀ k, 0 ≤ radius k) (hR : 0 ≤ R)
    (hpenalty : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k > N,
      Paper.OLS.affineCoordinateRiskPenalty witness R (radius k) ≤ ε)
    (href : ∀ f,
      |Paper.OLS.affineModel witness ψ f - truth f| ≤ R)
    (hestimated : ∀ k ω, Integrable
      (fun f => sqLoss
        (Paper.OLS.affineModel witness (ψHat k ω) f) (truth f)) Pf)
    (htrue : Integrable
      (fun f => sqLoss (Paper.OLS.affineModel witness ψ f) (truth f)) Pf)
    (hgeneralizationMeasurable : ∀ ε > 0, ∀ k,
      MeasurableSet (Paper.OLS.olsGeneralizationEvent
        Pf ψHat f_ref truth fit witness ε k))
    (htransferMeasurable : ∀ ε > 0, ∀ k,
      MeasurableSet {ω |
        MSE Pf truth (Paper.OLS.affineModel witness (ψHat k ω)) ≤
          MSE Pf truth (Paper.OLS.affineModel witness ψ) + ε}) :
    Paper.OLS.HighProbOLSRiskBridge
      μ hμ Pf ψ ψHat f_ref truth fit witness := by
  exact highProb_olsRiskBridge_of_finite_configError_on
    μ hμ Pf indexOf ψFinite ψhatFinite ψ ψHat radius hψ hψHat hfinite
    f_ref truth fit witness Set.univ
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _) hgeneralization
    R hradius hR hpenalty href hestimated htrue
    hgeneralizationMeasurable htransferMeasurable

end DkpsQuench2026
