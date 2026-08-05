/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Section8
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation.WitnessGraph

/-!
# Reusing the production contour continuation layer

The repository already contains operator-valued contour integration,
spectral-calculus identification, norm transport, and continuation witnesses.
The missing circle-specific task is therefore geometric: construct one
proof-carrying `PiecewiseC1ClosedContour` and prove its winding laws.  This file
makes that boundary explicit and forwards every analytic conclusion once the
geometric realization is supplied.
-/

open scoped InnerProductSpace unitInterval
open Set

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Experimental.Foundation
open Frontier
open Frontier.Section8

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A E : H →L[ℂ] H} {s : Set ℝ}

/-- A realization of the elementary center-radius separation data by the
existing proof-carrying contour interface.  This is the exact remaining bridge
between the old circle frontier and the compiled generic contour theory. -/
structure RealizedCircleContinuationData
    (D : CircleContinuationData A E s) where
  contour : PiecewiseC1ClosedContour
  separating : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
    SpectralSeparatingContour (operatorPath A E t) s
  geometric_eq : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
    (separating t ht).geometric = contour
  margin_eq : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
    (separating t ht).spectralMargin = D.margin

namespace RealizedCircleContinuationData

/-- A realized circle supplies the production continuation witness directly. -/
noncomputable def toSpectralContinuationWitness
    (D : CircleContinuationData A E s)
    (R : RealizedCircleContinuationData D) :
    SpectralContinuationWitness A E s where
  contour := R.contour
  separating := R.separating
  geometric_eq := R.geometric_eq
  margin := D.margin
  margin_pos := D.margin_pos
  spectrum_separated := by
    intro t ht x lam hlam
    have h := (R.separating t ht).spectrum_separated x lam hlam
    rwa [R.margin_eq t ht, R.geometric_eq t ht] at h

/-- The source endpoint is the genuine selected spectral projection. -/
theorem sourceProjection_eq_spectralProjection
    (D : CircleContinuationData A E s)
    (R : RealizedCircleContinuationData D) :
    (R.toSpectralContinuationWitness D).sourceSelectedProjection =
      boundedSelfAdjointSpectralProjection A D.hA s D.hs := by
  let C := R.toSpectralContinuationWitness D
  have h := C.sourceSeparatingContour.fixedContourRieszOperator_eq_boundedSelfAdjointSpectralProjection
  simpa [C, toSpectralContinuationWitness,
    SpectralContinuationWitness.sourceSelectedProjection,
    SpectralContinuationWitness.sourceSeparatingContour_geometric] using h

/-- The target endpoint is the genuine selected spectral projection. -/
theorem targetProjection_eq_spectralProjection
    (D : CircleContinuationData A E s)
    (R : RealizedCircleContinuationData D) :
    (R.toSpectralContinuationWitness D).targetSelectedProjection =
      boundedSelfAdjointSpectralProjection (A + E)
        (D.hA.add D.hE) s D.hs := by
  let C := R.toSpectralContinuationWitness D
  have h := C.targetSeparatingContour.fixedContourRieszOperator_eq_boundedSelfAdjointSpectralProjection
  simpa [C, toSpectralContinuationWitness,
    SpectralContinuationWitness.targetSelectedProjection,
    SpectralContinuationWitness.targetSeparatingContour_geometric] using h

/-- The realized selected projection path is norm-continuous. -/
theorem continuous_selectedProjectionPath
    (D : CircleContinuationData A E s)
    (R : RealizedCircleContinuationData D) :
    ContinuousOn
      (fun t : ℝ => fixedContourRieszOperator R.contour (operatorPath A E t))
      (Set.Icc 0 1) := by
  exact continuousOn_fixedContourRieszOperator_operatorPath
    R.contour A E (Set.Icc 0 1) D.margin D.margin_pos
    (fun t ht => (R.separating t ht).selfAdjoint)
    (R.toSpectralContinuationWitness D).spectrum_separated

/-- Quantitative norm variation along the realized circle path. -/
theorem norm_selectedProjectionPath_sub_le
    (D : CircleContinuationData A E s)
    (R : RealizedCircleContinuationData D)
    {t u : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ‖fixedContourRieszOperator R.contour (operatorPath A E t) -
        fixedContourRieszOperator R.contour (operatorPath A E u)‖ ≤
      selectedBranchProjectionLipschitzConstant R.contour E D.margin *
        ‖t - u‖ := by
  simpa [selectedBranchProjectionLipschitzConstant, mul_assoc] using
    norm_fixedContourRieszOperator_operatorPath_sub_le
      R.contour A E (Set.Icc 0 1) D.margin D.margin_pos
      (fun r hr => (R.separating r hr).selfAdjoint)
      (R.toSpectralContinuationWitness D).spectrum_separated ht hu

/-- A small contour coefficient gives the canonical contractive angular graph
at the endpoint. -/
theorem existsUnique_endpointAngularOperator
    (D : CircleContinuationData A E s)
    (R : RealizedCircleContinuationData D)
    (hsmall : selectedBranchProjectionLipschitzConstant
      R.contour E D.margin < Real.sqrt 2 / 2) :
    ∃! X : H →L[ℂ] H,
      IsAngularOperator
          (R.toSpectralContinuationWitness D).sourceSelectedSpectralSubspace X ∧
      graphSubspace
          (R.toSpectralContinuationWitness D).sourceSelectedSpectralSubspace X =
        (R.toSpectralContinuationWitness D).targetSelectedSpectralSubspace ∧
      ‖X‖ < 1 := by
  exact SpectralContinuationWitness.existsUnique_selectedEndpointAngularOperator
    (R.toSpectralContinuationWitness D) hsmall

end RealizedCircleContinuationData

/-- A common geometric circle witness is precisely what is still required to
turn the elementary frontier data into the production continuation witness. -/
structure CommonCircleGeometry
    (D : CircleContinuationData A E s) where
  geometric : PiecewiseC1ClosedContour
  geometric_is_circle : Prop
  margin_from_circle : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
    ∀ x : unitInterval, ∀ lam ∈ realSpectrum (operatorPath A E t),
      D.margin ≤ ‖geometric.path x - (lam : ℂ)‖
  winding_selected : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
    ∀ lam ∈ realSpectrum (operatorPath A E t), lam ∈ s →
      geometric.normalizedWinding (lam : ℂ) = 1
  winding_complement : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
    ∀ lam ∈ realSpectrum (operatorPath A E t), lam ∉ s →
      geometric.normalizedWinding (lam : ℂ) = 0

/-- The common geometric data produce a realized continuation object. -/
noncomputable def CommonCircleGeometry.realize
    (D : CircleContinuationData A E s) (G : CommonCircleGeometry D) :
    RealizedCircleContinuationData D where
  contour := G.geometric
  separating := fun t ht =>
    { geometric := G.geometric
      -- `IsSymmetric.smul` takes the conjugation-fixedness of the scalar, not the scalar;
      -- for a real `t` viewed in `ℂ` that is `Complex.conj_ofReal`.
      selfAdjoint := D.hA.add
        (LinearMap.IsSymmetric.smul (c := (t : ℂ)) (by simp) D.hE)
      measurable_selected := D.hs
      spectralMargin := D.margin
      spectralMargin_pos := D.margin_pos
      spectrum_separated := G.margin_from_circle t ht
      winding_selected := G.winding_selected t ht
      winding_complement := G.winding_complement t ht }
  geometric_eq := by intro t ht; rfl
  margin_eq := by intro t ht; rfl

end

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti