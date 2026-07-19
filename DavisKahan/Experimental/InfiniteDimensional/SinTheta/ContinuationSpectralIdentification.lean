/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationAssembly
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.Basic
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.PVMSubspace
import Spectra.SpectralTheory.ResolventForm

/-!
# Spectral-projection target for contour continuation

This module packages the genuine Spectra projection-valued measure associated
with a bounded self-adjoint operator.  It identifies each measurable spectral
projection with the Mathlib orthogonal projection onto its range and records
the exact orthogonal-projection property required by the continuation
assembly.

The scalar half of spectral identification is also recorded here: the
sign-correct scalar Riesz transform equals normalized winding, normalized
winding equals the selected-set indicator on the real spectrum, and the target
projection is the bounded spectral calculus of that indicator.  The remaining
bridge transports the operator-valued contour integral through the spectral
calculus.
-/

namespace ForMathlib
namespace DavisKahanExt

open Set
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory
open DavisKahan.Experimental.Foundation
open DavisKahan.Experimental.SpectraBridge

universe v

section BoundedSpectralProjection

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The genuine Spectra projection-valued measure of a bounded self-adjoint
operator. -/
noncomputable def boundedSelfAdjointSpectralPVM
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    Spectra.ProjValMeasure H :=
  spectralPVM (boundedSelfAdjointOperator A hA).selfAdjoint

/-- The genuine measurable spectral projection of a bounded self-adjoint
operator. -/
noncomputable def boundedSelfAdjointSpectralProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) : H →L[ℂ] H :=
  (boundedSelfAdjointSpectralPVM A hA).proj s hs

/-- The selected spectral range of a bounded self-adjoint operator. -/
noncomputable def boundedSelfAdjointSpectralSubspace
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) : Submodule ℂ H :=
  pvmRangeSubspace (boundedSelfAdjointSpectralPVM A hA) s hs

/-- The selected bounded spectral range has the canonical orthogonal
projection supplied by the underlying PVM projection. -/
noncomputable instance boundedSelfAdjointSpectralSubspace_hasOrthogonalProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (boundedSelfAdjointSpectralSubspace A hA s hs).HasOrthogonalProjection := by
  change
    (pvmRangeSubspace (boundedSelfAdjointSpectralPVM A hA) s hs).HasOrthogonalProjection
  infer_instance

/-- The bounded spectral projection is the group-calculus spectral
projection used by Spectra. -/
theorem boundedSelfAdjointSpectralProjection_eq_spectralProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      Spectra.QuantumMechanics.SpectralTheory.spectralProjection
        (Spectra.YosidaHille.genToGroup
          (boundedSelfAdjointOperator A hA).selfAdjoint) s hs :=
  rfl

/-- The selected spectral subspace is exactly the range of its spectral
projection. -/
@[simp] theorem boundedSelfAdjointSpectralSubspace_eq_range
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralSubspace A hA s hs =
      (boundedSelfAdjointSpectralProjection A hA s hs).range :=
  rfl

/-- The genuine bounded spectral projection is the Mathlib star projection
onto its selected spectral range. -/
theorem boundedSelfAdjointSpectralProjection_eq_starProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      (boundedSelfAdjointSpectralSubspace A hA s hs).starProjection := by
  change
    (boundedSelfAdjointSpectralPVM A hA).proj s hs =
      (pvmRangeSubspace (boundedSelfAdjointSpectralPVM A hA) s hs).starProjection
  exact pvmProjection_eq_starProjection_rangeSubspace
    (boundedSelfAdjointSpectralPVM A hA) s hs

/-- Every genuine bounded spectral projection is an orthogonal projection in
the continuation-facing predicate. -/
theorem boundedSelfAdjointSpectralProjection_isOrthogonalProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    IsOrthogonalProjection
      (boundedSelfAdjointSpectralProjection A hA s hs) := by
  let P : Spectra.ProjValMeasure H := boundedSelfAdjointSpectralPVM A hA
  change IsOrthogonalProjection (P.proj s hs)
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change P.proj s hs (P.proj s hs x) = P.proj s hs x
    simpa only [mul_apply_eq_comp] using
      congrArg (fun T : H →L[ℂ] H => T x) (P.proj_idem s hs)
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (P.isSelfAdjoint_proj s hs)

/-- Once contour spectral identification is supplied, the contour Riesz
operator inherits the exact orthogonal-projection property. -/
theorem SpectralSeparatingContour.contourRieszProjection_isOrthogonalProjection_of_eq
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s)
    (hidentify : Γ.contourRieszProjection =
      boundedSelfAdjointSpectralProjection A Γ.selfAdjoint s
        Γ.measurable_selected) :
    IsOrthogonalProjection Γ.contourRieszProjection := by
  rw [hidentify]
  exact boundedSelfAdjointSpectralProjection_isOrthogonalProjection
    A Γ.selfAdjoint s Γ.measurable_selected

/-- A pointwise spectral-identification result turns the fixed-contour affine
path into a path of orthogonal projections. -/
theorem fixedContourRieszOperator_operatorPath_isOrthogonalProjection_of_identification
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (parameterSet : Set ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ parameterSet,
      IsSelfAdjointOperator (operatorPath A V t))
    (hidentify : ∀ t (ht : t ∈ parameterSet),
      fixedContourRieszOperator Γ (operatorPath A V t) =
        boundedSelfAdjointSpectralProjection (operatorPath A V t)
          (hself t ht) s hs)
    {t : ℝ} (ht : t ∈ parameterSet) :
    IsOrthogonalProjection
      (fixedContourRieszOperator Γ (operatorPath A V t)) := by
  rw [hidentify t ht]
  exact boundedSelfAdjointSpectralProjection_isOrthogonalProjection
    (operatorPath A V t) (hself t ht) s hs


/-! ## Scalar contour selector -/

/-- The complex-valued indicator symbol of the selected real spectral set. -/
noncomputable def spectralSelector (s : Set ℝ) : ℝ → ℂ :=
  Set.indicator s (fun _ => (1 : ℂ))

/-- The selected-set indicator is measurable whenever the set is measurable. -/
theorem spectralSelector_measurable (s : Set ℝ) (hs : MeasurableSet s) :
    Measurable (spectralSelector s) := by
  classical
  exact measurable_const.indicator hs

/-- The selected-set indicator is uniformly bounded by one. -/
theorem spectralSelector_bounded (s : Set ℝ) :
    ∃ C : ℝ, ∀ lam : ℝ, ‖spectralSelector s lam‖ ≤ C := by
  simpa only [spectralSelector] using
    Spectra.QuantumMechanics.SpectralTheory.indicator_one_bdd s

namespace PiecewiseC1ClosedContour

/-- The sign-correct scalar Riesz transform associated with the project
resolvent convention `(A - z I)⁻¹`. -/
noncomputable def scalarRieszTransform
    (Γ : PiecewiseC1ClosedContour) (lam : ℝ) : ℂ :=
  rieszNormalization *
    ∫ t in (0 : ℝ)..1,
      (((lam : ℂ) - Γ.param t)⁻¹) *
        derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t

/-- The sign-correct scalar resolvent transform is exactly the normalized
winding value recorded by the contour. -/
theorem scalarRieszTransform_eq_normalizedWinding
    (Γ : PiecewiseC1ClosedContour) (lam : ℝ) :
    Γ.scalarRieszTransform lam = Γ.normalizedWinding (lam : ℂ) := by
  unfold scalarRieszTransform normalizedWinding
  have hintegral :
      (∫ t in (0 : ℝ)..1,
        (((lam : ℂ) - Γ.param t)⁻¹) *
          derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t) =
        -(∫ t in (0 : ℝ)..1,
          ((Γ.param t - (lam : ℂ))⁻¹) *
            derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    change (((lam : ℂ) - Γ.param t)⁻¹) *
        derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t =
      -(((Γ.param t - (lam : ℂ))⁻¹) *
        derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t)
    rw [show (lam : ℂ) - Γ.param t =
      -(Γ.param t - (lam : ℂ)) by ring]
    rw [inv_neg, neg_mul]
  rw [hintegral]
  simp [rieszNormalization]

end PiecewiseC1ClosedContour

/-- On the real spectrum, the scalar Riesz transform is the indicator of the
selected component. -/
theorem SpectralSeparatingContour.scalarRieszTransform_eq_spectralSelector
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) {lam : ℝ}
    (hlam : lam ∈ realSpectrum A) :
    Γ.geometric.scalarRieszTransform lam = spectralSelector s lam := by
  rw [Γ.geometric.scalarRieszTransform_eq_normalizedWinding]
  classical
  by_cases hmem : lam ∈ s
  · rw [Γ.normalizedWinding_eq_one hlam hmem]
    simp [spectralSelector, hmem]
  · rw [Γ.normalizedWinding_eq_zero hlam hmem]
    simp [spectralSelector, hmem]

/-- The genuine bounded spectral projection is the Spectra bounded functional
calculus applied to the selected-set indicator. -/
theorem boundedSelfAdjointSpectralProjection_eq_spectralCalculus_selector
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      Spectra.QuantumMechanics.SpectralTheory.spectralCalculus
        (Spectra.YosidaHille.genToGroup
          (boundedSelfAdjointOperator A hA).selfAdjoint)
        (spectralSelector s)
        (spectralSelector_measurable s hs)
        (spectralSelector_bounded s) := by
  rw [boundedSelfAdjointSpectralProjection_eq_spectralProjection]
  rfl

end BoundedSpectralProjection

end DavisKahanExt
end ForMathlib
