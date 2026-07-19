/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationAssembly
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.Basic
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.PVMSubspace
import Spectra.SpectralTheory.ResolventForm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

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
open MeasureTheory
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


/-! ## Resolvent through the bounded continuous functional calculus -/

/-- Under a positive distance bound from the real spectrum, the project
resolvent is the complex continuous functional calculus of the scalar
resolvent symbol. -/
theorem resolventOperator_eq_cfc_resolventSymbol
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (z : ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ lam ∈ realSpectrum A, delta ≤ ‖z - (lam : ℂ)‖) :
    resolventOperator A z = cfc (fun w : ℂ => (w - z)⁻¹) A := by
  let f : ℂ → ℂ := fun w => w - z
  let g : ℂ → ℂ := fun w => (w - z)⁻¹
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hnormal : IsStarNormal A := hAsa.isStarNormal
  have hne : ∀ w ∈ spectrum ℂ A, f w ≠ 0 := by
    intro w hw hzero
    obtain ⟨lam, hlam, rfl⟩ :=
      hAsa.spectrumRestricts.algebraMap_image.symm ▸ hw
    have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
      rw [← hAsa.spectrumRestricts.algebraMap_image]
      exact ⟨lam, hlam, rfl⟩
    have hdist := hsep lam (by exact hlamC)
    have heq : (lam : ℂ) = z :=
      sub_eq_zero.mp (by simpa [f] using hzero)
    rw [← heq, sub_self, norm_zero] at hdist
    linarith
  have hfcont : ContinuousOn f (spectrum ℂ A) :=
    (continuous_id.sub continuous_const).continuousOn
  have hgcont : ContinuousOn g (spectrum ℂ A) := hfcont.inv₀ hne
  let R : H →L[ℂ] H := cfc g A
  have hshift : cfc f A = A - z • (1 : H →L[ℂ] H) := by
    rw [show f = fun w : ℂ => w - z from rfl,
      cfc_sub (fun w : ℂ => w) (fun _ : ℂ => z) A,
      cfc_id' (R := ℂ) (a := A), cfc_const z A,
      Algebra.algebraMap_eq_smul_one]
  have hright : (A - z • (1 : H →L[ℂ] H)) * R = 1 := by
    have hmul : cfc f A * cfc g A = cfc (fun w => f w * g w) A :=
      (cfc_mul f g A hfcont hgcont).symm
    rw [← hshift]
    change cfc f A * cfc g A = 1
    rw [hmul,
      cfc_congr (g := fun _ : ℂ => (1 : ℂ))
        (fun w hw => by simpa [f, g] using mul_inv_cancel₀ (hne w hw)),
      cfc_const_one ℂ A]
  have hz : InResolventSet A z :=
    complex_inResolventSet_of_distance A hA z delta hdelta hsep
  have hchosen := resolventOperator_mul_cancel A hz
  change resolventOperator A z = cfc g A
  calc
    resolventOperator A z = resolventOperator A z * 1 := (mul_one _).symm
    _ = resolventOperator A z *
        ((A - z • (1 : H →L[ℂ] H)) * R) := by rw [hright]
    _ = (resolventOperator A z *
        (A - z • (1 : H →L[ℂ] H))) * R := by rw [mul_assoc]
    _ = R := by rw [hchosen, one_mul]
    _ = cfc g A := rfl

/-- Along a separating contour, each project resolvent is represented by the
bounded continuous functional calculus of its scalar symbol. -/
theorem SpectralSeparatingContour.resolventOperator_eq_cfc
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) (t : unitInterval) :
    resolventOperator A (Γ.path t) =
      cfc (fun w : ℂ => (w - Γ.path t)⁻¹) A := by
  exact resolventOperator_eq_cfc_resolventSymbol
    A Γ.selfAdjoint (Γ.path t) Γ.spectralMargin Γ.spectralMargin_pos
      (Γ.spectrum_separated t)

/-- The contour resolvent one-form is the continuous functional calculus of
its scalar one-form symbol. -/
theorem SpectralSeparatingContour.resolventOneForm_eq_cfc
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) (t : unitInterval) (v : ℂ) :
    resolventOneForm A (Γ.path t) v =
      cfc (fun w : ℂ => v * (w - Γ.path t)⁻¹) A := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr Γ.selfAdjoint
  have hne : ∀ w ∈ spectrum ℂ A, w - Γ.path t ≠ 0 := by
    intro w hw hzero
    obtain ⟨lam, hlam, rfl⟩ :=
      hAsa.spectrumRestricts.algebraMap_image.symm ▸ hw
    have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
      rw [← hAsa.spectrumRestricts.algebraMap_image]
      exact ⟨lam, hlam, rfl⟩
    have hdist := Γ.spectrum_separated t lam (by exact hlamC)
    have heq : (lam : ℂ) = Γ.path t := sub_eq_zero.mp hzero
    rw [← heq, sub_self, norm_zero] at hdist
    linarith [Γ.spectralMargin_pos]
  have hgcont : ContinuousOn (fun w : ℂ => (w - Γ.path t)⁻¹)
      (spectrum ℂ A) :=
    ((continuous_id.sub continuous_const).continuousOn).inv₀ hne
  rw [resolventOneForm_apply, Γ.resolventOperator_eq_cfc t]
  rw [← cfc_const_mul v (fun w : ℂ => (w - Γ.path t)⁻¹) A hgcont]


/-! ## Interval-integral calculus bridge -/

/-- The bundled continuous functional calculus commutes with an oriented
interval integral of continuous spectrum-valued symbols. -/
theorem cfcL_intervalIntegral
    (A : H →L[ℂ] H) (hA : IsStarNormal A)
    (f : ℝ → C(spectrum ℂ A, ℂ)) {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, cfcL (a := A) hA (f t)) =
      cfcL (a := A) hA (∫ t in a..b, f t) := by
  change
    (∫ t in Set.Ioc a b, cfcL (a := A) hA (f t)) -
        (∫ t in Set.Ioc b a, cfcL (a := A) hA (f t)) =
      cfcL (a := A) hA
        ((∫ t in Set.Ioc a b, f t) - (∫ t in Set.Ioc b a, f t))
  rw [map_sub]
  congr 1
  · exact cfcL_integral A f hf.1 hA
  · exact cfcL_integral A f hf.2 hA

/-- On an ordered real interval, the unbundled continuous functional calculus
commutes with integration once the restricted scalar symbols form an
integrable continuous-map-valued function. -/
theorem cfc_intervalIntegral_of_le'
    (A : H →L[ℂ] H) (hA : IsStarNormal A)
    (f : ℝ → ℂ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ContinuousOn (f t) (spectrum ℂ A))
    (hf_int : IntegrableOn
      (fun t : ℝ =>
        ContinuousMap.mkD ((spectrum ℂ A).restrict (f t)) 0)
      (Set.Ioc a b) volume) :
    cfc (fun z => ∫ t in a..b, f t z) A =
      ∫ t in a..b, cfc (f t) A := by
  simpa only [intervalIntegral.integral_of_le hab] using
    (cfc_integral' f A hf_cont hf_int hA)


/-! ## The operator contour integral through the isometric CFC -/

/-- The scalar contour integrand, bundled as a continuous function on the
complex spectrum.  `mkD` keeps the definition total; spectral separation shows
that it takes the intended value on the contour parameter interval. -/
noncomputable def PiecewiseC1ClosedContour.contourResolventSymbol
    (Γ : PiecewiseC1ClosedContour) (A : H →L[ℂ] H) (t : ℝ) :
    C(spectrum ℂ A, ℂ) :=
  ContinuousMap.mkD
    ((spectrum ℂ A).restrict
      (fun w : ℂ =>
        derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t *
          (w - Γ.param t)⁻¹)) 0

/-- At every contour point, the scalar resolvent symbol is continuous on the
complex spectrum. -/
theorem SpectralSeparatingContour.continuousOn_resolventSymbol
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) (t : unitInterval) :
    ContinuousOn (fun w : ℂ => (w - Γ.path t)⁻¹) (spectrum ℂ A) := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr Γ.selfAdjoint
  have hne : ∀ w ∈ spectrum ℂ A, w - Γ.path t ≠ 0 := by
    intro w hw hzero
    obtain ⟨lam, hlam, rfl⟩ :=
      hAsa.spectrumRestricts.algebraMap_image.symm ▸ hw
    have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
      rw [← hAsa.spectrumRestricts.algebraMap_image]
      exact ⟨lam, hlam, rfl⟩
    have hdist := Γ.spectrum_separated t lam (by exact hlamC)
    have heq : (lam : ℂ) = Γ.path t := sub_eq_zero.mp hzero
    rw [← heq, sub_self, norm_zero] at hdist
    linarith [Γ.spectralMargin_pos]
  exact ((continuous_id.sub continuous_const).continuousOn).inv₀ hne

/-- Applying the bounded continuous functional calculus to the bundled scalar
symbol recovers the operator-valued curve-integral integrand. -/
theorem SpectralSeparatingContour.cfcL_contourResolventSymbol_eq_curveIntegralFun
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cfcL (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        (Γ.geometric.contourResolventSymbol A t) =
      curveIntegralFun (resolventOneForm A) Γ.path t := by
  let τ : unitInterval := ⟨t, ht⟩
  have hnormal : IsStarNormal A :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      Γ.selfAdjoint).isStarNormal
  unfold PiecewiseC1ClosedContour.contourResolventSymbol
  rw [← cfc_eq_cfcL_mkD
    (f := fun w : ℂ =>
      derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t *
        (w - Γ.geometric.param t)⁻¹)
    (a := A) (ha := hnormal)]
  rw [curveIntegralFun_def]
  have hparam : Γ.geometric.param = Γ.path.extend := by
    unfold PiecewiseC1ClosedContour.param
    rfl
  rw [hparam, Γ.path.extend_apply ht]
  exact
    (Γ.resolventOneForm_eq_cfc τ
      (derivWithin Γ.path.extend (Set.Icc (0 : ℝ) 1) t)).symm

/-- The continuous-map-valued scalar contour integrand is interval integrable.
The proof pulls integrability back from the already established operator
integrand through the isometric complex continuous functional calculus. -/
theorem SpectralSeparatingContour.intervalIntegrable_contourResolventSymbol
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    IntervalIntegrable
      (Γ.geometric.contourResolventSymbol A) volume 0 1 := by
  let hnormal : IsStarNormal A :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      Γ.selfAdjoint).isStarNormal
  let L : C(spectrum ℂ A, ℂ) →L[ℂ] (H →L[ℂ] H) :=
    cfcL (a := A) hnormal
  have hoperator :
      IntervalIntegrable
        (curveIntegralFun (resolventOneForm A) Γ.path) volume 0 1 :=
    Γ.curveIntegrable_resolventOneForm
  have hmapped :
      IntervalIntegrable
        (fun t => L (Γ.geometric.contourResolventSymbol A t))
        volume 0 1 := by
    refine hoperator.congr_uIoo ?_
    intro t ht
    rw [Set.uIoo_of_le zero_le_one] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self ht
    exact (Γ.cfcL_contourResolventSymbol_eq_curveIntegralFun htI).symm
  have hIso : Isometry L := by
    simpa [L, cfcL] using (isometry_cfcHom A hnormal)
  have hpull {μ : Measure ℝ}
      {f : ℝ → C(spectrum ℂ A, ℂ)}
      (hf : Integrable (fun t => L (f t)) μ) : Integrable f μ := by
    have hiff :
        Integrable ((fun g : C(spectrum ℂ A, ℂ) => L g) ∘ f) μ ↔
          Integrable f μ :=
      LipschitzWith.integrable_comp_iff_of_antilipschitz
        (μ := μ) (f := f) (g := fun g : C(spectrum ℂ A, ℂ) => L g)
        hIso.lipschitz hIso.antilipschitz (by simp)
    exact hiff.mp (by simpa only [Function.comp_def] using hf)
  exact ⟨hpull hmapped.1, hpull hmapped.2⟩

/-- The normalized scalar contour integral as one continuous function on the
complex spectrum. -/
noncomputable def SpectralSeparatingContour.integratedContourResolventSymbol
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) : C(spectrum ℂ A, ℂ) :=
  rieszNormalization •
    ∫ t in (0 : ℝ)..1, Γ.geometric.contourResolventSymbol A t

/-- The unnormalized operator contour integral is the continuous functional
calculus of the integrated scalar contour symbol. -/
theorem SpectralSeparatingContour.resolventCurveIntegral_eq_cfcL
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    Γ.resolventCurveIntegral =
      cfcL (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        (∫ t in (0 : ℝ)..1,
          Γ.geometric.contourResolventSymbol A t) := by
  rw [resolventCurveIntegral, curveIntegral_def]
  calc
    (∫ t in (0 : ℝ)..1,
        curveIntegralFun (resolventOneForm A) Γ.path t) =
      ∫ t in (0 : ℝ)..1,
        cfcL (a := A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
            Γ.selfAdjoint).isStarNormal
          (Γ.geometric.contourResolventSymbol A t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        exact (Γ.cfcL_contourResolventSymbol_eq_curveIntegralFun ht).symm
    _ = cfcL (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        (∫ t in (0 : ℝ)..1,
          Γ.geometric.contourResolventSymbol A t) :=
      cfcL_intervalIntegral A
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        (Γ.geometric.contourResolventSymbol A)
        Γ.intervalIntegrable_contourResolventSymbol

/-- The normalized Riesz operator is the continuous functional calculus of the
integrated scalar contour symbol. -/
theorem SpectralSeparatingContour.contourRieszProjection_eq_cfcL
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    Γ.contourRieszProjection =
      cfcL (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        Γ.integratedContourResolventSymbol := by
  rw [contourRieszProjection, Γ.resolventCurveIntegral_eq_cfcL]
  unfold SpectralSeparatingContour.integratedContourResolventSymbol
  rw [map_smul]

/-- At a real spectral point, the integrated continuous symbol is the scalar
Riesz transform recorded by the contour. -/
theorem SpectralSeparatingContour.integratedContourResolventSymbol_apply
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) {lam : ℝ}
    (hlam : lam ∈ realSpectrum A) :
    Γ.integratedContourResolventSymbol
        ⟨(lam : ℂ), by
          have hAsa : IsSelfAdjoint A :=
            ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
              Γ.selfAdjoint
          rw [← hAsa.spectrumRestricts.algebraMap_image]
          exact ⟨lam, hlam, rfl⟩⟩ =
      Γ.geometric.scalarRieszTransform lam := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr Γ.selfAdjoint
  have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
    rw [← hAsa.spectrumRestricts.algebraMap_image]
    exact ⟨lam, hlam, rfl⟩
  let x : spectrum ℂ A := ⟨(lam : ℂ), hlamC⟩
  have hint := Γ.intervalIntegrable_contourResolventSymbol
  have heval :
      (∫ t in (0 : ℝ)..1,
        Γ.geometric.contourResolventSymbol A t) x =
      ∫ t in (0 : ℝ)..1,
        Γ.geometric.contourResolventSymbol A t x := by
    simpa only [intervalIntegral.integral_of_le zero_le_one] using
      (ContinuousMap.integral_apply hint.1 x)
  change rieszNormalization *
      (∫ t in (0 : ℝ)..1,
        Γ.geometric.contourResolventSymbol A t) x =
    Γ.geometric.scalarRieszTransform lam
  rw [heval]
  unfold PiecewiseC1ClosedContour.scalarRieszTransform
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  let τ : unitInterval := ⟨t, ht⟩
  have hparam : Γ.geometric.param t = Γ.path τ := by
    simpa only [PiecewiseC1ClosedContour.param] using Γ.path.extend_apply ht
  have hcont : ContinuousOn
      (fun w : ℂ =>
        derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t *
          (w - Γ.geometric.param t)⁻¹)
      (spectrum ℂ A) := by
    rw [hparam]
    exact continuousOn_const.mul (Γ.continuousOn_resolventSymbol τ)
  change
    (Γ.geometric.contourResolventSymbol A t) x =
      ((lam : ℂ) - Γ.geometric.param t)⁻¹ *
        derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t
  unfold PiecewiseC1ClosedContour.contourResolventSymbol
  change
    (ContinuousMap.mkD
      ((spectrum ℂ A).restrict fun w : ℂ =>
        derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t *
          (w - Γ.geometric.param t)⁻¹) 0) x =
      ((lam : ℂ) - Γ.geometric.param t)⁻¹ *
        derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t
  rw [ContinuousMap.mkD_apply_of_continuousOn hcont]
  change
    derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t *
        ((lam : ℂ) - Γ.geometric.param t)⁻¹ =
      ((lam : ℂ) - Γ.geometric.param t)⁻¹ *
        derivWithin Γ.geometric.param (Set.Icc (0 : ℝ) 1) t
  exact mul_comm _ _

/-- On the real spectrum, the integrated continuous symbol is exactly the
selected-set indicator. -/
theorem SpectralSeparatingContour.integratedContourResolventSymbol_eq_selector
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) {lam : ℝ}
    (hlam : lam ∈ realSpectrum A) :
    Γ.integratedContourResolventSymbol
        ⟨(lam : ℂ), by
          have hAsa : IsSelfAdjoint A :=
            ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
              Γ.selfAdjoint
          rw [← hAsa.spectrumRestricts.algebraMap_image]
          exact ⟨lam, hlam, rfl⟩⟩ =
      spectralSelector s lam := by
  rw [Γ.integratedContourResolventSymbol_apply hlam]
  exact Γ.scalarRieszTransform_eq_spectralSelector hlam

end BoundedSpectralProjection

end DavisKahanExt
end ForMathlib
