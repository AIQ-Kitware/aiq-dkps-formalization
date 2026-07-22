/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationAssembly
import DavisKahan.Experimental.InfiniteDimensional.Core.SpectralProjection
import Spectra.SpectralTheory.ResolventForm
import Spectra.StoneBridge.CalculusBridge
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
projection is the bounded spectral calculus of that indicator.  The operator
half transports the contour integral through Mathlib's continuous calculus and
identifies it with Spectra's bounded measurable calculus through the Cayley
transform.
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


/-! ## Compatibility of the bounded Spectra and Mathlib calculi -/

/-- The scalar Möbius map used by the Cayley transform. -/
noncomputable def boundedMobiusSymbol (z : ℂ) : ℂ :=
  (z - Complex.I) * (z + Complex.I)⁻¹

/-- The inverse Möbius map recovers every real scalar. -/
theorem inverseMobius_boundedMobiusSymbol_ofReal (lam : ℝ) :
    Spectra.Cayley.inverseMobius (boundedMobiusSymbol (lam : ℂ)) = (lam : ℂ) := by
  have hne : (lam : ℂ) + Complex.I ≠ 0 :=
    Spectra.Cayley.real_add_I_ne_zero lam
  unfold boundedMobiusSymbol Spectra.Cayley.inverseMobius
  rw [Spectra.Cayley.one_add_mobius lam hne,
    Spectra.Cayley.one_sub_mobius lam hne]
  field_simp [hne, Complex.I_ne_zero]

/-- A real point belongs to the real spectrum once its complex coercion belongs
 to the complex spectrum of a self-adjoint operator. -/
theorem mem_realSpectrum_of_coe_mem_spectrum
    (A : H →L[ℂ] H) (_hA : IsSelfAdjointOperator A) {lam : ℝ}
    (hlam : (lam : ℂ) ∈ spectrum ℂ A) :
    lam ∈ realSpectrum A :=
  hlam

/-- The Möbius symbol is continuous on the spectrum of a bounded
self-adjoint operator. -/
theorem continuousOn_boundedMobiusSymbol_spectrum
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    ContinuousOn boundedMobiusSymbol (spectrum ℂ A) := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hne : ∀ z ∈ spectrum ℂ A, z + Complex.I ≠ 0 := by
    intro z hz
    obtain ⟨lam, hlam, rfl⟩ :=
      hAsa.spectrumRestricts.algebraMap_image.symm ▸ hz
    exact Spectra.Cayley.real_add_I_ne_zero lam
  unfold boundedMobiusSymbol
  exact (continuous_id.sub continuous_const).continuousOn.mul
    ((continuous_id.add continuous_const).continuousOn.inv₀ hne)

/-- The Spectra resolvent at negative imaginary one agrees with the project
resolvent of the original bounded operator. -/
theorem resolventAtNegI_boundedSelfAdjointOperator_eq
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    Spectra.Resolvent.resolventAtNegI
        (Spectra.Operator.isFormalAdjoint_self_of_isSelfAdjoint
          (boundedSelfAdjointOperator A hA).selfAdjoint)
        (Spectra.YosidaHille.isSelfAdjoint_to_surjective
          (boundedSelfAdjointOperator A hA).selfAdjoint).1 =
      resolventOperator A (-Complex.I) := by
  let Aop := boundedSelfAdjointOperator A hA
  let hSA := Aop.selfAdjoint
  let hsym :=
    Spectra.Operator.isFormalAdjoint_self_of_isSelfAdjoint hSA
  let hplus := (Spectra.YosidaHille.isSelfAdjoint_to_surjective hSA).1
  change Spectra.Resolvent.resolventAtNegI hsym hplus =
    resolventOperator A (-Complex.I)
  have hsep : ∀ lam ∈ realSpectrum A,
      (1 : ℝ) ≤ ‖(-Complex.I : ℂ) - (lam : ℂ)‖ := by
    intro lam hlam
    calc
      (1 : ℝ) = |((-Complex.I : ℂ) - (lam : ℂ)).im| := by simp
      _ ≤ ‖(-Complex.I : ℂ) - (lam : ℂ)‖ :=
        Complex.abs_im_le_norm _
  have hz : InResolventSet A (-Complex.I) :=
    complex_inResolventSet_of_distance A hA (-Complex.I) 1 zero_lt_one hsep
  apply ContinuousLinearMap.ext
  intro x
  have hdom : Aop.toLinearPMap.domain = ⊤ := by
    change Aop.domain = ⊤
    simpa [Aop] using boundedSelfAdjointOperator_domain A hA
  refine Spectra.Resolvent.resolvent_at_neg_i_unique hsym x
    (Spectra.Resolvent.resolventAtNegI hsym hplus x)
    (resolventOperator A (-Complex.I) x) ?_ ?_ ?_ ?_
  · simpa [Spectra.Resolvent.resolventAtNegI,
      Spectra.Resolvent.resolventAtImaginary, Spectra.Resolvent.Rplus] using
      (Spectra.Resolvent.Rplus_mem hplus x)
  · rw [hdom]
    exact Submodule.mem_top
  · simpa [Spectra.Resolvent.resolventAtNegI,
      Spectra.Resolvent.resolventAtImaginary, Spectra.Resolvent.Rplus] using
      (Spectra.Resolvent.Rplus_eq hplus x)
  · have hcancel := congrArg
        (fun T : H →L[ℂ] H => T x)
        (mul_resolventOperator_cancel A hz)
    change
      A (resolventOperator A (-Complex.I) x) +
        Complex.I • resolventOperator A (-Complex.I) x = x
    simpa [ContinuousLinearMap.mul_apply] using hcancel

/-- For a bounded self-adjoint operator, Spectra's Cayley transform is the
Mathlib continuous functional calculus of the scalar Möbius map. -/
theorem cayley_boundedSelfAdjointOperator_eq_cfc
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    Spectra.Cayley.cayley (boundedSelfAdjointOperator A hA).selfAdjoint =
      cfc boundedMobiusSymbol A := by
  have hsep : ∀ lam ∈ realSpectrum A,
      (1 : ℝ) ≤ ‖(-Complex.I : ℂ) - (lam : ℂ)‖ := by
    intro lam hlam
    calc
      (1 : ℝ) = |((-Complex.I : ℂ) - (lam : ℂ)).im| := by simp
      _ ≤ ‖(-Complex.I : ℂ) - (lam : ℂ)‖ :=
        Complex.abs_im_le_norm _
  have hres : resolventOperator A (-Complex.I) =
      cfc (fun z : ℂ => (z + Complex.I)⁻¹) A := by
    simpa only [sub_neg_eq_add] using
      (resolventOperator_eq_cfc_resolventSymbol
        A hA (-Complex.I) 1 zero_lt_one hsep)
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hne : ∀ z ∈ spectrum ℂ A, z + Complex.I ≠ 0 := by
    intro z hz
    obtain ⟨lam, hlam, rfl⟩ :=
      hAsa.spectrumRestricts.algebraMap_image.symm ▸ hz
    exact Spectra.Cayley.real_add_I_ne_zero lam
  have hinv : ContinuousOn (fun z : ℂ => (z + Complex.I)⁻¹)
      (spectrum ℂ A) :=
    (continuous_id.add continuous_const).continuousOn.inv₀ hne
  have hscaled : ContinuousOn
      (fun z : ℂ => (2 * Complex.I) * (z + Complex.I)⁻¹)
      (spectrum ℂ A) := continuousOn_const.mul hinv
  unfold Spectra.Cayley.cayley Spectra.Cayley.cayleyTransform
  rw [resolventAtNegI_boundedSelfAdjointOperator_eq A hA, hres]
  change
    (1 : H →L[ℂ] H) -
        (2 * Complex.I) • cfc (fun z : ℂ => (z + Complex.I)⁻¹) A =
      cfc boundedMobiusSymbol A
  calc
    (1 : H →L[ℂ] H) -
        (2 * Complex.I) • cfc (fun z : ℂ => (z + Complex.I)⁻¹) A =
      cfc (fun z : ℂ => 1 - (2 * Complex.I) * (z + Complex.I)⁻¹) A := by
        rw [cfc_sub (fun _ : ℂ => (1 : ℂ))
          (fun z : ℂ => (2 * Complex.I) * (z + Complex.I)⁻¹) A
          continuousOn_const hscaled,
          cfc_const_one ℂ A,
          cfc_const_mul (2 * Complex.I)
            (fun z : ℂ => (z + Complex.I)⁻¹) A hinv]
    _ = cfc boundedMobiusSymbol A := by
      apply cfc_congr
      intro z hz
      have hzI : z + Complex.I ≠ 0 := hne z hz
      unfold boundedMobiusSymbol
      field_simp [hzI]
      ring

/-- The Möbius map bundled as a continuous function on the bounded complex
spectrum. -/
noncomputable def boundedMobiusSpectrumSymbol
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    C(spectrum ℂ A, ℂ) :=
  ⟨fun z => boundedMobiusSymbol z,
    (continuousOn_boundedMobiusSymbol_spectrum A hA).restrict⟩

/-- Bundled form of the bounded Cayley/CFC identification. -/
theorem cayley_boundedSelfAdjointOperator_eq_cfcHom
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    Spectra.Cayley.cayley (boundedSelfAdjointOperator A hA).selfAdjoint =
      cfcHom
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
        (boundedMobiusSpectrumSymbol A hA) := by
  rw [cayley_boundedSelfAdjointOperator_eq_cfc A hA]
  rw [cfc_apply boundedMobiusSymbol A
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
    (continuousOn_boundedMobiusSymbol_spectrum A hA)]
  rfl

/-- The point one is absent from the Cayley spectrum of a bounded
self-adjoint operator. -/
theorem one_not_mem_spectrum_cayley_boundedSelfAdjointOperator
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    (1 : ℂ) ∉ spectrum ℂ
      (Spectra.Cayley.cayley
        (boundedSelfAdjointOperator A hA).selfAdjoint) := by
  intro hone
  let hnormal : IsStarNormal A :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
  let f := boundedMobiusSpectrumSymbol A hA
  have hone' : (1 : ℂ) ∈ spectrum ℂ (cfcHom hnormal f) := by
    rw [← cayley_boundedSelfAdjointOperator_eq_cfcHom A hA]
    exact hone
  rw [cfcHom_map_spectrum] at hone'
  obtain ⟨z, hz⟩ := hone'
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  rcases z with ⟨z, hzspec⟩
  obtain ⟨lam, hlam, rfl⟩ :=
    hAsa.spectrumRestricts.algebraMap_image.symm ▸ hzspec
  have hz' : boundedMobiusSymbol (lam : ℂ) = 1 := by
    simpa [f, boundedMobiusSpectrumSymbol] using hz
  have hne := Spectra.Cayley.one_sub_mobius_ne_zero lam
    (Spectra.Cayley.real_add_I_ne_zero lam)
  apply hne
  change (1 : ℂ) - boundedMobiusSymbol (lam : ℂ) = 0
  rw [hz']
  simp

/-- Inverse Möbius maps the bounded Cayley spectrum back into the complex
spectrum of the original operator. -/
theorem inverseMobius_mem_spectrum_of_mem_cayley_bounded
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (w : spectrum ℂ
      (Spectra.Cayley.cayley
        (boundedSelfAdjointOperator A hA).selfAdjoint)) :
    Spectra.Cayley.inverseMobius (w : ℂ) ∈ spectrum ℂ A := by
  let hnormal : IsStarNormal A :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
  let f := boundedMobiusSpectrumSymbol A hA
  have hw : (w : ℂ) ∈ spectrum ℂ (cfcHom hnormal f) := by
    rw [← cayley_boundedSelfAdjointOperator_eq_cfcHom A hA]
    exact w.property
  rw [cfcHom_map_spectrum] at hw
  obtain ⟨z, hz⟩ := hw
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  rcases z with ⟨z, hzspec⟩
  obtain ⟨lam, hlam, rfl⟩ :=
    hAsa.spectrumRestricts.algebraMap_image.symm ▸ hzspec
  have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
    rw [← hAsa.spectrumRestricts.algebraMap_image]
    exact ⟨lam, hlam, rfl⟩
  have hz' : boundedMobiusSymbol (lam : ℂ) = (w : ℂ) := by
    simpa [f, boundedMobiusSpectrumSymbol] using hz
  change Spectra.Cayley.inverseMobius (w : ℂ) ∈ spectrum ℂ A
  rw [← hz']
  simpa using
    (show Spectra.Cayley.inverseMobius
        (boundedMobiusSymbol (lam : ℂ)) ∈ spectrum ℂ A by
      rw [inverseMobius_boundedMobiusSymbol_ofReal]
      exact hlamC)

/-- The inverse Möbius map from the bounded Cayley spectrum to the original
complex spectrum, bundled continuously. -/
noncomputable def boundedCayleySpectrumInverse
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    C(spectrum ℂ
        (Spectra.Cayley.cayley
          (boundedSelfAdjointOperator A hA).selfAdjoint),
      spectrum ℂ A) := by
  let U := Spectra.Cayley.cayley
    (boundedSelfAdjointOperator A hA).selfAdjoint
  have hne : ∀ w ∈ spectrum ℂ U, (1 : ℂ) - w ≠ 0 := by
    intro w hw
    apply sub_ne_zero.mpr
    intro h
    apply one_not_mem_spectrum_cayley_boundedSelfAdjointOperator A hA
    rw [h]
    exact hw
  have hcont : ContinuousOn Spectra.Cayley.inverseMobius
      (spectrum ℂ U) := by
    unfold Spectra.Cayley.inverseMobius
    exact (continuous_const.mul (continuous_const.add continuous_id)).continuousOn.div
      (continuous_const.sub continuous_id).continuousOn hne
  exact
    { toFun := fun w =>
        ⟨Spectra.Cayley.inverseMobius (w : ℂ),
          inverseMobius_mem_spectrum_of_mem_cayley_bounded A hA w⟩
      continuous_toFun := hcont.restrict.subtype_mk
        (fun w => inverseMobius_mem_spectrum_of_mem_cayley_bounded A hA w) }

/-- The selector pulled back to the bounded Cayley spectrum is continuous,
because on that spectrum it is the already continuous integrated contour
symbol. -/
theorem SpectralSeparatingContour.continuous_cayleySelectorPullback
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    Continuous (fun w : spectrum ℂ
      (Spectra.Cayley.cayley
        (boundedSelfAdjointOperator A Γ.selfAdjoint).selfAdjoint) =>
      spectralSelector s
        (Spectra.Cayley.inverseMobiusReal
          (boundedSelfAdjointOperator A Γ.selfAdjoint).selfAdjoint w)) := by
  let hSA :=
    (boundedSelfAdjointOperator A Γ.selfAdjoint).selfAdjoint
  let invMap := boundedCayleySpectrumInverse A Γ.selfAdjoint
  have hcontinuous : Continuous
      (fun w => Γ.integratedContourResolventSymbol (invMap w)) :=
    Γ.integratedContourResolventSymbol.continuous.comp invMap.continuous
  apply hcontinuous.congr
  intro w
  let lam : ℝ := Spectra.Cayley.inverseMobiusReal hSA w
  have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
    rw [Spectra.Cayley.inverseMobiusReal_coe hSA w]
    exact (invMap w).property
  have hlam : lam ∈ realSpectrum A :=
    mem_realSpectrum_of_coe_mem_spectrum A Γ.selfAdjoint hlamC
  have hsub : invMap w = ⟨(lam : ℂ), hlamC⟩ := by
    apply Subtype.ext
    exact (Spectra.Cayley.inverseMobiusReal_coe hSA w).symm
  simpa [lam, hsub] using
    Γ.integratedContourResolventSymbol_eq_selector hlam

/-- The Spectra bounded selector calculus equals the Mathlib continuous
functional calculus of the integrated contour symbol. -/
theorem SpectralSeparatingContour.spectralCalculus_selector_eq_cfcL
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    Spectra.QuantumMechanics.SpectralTheory.spectralCalculus
        (Spectra.YosidaHille.genToGroup
          (boundedSelfAdjointOperator A Γ.selfAdjoint).selfAdjoint)
        (spectralSelector s)
        (spectralSelector_measurable s Γ.measurable_selected)
        (spectralSelector_bounded s) =
      cfcL
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal
        Γ.integratedContourResolventSymbol := by
  classical
  by_cases hH : Nontrivial H
  · letI : Nontrivial H := hH
    let hSA :=
      (boundedSelfAdjointOperator A Γ.selfAdjoint).selfAdjoint
    let U : H →L[ℂ] H := Spectra.Cayley.cayley hSA
    let G : ℂ → ℂ := fun w =>
      spectralSelector s (Spectra.Cayley.inverseMobius w).re
    have hGrestrict : Continuous
        ((spectrum ℂ U).restrict G) := by
      apply Γ.continuous_cayleySelectorPullback.congr
      intro w
      simp only [Set.restrict_apply, G, U, hSA,
        Spectra.Cayley.inverseMobiusReal]
    have hGcont : ContinuousOn G (spectrum ℂ U) :=
      continuousOn_iff_continuous_restrict.mpr hGrestrict
    have hbridge :
        Spectra.QuantumMechanics.SpectralTheory.spectralCalculus
            (Spectra.YosidaHille.genToGroup hSA)
            (spectralSelector s)
            (spectralSelector_measurable s Γ.measurable_selected)
            (spectralSelector_bounded s) =
          cfc G U := by
      rw [← Spectra.YosidaHille.stoneGroup_eq_genToGroup hSA]
      calc
        Spectra.QuantumMechanics.SpectralTheory.spectralCalculus
            (Spectra.Cayley.stoneGroup hSA)
            (spectralSelector s)
            (spectralSelector_measurable s Γ.measurable_selected)
            (spectralSelector_bounded s) =
          cfcHom (Spectra.Cayley.cayley_isStarNormal hSA)
            (⟨fun w => spectralSelector s
                (Spectra.Cayley.inverseMobiusReal hSA w),
              Γ.continuous_cayleySelectorPullback⟩ :
              C(spectrum ℂ (Spectra.Cayley.cayley hSA), ℂ)) :=
          Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_stoneGroup_eq_cfcHom
            hSA (spectralSelector s)
            (spectralSelector_measurable s Γ.measurable_selected)
            (spectralSelector_bounded s)
            Γ.continuous_cayleySelectorPullback
        _ = cfcHom (Spectra.Cayley.cayley_isStarNormal hSA)
            (⟨(spectrum ℂ U).restrict G, hGrestrict⟩ :
              C(spectrum ℂ U, ℂ)) := by
          apply congrArg (cfcHom (Spectra.Cayley.cayley_isStarNormal hSA))
          ext w
          change spectralSelector s
              (Spectra.Cayley.inverseMobius (w : ℂ)).re =
            spectralSelector s
              (Spectra.Cayley.inverseMobius (w : ℂ)).re
          rfl
        _ = cfc G U :=
          (cfc_apply G U (Spectra.Cayley.cayley_isStarNormal hSA) hGcont).symm
    have hmobcont : ContinuousOn boundedMobiusSymbol (spectrum ℂ A) :=
      continuousOn_boundedMobiusSymbol_spectrum A Γ.selfAdjoint
    have hU : U = cfc boundedMobiusSymbol A := by
      simpa [U, hSA] using
        (cayley_boundedSelfAdjointOperator_eq_cfc A Γ.selfAdjoint)
    have hspec : spectrum ℂ U =
        boundedMobiusSymbol '' spectrum ℂ A := by
      rw [hU]
      exact cfc_map_spectrum
        (f := boundedMobiusSymbol) (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          Γ.selfAdjoint).isStarNormal hmobcont
    have hGimage : ContinuousOn G
        (boundedMobiusSymbol '' spectrum ℂ A) := by
      rwa [← hspec]
    have hcompcont : ContinuousOn (G ∘ boundedMobiusSymbol)
        (spectrum ℂ A) :=
      hGimage.comp hmobcont (fun z hz => ⟨z, hz, rfl⟩)
    calc
      Spectra.QuantumMechanics.SpectralTheory.spectralCalculus
          (Spectra.YosidaHille.genToGroup hSA)
          (spectralSelector s)
          (spectralSelector_measurable s Γ.measurable_selected)
          (spectralSelector_bounded s) =
        cfc G U := hbridge
      _ = cfc G (cfc boundedMobiusSymbol A) := by rw [← hU]
      _ = cfc (G ∘ boundedMobiusSymbol) A := by
        symm
        exact cfc_comp
          (g := G) (f := boundedMobiusSymbol) (a := A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
            Γ.selfAdjoint).isStarNormal hGimage hmobcont
      _ = cfcL
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
            Γ.selfAdjoint).isStarNormal
          Γ.integratedContourResolventSymbol := by
        rw [cfc_eq_cfcL
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
            Γ.selfAdjoint).isStarNormal hcompcont]
        congr 1
        ext z
        have hAsa : IsSelfAdjoint A :=
          ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr Γ.selfAdjoint
        rcases z with ⟨z, hz⟩
        obtain ⟨lam, hlam, rfl⟩ :=
          hAsa.spectrumRestricts.algebraMap_image.symm ▸ hz
        change
          spectralSelector s
              (Spectra.Cayley.inverseMobius
                (boundedMobiusSymbol (lam : ℂ))).re =
            Γ.integratedContourResolventSymbol
              ⟨(lam : ℂ), by
                rw [← hAsa.spectrumRestricts.algebraMap_image]
                exact ⟨lam, hlam, rfl⟩⟩
        rw [inverseMobius_boundedMobiusSymbol_ofReal]
        simp only [Complex.ofReal_re]
        exact (Γ.integratedContourResolventSymbol_eq_selector hlam).symm
  · haveI : Subsingleton H := not_nontrivial_iff_subsingleton.mp hH
    exact Subsingleton.elim _ _

/-- The normalized contour Riesz operator is the genuine Spectra projection
onto the selected bounded spectral subspace. -/
theorem SpectralSeparatingContour.contourRieszProjection_eq_boundedSelfAdjointSpectralProjection
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    Γ.contourRieszProjection =
      boundedSelfAdjointSpectralProjection
        A Γ.selfAdjoint s Γ.measurable_selected := by
  rw [Γ.contourRieszProjection_eq_cfcL,
    boundedSelfAdjointSpectralProjection_eq_spectralCalculus_selector]
  exact Γ.spectralCalculus_selector_eq_cfcL.symm

/-- Every spectrally separating contour produces an orthogonal projection. -/
theorem SpectralSeparatingContour.contourRieszProjection_isOrthogonalProjection
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    IsOrthogonalProjection Γ.contourRieszProjection :=
  Γ.contourRieszProjection_isOrthogonalProjection_of_eq
    Γ.contourRieszProjection_eq_boundedSelfAdjointSpectralProjection

/-- A common geometric contour that separates every point of an affine path
produces a path of orthogonal fixed-contour Riesz projections. -/
theorem fixedContourRieszOperator_operatorPath_isOrthogonalProjection
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (s : Set ℝ)
    (hseparating : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      SpectralSeparatingContour (operatorPath A V t) s)
    (hgeometric : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      (hseparating t ht).geometric = Γ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsOrthogonalProjection
        (fixedContourRieszOperator Γ (operatorPath A V t)) := by
  intro t ht
  let Γt := hseparating t ht
  have hfixed :
      fixedContourRieszOperator Γ (operatorPath A V t) =
        Γt.contourRieszProjection := by
    rw [← hgeometric t ht]
    exact fixedContourRieszOperator_eq_contourRieszProjection Γt
  rw [hfixed]
  exact Γt.contourRieszProjection_isOrthogonalProjection

end BoundedSpectralProjection

end DavisKahanExt
end ForMathlib
