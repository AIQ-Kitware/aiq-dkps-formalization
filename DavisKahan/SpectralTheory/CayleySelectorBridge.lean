/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.SpectralTheory.ResolventOperator
import DavisKahan.Interop.Spectra.Basic
import DavisKahan.Interop.Spectra.BoundedSelfAdjointSpectralProjection
import Spectra.SpectralTheory.ResolventForm
import Spectra.StoneBridge.CalculusBridge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Cayley/selector bridge for bounded spectral projections

The contour-free half of the spectral-identification machinery, split out of
`ContinuationSpectralIdentification` so that consumers that produce their own
continuous spectral symbol (for example the circle Riesz projection in
`Frontier/RieszCircle.lean`) can identify the Spectra bounded selector calculus
with a Mathlib continuous-functional-calculus value without importing the
contour-continuation chain (which is currently blocked on `SinTheta/General`).

Contents: the selected-set spectral selector; the identification of the
genuine bounded spectral projection with the Spectra selector calculus; the
project resolvent as a continuous functional calculus; the interval-integral /
calculus exchange; the bounded Cayley/Möbius bridge; and the contour-free
generalization of the selector/cfcL identification, parametrized by any
continuous spectral function that agrees with the selector on the real
spectrum.
-/

namespace TauCeti
namespace DavisKahanExt

open Set
open MeasureTheory
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory
open DavisKahan.Experimental.Foundation
open DavisKahan.Experimental.SpectraBridge

universe v

section CayleySelectorBridge

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

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

/-- **The genuine bounded spectral projection is the continuous functional
calculus of any continuous symbol agreeing with the selector on the spectrum.**

Until 2026-07-29 this went through Spectra in two steps — the projection was
Spectra's group calculus of the selector, and that calculus was identified with
`cfcL` by a Cayley-transform argument.  Both steps collapse into
`TauCeti.BorelCalculus.boundedPVM_proj_eq_cfcHom`: the native Borel calculus of
a bounded self-adjoint operator is indexed along the real part of its own
spectrum, so a continuous symbol agreeing with the indicator *there* has the
same calculus image, definitionally. -/
theorem boundedSelfAdjointSpectralProjection_eq_cfcL_of_selector
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s)
    (g : C(spectrum ℂ A, ℂ))
    (hg : ∀ (lam : ℝ) (hlam : (lam : ℂ) ∈ spectrum ℂ A),
      g ⟨(lam : ℂ), hlam⟩ = spectralSelector s lam) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      cfcL (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal g := by
  refine TauCeti.DavisKahanExt.boundedSelfAdjointSpectralProjection_eq_cfcL_of_agrees
    A hA s hs g fun w => ?_
  have hcoe := TauCeti.DavisKahanExt.coe_reCoord A hA w
  have hmem : ((TauCeti.BorelCalculus.reCoord w : ℝ) : ℂ) ∈ spectrum ℂ A := by
    rw [hcoe]; exact w.2
  have h1 : g w = spectralSelector s (TauCeti.BorelCalculus.reCoord w) := by
    rw [← hg (TauCeti.BorelCalculus.reCoord w) hmem]
    congr 1
    exact Subtype.ext hcoe.symm
  rw [h1, spectralSelector]
  by_cases hw : TauCeti.BorelCalculus.reCoord w ∈ s <;> simp [hw, Set.mem_preimage]

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

omit [CompleteSpace H] in
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
    simp [Aop]
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
    simpa [mul_apply_eq_comp] using hcancel

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

theorem continuous_cayleySelectorPullback_of_agrees
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) (s : Set ℝ)
    (g : C(spectrum ℂ A, ℂ))
    (hg : ∀ (lam : ℝ) (hlam : (lam : ℂ) ∈ spectrum ℂ A),
      g ⟨(lam : ℂ), hlam⟩ = spectralSelector s lam) :
    Continuous (fun w : spectrum ℂ
      (Spectra.Cayley.cayley
        (boundedSelfAdjointOperator A hA).selfAdjoint) =>
      spectralSelector s
        (Spectra.Cayley.inverseMobiusReal
          (boundedSelfAdjointOperator A hA).selfAdjoint w)) := by
  let hSA := (boundedSelfAdjointOperator A hA).selfAdjoint
  let invMap := boundedCayleySpectrumInverse A hA
  have hcontinuous : Continuous (fun w => g (invMap w)) :=
    g.continuous.comp invMap.continuous
  apply hcontinuous.congr
  intro w
  let lam : ℝ := Spectra.Cayley.inverseMobiusReal hSA w
  have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
    rw [Spectra.Cayley.inverseMobiusReal_coe hSA w]
    exact (invMap w).property
  have hsub : invMap w = ⟨(lam : ℂ), hlamC⟩ := by
    apply Subtype.ext
    exact (Spectra.Cayley.inverseMobiusReal_coe hSA w).symm
  simpa [lam, hsub] using hg lam hlamC

/-- The Spectra bounded selector calculus equals the Mathlib continuous
functional calculus of any continuous spectral function that agrees with the
selected-set indicator at every real spectral point.  Contour-free
generalization of `SpectralSeparatingContour.spectralCalculus_selector_eq_cfcL`;
the function `g` plays the role of the integrated contour symbol. -/
theorem spectralCalculus_selector_eq_cfcL_of_agrees
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s)
    (g : C(spectrum ℂ A, ℂ))
    (hg : ∀ (lam : ℝ) (hlam : (lam : ℂ) ∈ spectrum ℂ A),
      g ⟨(lam : ℂ), hlam⟩ = spectralSelector s lam) :
    Spectra.QuantumMechanics.SpectralTheory.spectralCalculus
        (Spectra.YosidaHille.genToGroup
          (boundedSelfAdjointOperator A hA).selfAdjoint)
        (spectralSelector s)
        (spectralSelector_measurable s hs)
        (spectralSelector_bounded s) =
      cfcL
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          hA).isStarNormal
        g := by
  classical
  by_cases hH : Nontrivial H
  · letI : Nontrivial H := hH
    let hSA :=
      (boundedSelfAdjointOperator A hA).selfAdjoint
    let U : H →L[ℂ] H := Spectra.Cayley.cayley hSA
    let G : ℂ → ℂ := fun w =>
      spectralSelector s (Spectra.Cayley.inverseMobius w).re
    have hGrestrict : Continuous
        ((spectrum ℂ U).restrict G) := by
      apply (continuous_cayleySelectorPullback_of_agrees A hA s g hg).congr
      intro w
      simp only [Set.restrict_apply, G, U,
        Spectra.Cayley.inverseMobiusReal]
    have hGcont : ContinuousOn G (spectrum ℂ U) :=
      continuousOn_iff_continuous_restrict.mpr hGrestrict
    have hbridge :
        Spectra.QuantumMechanics.SpectralTheory.spectralCalculus
            (Spectra.YosidaHille.genToGroup hSA)
            (spectralSelector s)
            (spectralSelector_measurable s hs)
            (spectralSelector_bounded s) =
          cfc G U := by
      rw [← Spectra.YosidaHille.stoneGroup_eq_genToGroup hSA]
      calc
        Spectra.QuantumMechanics.SpectralTheory.spectralCalculus
            (Spectra.Cayley.stoneGroup hSA)
            (spectralSelector s)
            (spectralSelector_measurable s hs)
            (spectralSelector_bounded s) =
          cfcHom (Spectra.Cayley.cayley_isStarNormal hSA)
            (⟨fun w => spectralSelector s
                (Spectra.Cayley.inverseMobiusReal hSA w),
              continuous_cayleySelectorPullback_of_agrees A hA s g hg⟩ :
              C(spectrum ℂ (Spectra.Cayley.cayley hSA), ℂ)) :=
          Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_stoneGroup_eq_cfcHom
            hSA (spectralSelector s)
            (spectralSelector_measurable s hs)
            (spectralSelector_bounded s)
            (continuous_cayleySelectorPullback_of_agrees A hA s g hg)
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
      continuousOn_boundedMobiusSymbol_spectrum A hA
    have hU : U = cfc boundedMobiusSymbol A := by
      simpa [U, hSA] using
        (cayley_boundedSelfAdjointOperator_eq_cfc A hA)
    have hspec : spectrum ℂ U =
        boundedMobiusSymbol '' spectrum ℂ A := by
      rw [hU]
      exact cfc_map_spectrum
        (f := boundedMobiusSymbol) (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          hA).isStarNormal hmobcont
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
          (spectralSelector_measurable s hs)
          (spectralSelector_bounded s) =
        cfc G U := hbridge
      _ = cfc G (cfc boundedMobiusSymbol A) := by rw [← hU]
      _ = cfc (G ∘ boundedMobiusSymbol) A := by
        symm
        exact cfc_comp
          (g := G) (f := boundedMobiusSymbol) (a := A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
            hA).isStarNormal hGimage hmobcont
      _ = cfcL
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
            hA).isStarNormal
          g := by
        rw [cfc_eq_cfcL
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
            hA).isStarNormal hcompcont]
        congr 1
        ext z
        have hAsa : IsSelfAdjoint A :=
          ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
        rcases z with ⟨z, hz⟩
        obtain ⟨lam, hlam, rfl⟩ :=
          hAsa.spectrumRestricts.algebraMap_image.symm ▸ hz
        have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
          rw [← hAsa.spectrumRestricts.algebraMap_image]
          exact ⟨lam, hlam, rfl⟩
        change
          spectralSelector s
              (Spectra.Cayley.inverseMobius
                (boundedMobiusSymbol (lam : ℂ))).re =
            g ⟨(lam : ℂ), by
                rw [← hAsa.spectrumRestricts.algebraMap_image]
                exact ⟨lam, hlam, rfl⟩⟩
        rw [inverseMobius_boundedMobiusSymbol_ofReal]
        simp only [Complex.ofReal_re]
        exact (hg lam hlamC).symm
  · haveI : Subsingleton H := not_nontrivial_iff_subsingleton.mp hH
    exact Subsingleton.elim _ _

end CayleySelectorBridge

end DavisKahanExt
end TauCeti