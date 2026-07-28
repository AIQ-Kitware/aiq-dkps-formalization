/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.ClosedOperator
import DavisKahan.Sylvester.ClosedSylvesterEquation
import Spectra.QuantumMechanics.BornRule.Observable
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Genuine spectral half-line localization

This leaf converts half-line containment of the genuine Spectra spectrum of a
closed self-adjoint operator into the quadratic-form semibounds consumed by the
ordered branches of the unbounded Sylvester theorem.

The proof uses the Born measure of each domain vector.  Its support lies in the
operator spectrum, while its first moment is the corresponding diagonal matrix
element.  Integrating the pointwise half-line inequality therefore gives the
required form bound.
-/

open scoped InnerProductSpace
open MeasureTheory

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

open Spectra.QuantumMechanics
open Spectra.QuantumMechanics.BornRule.Observable
open Spectra.QuantumMechanics.SpectralTheory
open TauCeti.DavisKahan.Experimental.ExactSinTheta

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine spectral containment in `[c, ∞)` implies the matching lower
quadratic-form bound. -/
theorem semiboundedBelow_of_spectrum_subset_Ici
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {c : ℝ}
    (hσ : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A.toLinearPMap ⊆
        Set.Ici c) :
    SemiboundedBelow A c := by
  intro x
  let Aop := closedOperatorToSpectra A hA
  let μ : Measure ℝ := Aop.bornMeasure (x : H)
  letI : IsFiniteMeasure μ := by
    change IsFiniteMeasure (Aop.spectralPVM.diag (x : H))
    exact Aop.spectralPVM.diag_finite (x : H)
  have hint : Integrable (fun s : ℝ => s) μ := by
    change Integrable (fun s : ℝ => s)
      ((Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM hA).diag (x : H))
    exact spectralPVM_integrable_id hA (x : H) x.property
  have hval : ∫ s, s ∂μ = (⟪(x : H), A.toLinearMap x⟫_ℂ).re := by
    simpa [μ, Aop,
      Spectra.Operator.SelfAdjointOperator.bornMeasure,
      Spectra.QuantumMechanics.BornRule.Moments.bornExpectation] using
      bornExpectation_eq_inner Aop x.property
  have hsupp : μ.support ⊆ Set.Ici c := by
    intro s hs
    exact hσ (bornMeasure_support_subset_spectrum Aop (x : H) hs)
  have hae : ∀ᵐ s ∂μ, c ≤ s := by
    filter_upwards [Measure.support_mem_ae (μ := μ)] with s hs using hsupp hs
  calc
    c * ‖(x : H)‖ ^ 2 = ∫ _s, c ∂μ := by
      rw [integral_const, smul_eq_mul, Measure.real_def]
      change c * ‖(x : H)‖ ^ 2 =
        ((Aop.spectralPVM.diag (x : H)) Set.univ).toReal * c
      rw [Aop.spectralPVM.diag_univ_toReal, mul_comm]
    _ ≤ ∫ s, s ∂μ := integral_mono_ae (integrable_const _) hint hae
    _ = (⟪(x : H), A.toLinearMap x⟫_ℂ).re := hval
    _ = (⟪A.toLinearMap x, (x : H)⟫_ℂ).re := by
      rw [← inner_conj_symm, Complex.conj_re]

/-- Genuine spectral containment in `(-∞, c]` implies the matching upper
quadratic-form bound. -/
theorem semiboundedAbove_of_spectrum_subset_Iic
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {c : ℝ}
    (hσ : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A.toLinearPMap ⊆
        Set.Iic c) :
    SemiboundedAbove A c := by
  intro x
  let Aop := closedOperatorToSpectra A hA
  let μ : Measure ℝ := Aop.bornMeasure (x : H)
  letI : IsFiniteMeasure μ := by
    change IsFiniteMeasure (Aop.spectralPVM.diag (x : H))
    exact Aop.spectralPVM.diag_finite (x : H)
  have hint : Integrable (fun s : ℝ => s) μ := by
    change Integrable (fun s : ℝ => s)
      ((Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM hA).diag (x : H))
    exact spectralPVM_integrable_id hA (x : H) x.property
  have hval : ∫ s, s ∂μ = (⟪(x : H), A.toLinearMap x⟫_ℂ).re := by
    simpa [μ, Aop,
      Spectra.Operator.SelfAdjointOperator.bornMeasure,
      Spectra.QuantumMechanics.BornRule.Moments.bornExpectation] using
      bornExpectation_eq_inner Aop x.property
  have hsupp : μ.support ⊆ Set.Iic c := by
    intro s hs
    exact hσ (bornMeasure_support_subset_spectrum Aop (x : H) hs)
  have hae : ∀ᵐ s ∂μ, s ≤ c := by
    filter_upwards [Measure.support_mem_ae (μ := μ)] with s hs using hsupp hs
  calc
    (⟪A.toLinearMap x, (x : H)⟫_ℂ).re =
        (⟪(x : H), A.toLinearMap x⟫_ℂ).re := by
      rw [← inner_conj_symm, Complex.conj_re]
    _ = ∫ s, s ∂μ := hval.symm
    _ ≤ ∫ _s, c ∂μ := integral_mono_ae hint (integrable_const _) hae
    _ = c * ‖(x : H)‖ ^ 2 := by
      rw [integral_const, smul_eq_mul, Measure.real_def]
      change ((Aop.spectralPVM.diag (x : H)) Set.univ).toReal * c =
        c * ‖(x : H)‖ ^ 2
      rw [Aop.spectralPVM.diag_univ_toReal, mul_comm]

end SpectraBridge
end Experimental
end DavisKahan
end TauCeti