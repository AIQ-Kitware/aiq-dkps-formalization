/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Spectra.SpectralTheory.Calculus.MixedProduct

/-!
# Inversion of the identity multiplier on a vector with a spectral gap

Let `U` be a one-parameter unitary group and let `xi` have scalar spectral
measure supported in `{s | delta <= |s|}`.  The bounded symbol

`g_delta(s) = if delta <= |s| then 1/s else 0`

produces a vector `eta = Phi(g_delta) xi` in the natural domain of the identity
multiplier.  The unbounded identity calculus sends `eta` back to `xi`, and
`‖eta‖ <= delta⁻¹ ‖xi‖`.

This is the defect-first inverse used by the rectangular Hilbert--Schmidt
Sylvester theorem.  It is deliberately vector-local: no global spectral-gap
assumption on the generator is needed.
-/

open InnerProductSpace Complex MeasureTheory
open scoped InnerProductSpace

namespace Spectra.QuantumMechanics.SpectralTheory

noncomputable section

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The reciprocal symbol, cut off inside the forbidden gap. -/
def spectralGapInverseSymbol (δ : ℝ) (s : ℝ) : ℂ :=
  if δ ≤ |s| then ((s : ℂ)⁻¹) else 0

/-- The scalar spectral measure of `xi` stays outside the open gap. -/
def HasVectorSpectralGap (U : OneParameterUnitaryGroup (H := H))
    (ξ : H) (δ : ℝ) : Prop :=
  ∀ᵐ s ∂borelMeasure U ξ, δ ≤ |s|

/-- The cut-off reciprocal symbol is measurable. -/
theorem measurable_spectralGapInverseSymbol (δ : ℝ) :
    Measurable (spectralGapInverseSymbol δ) := by
  unfold spectralGapInverseSymbol
  exact Measurable.ite
    (measurableSet_le measurable_const measurable_abs)
    Complex.measurable_ofReal.inv measurable_const

/-- The cut-off reciprocal is bounded by `δ⁻¹` when `δ > 0`. -/
theorem norm_spectralGapInverseSymbol_le {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    ‖spectralGapInverseSymbol δ s‖ ≤ δ⁻¹ := by
  unfold spectralGapInverseSymbol
  split_ifs with hs
  · rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    exact inv_le_inv₀ hδ hs
  · simp [inv_nonneg.mpr hδ.le]

/-- The product of the identity and cut-off reciprocal is bounded by one. -/
theorem norm_mul_spectralGapInverseSymbol_le_one {δ : ℝ}
    (hδ : 0 < δ) (s : ℝ) :
    ‖(s : ℂ) * spectralGapInverseSymbol δ s‖ ≤ 1 := by
  unfold spectralGapInverseSymbol
  split_ifs with hs
  · have hs0 : (s : ℂ) ≠ 0 := by
      exact_mod_cast (abs_pos.mp (hδ.trans_le hs)).ne'
    rw [mul_inv_cancel₀ hs0, norm_one]
  · simp

/-- The bounded inverse-calculus vector. -/
noncomputable def spectralGapSolution
    (U : OneParameterUnitaryGroup (H := H)) (δ : ℝ) (hδ : 0 < δ)
    (ξ : H) : H :=
  spectralCalculus U (spectralGapInverseSymbol δ)
    (measurable_spectralGapInverseSymbol δ)
    ⟨δ⁻¹, fun s => norm_spectralGapInverseSymbol_le hδ s⟩ ξ

/-- Norm estimate for the defect-first inverse vector. -/
theorem norm_spectralGapSolution_le
    (U : OneParameterUnitaryGroup (H := H)) {δ : ℝ} (hδ : 0 < δ)
    (ξ : H) :
    ‖spectralGapSolution U δ hδ ξ‖ ≤ δ⁻¹ * ‖ξ‖ := by
  unfold spectralGapSolution
  exact (spectralCalculus U (spectralGapInverseSymbol δ)
    (measurable_spectralGapInverseSymbol δ)
    ⟨δ⁻¹, fun s => norm_spectralGapInverseSymbol_le hδ s⟩).le_opNorm_of_bound
      (norm_spectralCalculus_le U _ _ _
        (fun s => norm_spectralGapInverseSymbol_le hδ s)) ξ

/-- The inverse-calculus vector belongs directly to the generator domain.
This avoids routing through a separate identification of the unbounded identity
calculus with the generator. -/
theorem spectralGapSolution_mem_generatorDomain
    (U : OneParameterUnitaryGroup (H := H)) {δ : ℝ} (hδ : 0 < δ)
    (ξ : H) :
    spectralGapSolution U δ hδ ξ ∈
      OneParameterUnitaryGroup.generatorDomain U := by
  unfold spectralGapSolution
  exact spectralCalculus_mem_generatorDomain U
    (spectralGapInverseSymbol δ)
    (measurable_spectralGapInverseSymbol δ)
    ⟨δ⁻¹, fun s => norm_spectralGapInverseSymbol_le hδ s⟩
    (Complex.measurable_ofReal.mul
      (measurable_spectralGapInverseSymbol δ))
    ⟨1, fun s => norm_mul_spectralGapInverseSymbol_le_one hδ s⟩ ξ

/-- On a vector spectrally supported outside the gap, the generator sends the
inverse-calculus vector back to the original vector. -/
theorem generator_spectralGapSolution
    (U : OneParameterUnitaryGroup (H := H)) {δ : ℝ} (hδ : 0 < δ)
    (ξ : H) (hgap : HasVectorSpectralGap U ξ δ) :
    OneParameterUnitaryGroup.generator U
        ⟨spectralGapSolution U δ hδ ξ,
          spectralGapSolution_mem_generatorDomain U hδ ξ⟩ = ξ := by
  unfold spectralGapSolution
  rw [generator_spectralCalculus U
    (spectralGapInverseSymbol δ)
    (measurable_spectralGapInverseSymbol δ)
    ⟨δ⁻¹, fun s => norm_spectralGapInverseSymbol_le hδ s⟩
    (Complex.measurable_ofReal.mul
      (measurable_spectralGapInverseSymbol δ))
    ⟨1, fun s => norm_mul_spectralGapInverseSymbol_le_one hδ s⟩ ξ]
  have hae : (fun s : ℝ => (s : ℂ) * spectralGapInverseSymbol δ s)
      =ᵐ[borelMeasure U ξ] (fun _ => (1 : ℂ)) := by
    filter_upwards [hgap] with s hs
    unfold spectralGapInverseSymbol
    rw [if_pos hs]
    have hs0 : (s : ℂ) ≠ 0 := by
      exact_mod_cast (abs_pos.mp (hδ.trans_le hs)).ne'
    exact mul_inv_cancel₀ hs0
  rw [spectralCalculus_congr_ae U
    (fun s : ℝ => (s : ℂ) * spectralGapInverseSymbol δ s)
    (fun _ => (1 : ℂ))
    (Complex.measurable_ofReal.mul
      (measurable_spectralGapInverseSymbol δ))
    ⟨1, fun s => norm_mul_spectralGapInverseSymbol_le_one hδ s⟩
    measurable_const ⟨1, fun _ => norm_one.le⟩ ξ hae,
    spectralCalculus_one]
  rfl

/-- The inverse vector lies in the natural domain of the identity multiplier. -/
theorem spectralGapSolution_mem_pmapDomain
    (U : OneParameterUnitaryGroup (H := H)) {δ : ℝ} (hδ : 0 < δ)
    (ξ : H) :
    spectralGapSolution U δ hδ ξ ∈
      ProjValMeasure.pmapDomain U.toPVM (fun s : ℝ => (s : ℂ)) := by
  unfold spectralGapSolution
  exact mem_pmapDomain_spectralCalculus U
    (fun s : ℝ => (s : ℂ)) (spectralGapInverseSymbol δ)
    Complex.measurable_ofReal (measurable_spectralGapInverseSymbol δ)
    ⟨δ⁻¹, fun s => norm_spectralGapInverseSymbol_le hδ s⟩
    ⟨1, fun s => norm_mul_spectralGapInverseSymbol_le_one hδ s⟩ ξ

/-- On a vector supported outside the gap, multiplying the inverse vector by
the identity symbol recovers the original vector. -/
theorem pmapOfPVM_id_spectralGapSolution
    (U : OneParameterUnitaryGroup (H := H)) {δ : ℝ} (hδ : 0 < δ)
    (ξ : H) (hgap : HasVectorSpectralGap U ξ δ) :
    pmapOfPVM U (fun s : ℝ => (s : ℂ)) Complex.measurable_ofReal
      ⟨spectralGapSolution U δ hδ ξ,
        spectralGapSolution_mem_pmapDomain U hδ ξ⟩ = ξ := by
  rw [pmapOfPVM_spectralCalculus_of_mul_bounded U
    (fun s : ℝ => (s : ℂ)) (spectralGapInverseSymbol δ)
    Complex.measurable_ofReal (measurable_spectralGapInverseSymbol δ)
    ⟨δ⁻¹, fun s => norm_spectralGapInverseSymbol_le hδ s⟩
    (Complex.measurable_ofReal.mul (measurable_spectralGapInverseSymbol δ))
    ⟨1, fun s => norm_mul_spectralGapInverseSymbol_le_one hδ s⟩ ξ
    (spectralGapSolution_mem_pmapDomain U hδ ξ)]
  have hae : (fun s : ℝ => (s : ℂ) * spectralGapInverseSymbol δ s)
      =ᵐ[borelMeasure U ξ] (fun _ => (1 : ℂ)) := by
    filter_upwards [hgap] with s hs
    unfold spectralGapInverseSymbol
    rw [if_pos hs]
    have hs0 : (s : ℂ) ≠ 0 := by
      exact_mod_cast (abs_pos.mp (hδ.trans_le hs)).ne'
    exact mul_inv_cancel₀ hs0
  rw [spectralCalculus_congr_ae U
    (fun s : ℝ => (s : ℂ) * spectralGapInverseSymbol δ s)
    (fun _ => (1 : ℂ))
    (Complex.measurable_ofReal.mul (measurable_spectralGapInverseSymbol δ))
    measurable_const
    ⟨1, fun s => norm_mul_spectralGapInverseSymbol_le_one hδ s⟩
    ⟨1, fun _ => norm_one.le⟩ ξ hae,
    spectralCalculus_one]
  rfl

end
end Spectra.QuantumMechanics.SpectralTheory
