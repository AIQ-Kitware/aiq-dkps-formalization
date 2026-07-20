/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.Released under Apache 2.0 license as described in the file LICENSE.Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.PairwiseSpectrumGap
import DavisKahan.SpectralTheory.ClosedOperator.Complexification
import DavisKahan.Sylvester.PairwiseHomogeneousUniqueness
import DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtDefectFirst
import Spectra.Spaces.Tensor.HilbertSchmidtSpectralGap
import Spectra.QuantumMechanics.BornRule.Observable

/-!
# Pairwise-gap square-norm Sylvester theorem

This file discharges the two hypotheses left by the defect-first reduction.Positive pairwise separation of the original self-adjoint spectra:

* gives bounded homogeneous uniqueness through rectangular spectral
  intertwining; and
* gives a global spectral gap for the left-minus-right Hilbert--Schmidt tensor
  flow through the pure-tensor product-measure formula.The resulting theorem has the exact hypothesis and constant of the
square-norm Sylvester estimate used in Davis--Kahan Theorem 6.2.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open ForMathlib.DavisKahanExt
open Spectra.Operator
open Spectra.YosidaHille
-- The support estimate sits under the observable namespace, and the
-- complexification of a bounded operator under the foundation namespace.
open Spectra.QuantumMechanics.BornRule.PVM
open Spectra.QuantumMechanics.BornRule.Observable
open Foundation

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem pairwiseScalarSupportGap_of_spectra
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {δ : ℝ} (hgap : GenuinePairwiseSpectrumGap A B δ) :
    Spectra.HilbertSchmidtTensor.PairwiseScalarSupportGap
      (genToGroup hA) (genToGroup hB) δ := by
  intro u v lam hlam alpha halpha
  let AO : SelfAdjointOperator E := ⟨A.toLinearPMap, hA⟩
  let BO : SelfAdjointOperator F := ⟨B.toLinearPMap, hB⟩
  have hlamSpec : lam ∈ Spectra.Resolvent.spectrum A.toLinearPMap := by
    have hsupp := bornMeasure_support_subset_spectrum AO u
    exact hsupp (by
      simpa [AO, bornMeasure,
        SelfAdjointOperator.spectralPVM] using hlam)
  have halphaSpec : alpha ∈ Spectra.Resolvent.spectrum B.toLinearPMap := by
    have hsupp := bornMeasure_support_subset_spectrum BO v
    exact hsupp (by
      simpa [BO, bornMeasure,
        SelfAdjointOperator.spectralPVM] using halpha)
  exact hgap lam hlamSpec alpha halphaSpec

/-- The defect tensor has the vector spectral gap dictated by the pairwise
separation of the original spectra.  In fact the tensor flow has this gap at
every vector. -/
theorem paperHilbertSchmidtTensor_hasVectorSpectralGap
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : GenuinePairwiseSpectrumGap A B δ)
    (hC : IsPaperHilbertSchmidt C) :
    Spectra.QuantumMechanics.SpectralTheory.HasVectorSpectralGap
      (Spectra.HilbertSchmidtTensor.sylvesterGroup
        (genToGroup hA) (genToGroup hB))
      (paperHilbertSchmidtTensor C hC) δ := by
  exact Spectra.HilbertSchmidtTensor.hasVectorSpectralGap
    (genToGroup hA) (genToGroup hB) hδ.le
    (pairwiseScalarSupportGap_of_spectra hA hB hgap)
    (paperHilbertSchmidtTensor C hC)

/-- **Davis--Kahan square-norm Sylvester estimate at arbitrary pairwise
spectral separation.**  This is the direct, non-circular completion of the
analytic engine required by Theorem 6.2. -/
theorem paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    {X C : F →L[ℂ] E}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : GenuinePairwiseSpectrumGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : IsPaperHilbertSchmidt C) :
    IsPaperHilbertSchmidt X ∧
      δ * paperHilbertSchmidtNorm X ≤ paperHilbertSchmidtNorm C := by
  apply paperHilbertSchmidt_sylvester_defectFirst
    hA hB hδ hEq
  · intro Y hY
    exact closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
      hA hB hδ hgap hY
  -- Supplying the gap instantiates the tensor's own membership argument, so
  -- there is no further obligation.
  · exact paperHilbertSchmidtTensor_hasVectorSpectralGap
      hA hB hδ hgap hC


/-- Real closed-operator form of the direct pairwise-gap theorem, obtained by
exact complexification. -/
theorem paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct
    {ER FR : Type v}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]
    {A : ClosedOperator (𝕜 := ℝ) (E := ER)}
    {B : ClosedOperator (𝕜 := ℝ) (E := FR)}
    {X C : FR →L[ℝ] ER}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ lam ∈ A.realSpectrum, ∀ α ∈ B.realSpectrum,
      δ ≤ |lam - α|)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : IsPaperHilbertSchmidt C) :
    IsPaperHilbertSchmidt X ∧
      δ * paperHilbertSchmidtNorm X ≤ paperHilbertSchmidtNorm C := by
  have hgapC : GenuinePairwiseSpectrumGap
      (ClosedOperatorComplexification.complexify A)
      (ClosedOperatorComplexification.complexify B) δ := by
    intro lam hlam α hα
    apply hgap lam _ α _
    · rwa [ClosedOperatorComplexification.realSpectrum_complexify A]
    · rwa [ClosedOperatorComplexification.realSpectrum_complexify B]
  have hCcomplex : IsPaperHilbertSchmidt
      (RealComplexification.complexify C) :=
    (isPaperHilbertSchmidt_complexify_iff C).2 hC
  have hmain := paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
    (ClosedOperatorComplexification.isSelfAdjoint_complexify hA)
    (ClosedOperatorComplexification.isSelfAdjoint_complexify hB)
    hδ hgapC
    (ClosedOperatorComplexification.closedSylvesterEquation_complexify hEq)
    hCcomplex
  constructor
  · exact (isPaperHilbertSchmidt_complexify_iff X).1 hmain.1
  · simpa [paperHilbertSchmidtNorm_complexify] using hmain.2

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
