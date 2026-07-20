/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidt
import DavisKahan.Sylvester.PairwiseSpectrumGap
import DavisKahan.SpectralTheory.ClosedOperator.Complexification
import Spectra.QuantumMechanics.BornRule.Joint.Forward
import Spectra.Spaces.Tensor.Map

/-!
# The square-norm Sylvester theorem at arbitrary spectral distance

This is the analytic engine used by Davis--Kahan Theorem 6.2.  Unlike the
arbitrary-norm theorem for disconnected spectra, the Hilbert--Schmidt norm has
constant one under the sole pairwise-distance hypothesis.

The hard construction is isolated in
`exists_paperHilbertSchmidtSylvesterSpectralModel`.  It is the rectangular
Hilbert--Schmidt Plancherel theorem for the commuting left and right spectral
measures.  Once that model exists, the coercive estimate is a one-line
pointwise multiplier bound under the product spectral measure.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace ENNReal

noncomputable section

universe v

open ForMathlib.DavisKahanExt

/-- Spectral-measure model of one rectangular Sylvester equation.

The measure is the scalar measure of the commuting left and right PVMs on the
Hilbert--Schmidt completion.  Its total mass is the solution square energy and
the squared multiplier integral is the defect square energy. -/
structure PaperHilbertSchmidtSylvesterSpectralModel
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : ClosedOperator (𝕜 := ℂ) (E := E))
    (B : ClosedOperator (𝕜 := ℂ) (E := F))
    (X C : F →L[ℂ] E) where
  measure : Measure (ℝ × ℝ)
  solution_energy :
    paperHilbertSchmidtEnergy X = ∫⁻ _p, (1 : ENNReal) ∂measure
  defect_energy :
    paperHilbertSchmidtEnergy C =
      ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂measure
  supported_on_spectra :
    ∀ᵐ p ∂measure,
      p.1 ∈ Spectra.Resolvent.spectrum A.toLinearPMap ∧
      p.2 ∈ Spectra.Resolvent.spectrum B.toLinearPMap

/-- **Hilbert--Schmidt double spectral representation.**

On finite-rank operators, send `rankOne u v` to the pure tensor
`u tensor conjugate(v)`.  Parseval extends this to an isometry from the
Hilbert--Schmidt completion to the Hilbert tensor product.  The spectral PVM of
`A` acts on the first tensor factor and that of `B` on the second.  These PVMs
strongly commute, so their canonical joint PVM supplies the measure below.
The closed Sylvester equation identifies the joint multiplier with
`(lambda,alpha) |-> lambda-alpha` on its natural domain. -/
theorem exists_paperHilbertSchmidtSylvesterSpectralModel
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    {X C : F →L[ℂ] E}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    (hEq : HasClosedSylvesterEquation A B X C) :
    Nonempty (PaperHilbertSchmidtSylvesterSpectralModel A B X C) := by
  -- The implementation is organized around the completed rank-one tensor
  -- isometry.  Every equality below is first proved on finite sums of pure
  -- tensors and then extended by density and closedness of the two spectral
  -- multiplication operators.
  let hsEquiv :=
    Spectra.HilbertSchmidtTensor.rectangularEquiv
      (𝕜 := ℂ) (E := E) (F := F)
  let leftObservable :=
    Spectra.HilbertSchmidtTensor.leftSelfAdjointOperator hsEquiv A hA
  let rightObservable :=
    Spectra.HilbertSchmidtTensor.rightSelfAdjointOperator hsEquiv B hB
  have hcomm : Spectra.Operator.StronglyCommute leftObservable rightObservable :=
    Spectra.HilbertSchmidtTensor.left_right_stronglyCommute hsEquiv A B hA hB
  let joint := Spectra.Joint.jointPOVM leftObservable rightObservable hcomm
  let ξ := Spectra.HilbertSchmidtTensor.ofBoundedOperator hsEquiv X
  let μ : Measure (ℝ × ℝ) := Spectra.Joint.jointBornMeasure joint ξ
  have hXenergy :
      paperHilbertSchmidtEnergy X = ∫⁻ _p, (1 : ENNReal) ∂μ := by
    simpa [μ, ξ] using
      Spectra.HilbertSchmidtTensor.lintegral_one_jointBornMeasure
        hsEquiv joint X
  have hCenergy :
      paperHilbertSchmidtEnergy C =
        ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂μ := by
    have hmult :=
      Spectra.HilbertSchmidtTensor.closedSylvester_jointMultiplier
        hsEquiv A B X C hA hB hEq
    simpa [μ, ξ, leftObservable, rightObservable] using hmult
  have hsupp :
      ∀ᵐ p ∂μ,
        p.1 ∈ Spectra.Resolvent.spectrum A.toLinearPMap ∧
        p.2 ∈ Spectra.Resolvent.spectrum B.toLinearPMap := by
    exact Spectra.HilbertSchmidtTensor.jointBornMeasure_supported_on_spectra
      hsEquiv A B hA hB joint ξ
  exact ⟨⟨μ, hXenergy, hCenergy, hsupp⟩⟩

/-- Pointwise spectral distance gives the squared Hilbert--Schmidt energy
inequality. -/
theorem paperHilbertSchmidtEnergy_sylvester_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    {X C : F →L[ℂ] E}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : GenuinePairwiseSpectrumGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C) :
    ENNReal.ofReal (δ ^ 2) * paperHilbertSchmidtEnergy X ≤
      paperHilbertSchmidtEnergy C := by
  let M := Classical.choice
    (exists_paperHilbertSchmidtSylvesterSpectralModel hA hB hEq)
  rw [M.solution_energy, M.defect_energy, ENNReal.mul_lintegral]
  apply lintegral_mono_ae
  filter_upwards [M.supported_on_spectra] with p hp
  have hdist := hgap p.1 hp.1 p.2 hp.2
  have hsquare : δ ^ 2 ≤ (p.1 - p.2) ^ 2 := by
    exact pow_le_pow_left₀ hδ.le hdist 2
  simpa [ENNReal.ofReal_mul (sq_nonneg δ)] using
    ENNReal.ofReal_le_ofReal hsquare

/-- **Davis--Kahan inequality (5.1), closed-operator square-norm form.** -/
theorem paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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
  have henergy :=
    paperHilbertSchmidtEnergy_sylvester_le_of_pairwiseSpectrumGap
      hA hB hδ hgap hEq
  have hXfinite : paperHilbertSchmidtEnergy X ≠ ⊤ := by
    by_contra htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero.mpr (sq_pos_of_pos hδ).ne')] at henergy
    exact hC (top_le_iff.mp henergy)
  refine ⟨hXfinite, ?_⟩
  have hreal := ENNReal.toReal_mono hC hXfinite henergy
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg δ)] at hreal
  have hsqrt := Real.sqrt_le_sqrt hreal
  simpa [paperHilbertSchmidtNorm, Real.sqrt_mul (sq_nonneg δ),
    Real.sqrt_sq hδ.le] using hsqrt

/-- Real closed-operator form, obtained by exact complexification. -/
theorem paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {A : ClosedOperator (𝕜 := ℝ) (E := E)}
    {B : ClosedOperator (𝕜 := ℝ) (E := F)}
    {X C : F →L[ℝ] E}
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
    · rwa [ClosedOperatorComplexification.closed_realSpectrum_complexify A]
    · rwa [ClosedOperatorComplexification.closed_realSpectrum_complexify B]
  have hCcomplex : IsPaperHilbertSchmidt
      (RealComplexification.complexify C) :=
    (isPaperHilbertSchmidt_complexify_iff C).2 hC
  have hmain := paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap
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
