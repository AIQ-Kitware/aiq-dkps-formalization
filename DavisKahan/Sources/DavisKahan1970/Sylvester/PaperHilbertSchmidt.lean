/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise

/-!
# Source-facing square-norm Sylvester theorem

This module restores the public declarations originally planned for the
Davis--Kahan square-norm Sylvester estimate.  The completed proof route is the
defect-first Hilbert-tensor argument in `HilbertSchmidtDefectFirst` and
`HilbertSchmidtPairwise`; it does not require a separate joint-PVM Plancherel
construction for rectangular operators.

The extended-energy statement is recovered from the norm theorem.  When the
defect energy is infinite the inequality is immediate.  When it is finite,
the direct pairwise-gap theorem proves Hilbert--Schmidt membership of the
solution and the sharp norm estimate; squaring and converting between finite
`ENNReal` energies gives the claimed inequality.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace ENNReal

open TauCeti.DavisKahanExt

noncomputable section

universe v

/-- Pairwise spectral distance gives the squared Hilbert--Schmidt energy
inequality, including the case of infinite defect energy. -/
theorem paperHilbertSchmidtEnergy_sylvester_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    {X C : F →L[ℂ] E}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C) :
    ENNReal.ofReal (δ ^ 2) * paperHilbertSchmidtEnergy X ≤
      paperHilbertSchmidtEnergy C := by
  by_cases hC : IsPaperHilbertSchmidt C
  · have hmain :=
      paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
        hA hB hδ hgap hEq hC
    have hsq :
        (δ * paperHilbertSchmidtNorm X) ^ 2 ≤
          paperHilbertSchmidtNorm C ^ 2 :=
      (sq_le_sq₀
        (mul_nonneg hδ.le (paperHilbertSchmidtNorm_nonneg X))
        (paperHilbertSchmidtNorm_nonneg C)).2 hmain.2
    have hreal :
        (ENNReal.ofReal (δ ^ 2) * paperHilbertSchmidtEnergy X).toReal ≤
          (paperHilbertSchmidtEnergy C).toReal := by
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (sq_nonneg δ),
        ← sq_paperHilbertSchmidtNorm hmain.1,
        ← sq_paperHilbertSchmidtNorm hC]
      simpa [mul_pow] using hsq
    exact (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmain.1) hC).mp hreal
  · have htop : paperHilbertSchmidtEnergy C = ⊤ := by
      by_contra hne
      exact hC hne
    rw [htop]
    exact le_top

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
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : IsPaperHilbertSchmidt C) :
    IsPaperHilbertSchmidt X ∧
      δ * paperHilbertSchmidtNorm X ≤ paperHilbertSchmidtNorm C :=
  paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
    hA hB hδ hgap hEq hC

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
      δ * paperHilbertSchmidtNorm X ≤ paperHilbertSchmidtNorm C :=
  paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct
    hA hB hδ hgap hEq hC

end

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti