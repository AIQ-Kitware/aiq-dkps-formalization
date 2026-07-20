/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ClosedOperator.Basic
import Spectra.Resolvent.Spectrum

/-!
# Pairwise spectral separation for two closed self-adjoint blocks

This is the exact weak spectral hypothesis used by the square-norm Sylvester
estimate and Davis--Kahan Theorem 6.2.  It is intentionally independent of the
three stronger interval/exterior and ordered gap configurations.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

noncomputable section

universe v

open ForMathlib.DavisKahanExt

/-- Every point of the two real spectra is separated by at least `delta`. -/
def GenuinePairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : ClosedOperator (𝕜 := ℂ) (E := E))
    (B : ClosedOperator (𝕜 := ℂ) (E := F))
    (δ : ℝ) : Prop :=
  ∀ lam ∈ Spectra.Resolvent.spectrum A.toLinearPMap,
    ∀ α ∈ Spectra.Resolvent.spectrum B.toLinearPMap,
      δ ≤ |lam - α|

namespace GenuinePairwiseSpectrumGap

/-- Pairwise spectral distance is symmetric. -/
theorem symm
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)} {δ : ℝ}
    (h : GenuinePairwiseSpectrumGap A B δ) :
    GenuinePairwiseSpectrumGap B A δ := by
  intro α hα lam hlam
  simpa [abs_sub_comm] using h lam hlam α hα

/-- Decreasing the requested distance preserves pairwise separation. -/
theorem mono
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)} {δ ε : ℝ}
    (h : GenuinePairwiseSpectrumGap A B δ) (hεδ : ε ≤ δ) :
    GenuinePairwiseSpectrumGap A B ε := by
  intro lam hlam α hα
  exact hεδ.trans (h lam hlam α hα)

/-- Positive pairwise separation implies disjoint spectra. -/
theorem disjoint
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)} {δ : ℝ}
    (h : GenuinePairwiseSpectrumGap A B δ) (hδ : 0 < δ) :
    Disjoint (Spectra.Resolvent.spectrum A.toLinearPMap)
      (Spectra.Resolvent.spectrum B.toLinearPMap) := by
  refine Set.disjoint_left.mpr ?_
  intro lam hlamA hlamB
  have hsep : δ ≤ |lam - lam| := h lam hlamA lam hlamB
  exact (not_le_of_gt hδ) (by simpa using hsep)

end GenuinePairwiseSpectrumGap

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
