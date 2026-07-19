/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Unbounded
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.UnboundedIntervalExterior
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.OrderedHalfLine
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineCutoffInterface
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineOrderedEngine

/-!
# Genuine-spectrum all-gap unbounded Sylvester theorem

This module states the source-facing all-gap predicate entirely through the
genuine Spectra spectrum.  It covers the interval/exterior configuration and
both ordered half-line configurations.  The capstone converts the ordered
spectral containments to form bounds and then calls the existing finite-Ky-Fan
engine.

The file is intentionally independent of the continuation and Section 8 graph
selection developments.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Genuine Spectra interval/exterior separation for a Sylvester pair. -/
def GenuineSylvesterIntervalExteriorGap
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E))
    (B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F))
    (β α δ : ℝ) : Prop :=
  (Spectra.Resolvent.spectrum A.toLinearPMap ⊆ Set.Icc β α ∧
    ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      lam ∉ Spectra.Resolvent.spectrum B.toLinearPMap) ∨
  (Spectra.Resolvent.spectrum B.toLinearPMap ⊆ Set.Icc β α ∧
    ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      lam ∉ Spectra.Resolvent.spectrum A.toLinearPMap)

/-- All three source gap configurations, stated with genuine Spectra spectra. -/
inductive GenuineUnboundedSylvesterGap
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E))
    (B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F))
    (δ : ℝ) : Prop where
  | intervalExterior
      {β α : ℝ}
      (hβα : β ≤ α)
      (hgap : GenuineSylvesterIntervalExteriorGap A B β α δ)
  | leftAboveRightBelow
      (c : ℝ)
      (hA : Spectra.Resolvent.spectrum A.toLinearPMap ⊆ Set.Ici (c + δ))
      (hB : Spectra.Resolvent.spectrum B.toLinearPMap ⊆ Set.Iic c)
  | leftBelowRightAbove
      (c : ℝ)
      (hA : Spectra.Resolvent.spectrum A.toLinearPMap ⊆ Set.Iic c)
      (hB : Spectra.Resolvent.spectrum B.toLinearPMap ⊆ Set.Ici (c + δ))

/-- Source-facing Theorem 5.2 wrapper with genuine spectra in every branch. -/
theorem davisKahan1970_sylvester_of_genuineSpectrumGap
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : GenuineUnboundedSylvesterGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge X ≤
        N.toRectangularSymmetricIdealFamily.gauge C := by
  cases hgap with
  | intervalExterior hβα hgap =>
      rcases hgap with hgap | hgap
      · exact SpectraBridge.unbounded_sylvester_mem_and_gauge_le_of_spectra_intervalLeft_exteriorRight
          N.toRectangularSymmetricIdealFamily hA hB hβα hδ
            hgap.1 hgap.2 hEq hC
      · exact SpectraBridge.unbounded_sylvester_mem_and_gauge_le_of_spectra_exteriorLeft_intervalRight
          N.toRectangularSymmetricIdealFamily hA hB hβα hδ
            hgap.2 hgap.1 hEq hC
  | leftAboveRightBelow c hAspec hBspec =>
      exact GenuineOrderedSylvesterEngine.lowerUpper
        canonicalGenuineOrderedSylvesterEngine N hA hB hδ
          (SpectraBridge.semiboundedBelow_of_spectrum_subset_Ici A hA hAspec)
          (SpectraBridge.semiboundedAbove_of_spectrum_subset_Iic B hB hBspec)
          hEq hC
  | leftBelowRightAbove c hAspec hBspec =>
      exact GenuineOrderedSylvesterEngine.upperLower
        canonicalGenuineOrderedSylvesterEngine N hA hB hδ
          (SpectraBridge.semiboundedAbove_of_spectrum_subset_Iic A hA hAspec)
          (SpectraBridge.semiboundedBelow_of_spectrum_subset_Ici B hB hBspec)
          hEq hC

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
