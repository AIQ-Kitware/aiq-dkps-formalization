/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.Unbounded.AllGap
import DavisKahan.Interop.Spectra.RealSpectrumBridge

/-!
# Completion of the manuscript-shaped complex gap API

The original manuscript API uses `ClosedOperator.realSpectrum` and packages
ordered form bounds together with interval/exterior spectral separation.  The
genuine complex implementation uses Spectra for the spectral branch and the
direct cutoff engine for the ordered branches.  This file connects those two
surfaces without importing any theorem from the obsolete cutoff facade.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A legacy interval/exterior hypothesis becomes the genuine Spectra
interval/exterior hypothesis after identifying the two real spectra. -/
theorem genuineSylvesterIntervalExteriorGap_of_legacy
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    {β α δ : ℝ}
    (hgap : UnboundedIntervalExteriorGap A B β α δ) :
    GenuineSylvesterIntervalExteriorGap A B β α δ := by
  rcases hgap with hgap | hgap
  · left
    constructor
    · simpa only [SpectraBridge.realSpectrum_eq_spectraSpectrum] using hgap.1
    · intro lam hlam hlamSpec
      have hlegacy : lam ∈ B.realSpectrum := by
        simpa only [SpectraBridge.realSpectrum_eq_spectraSpectrum] using hlamSpec
      rcases hgap.2 hlegacy with hleft | hright
      · exact (not_lt_of_ge hleft) hlam.1
      · exact (not_lt_of_ge hright) hlam.2
  · right
    constructor
    · simpa only [SpectraBridge.realSpectrum_eq_spectraSpectrum] using hgap.1
    · intro lam hlam hlamSpec
      have hlegacy : lam ∈ A.realSpectrum := by
        simpa only [SpectraBridge.realSpectrum_eq_spectraSpectrum] using hlamSpec
      rcases hgap.2 hlegacy with hleft | hright
      · exact (not_lt_of_ge hleft) hlam.1
      · exact (not_lt_of_ge hright) hlam.2

/-- The interval/exterior constructor of the manuscript gap embeds into the
genuine all-gap predicate.  Ordered constructors are intentionally handled by
their form bounds rather than translated into spectral containments. -/
theorem GenuineUnboundedSylvesterGap.intervalExterior_of_legacy
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    {β α δ : ℝ}
    (hβα : β ≤ α)
    (hgap : UnboundedIntervalExteriorGap A B β α δ) :
    GenuineUnboundedSylvesterGap A B δ :=
  GenuineUnboundedSylvesterGap.intervalExterior hβα
    (genuineSylvesterIntervalExteriorGap_of_legacy hgap)

/-- Admission-free complex specialization of the manuscript Section 5
Sylvester theorem.  The spectral constructor is routed through the genuine
Spectra theorem, while the two ordered constructors retain their original
form-bound hypotheses and call the direct engine verbatim. -/
theorem davisKahan1970_sylvester_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gauge X ≤
        N.gauge C := by
  cases hgap with
  | intervalExterior hβα hgap =>
      exact davisKahan1970_sylvester_of_genuineSpectrumGap
        N hA hB hδ
          (GenuineUnboundedSylvesterGap.intervalExterior_of_legacy hβα hgap)
          hEq hC
  | leftAboveRightBelow c hAc hBc =>
      exact directGenuineOrderedSylvesterEngine_lowerUpper
        N hA hB hδ hAc hBc hEq hC
  | leftBelowRightAbove c hAc hBc =>
      exact directGenuineOrderedSylvesterEngine_upperLower
        N hA hB hδ hAc hBc hEq hC

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti