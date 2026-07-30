/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.Unbounded.AllGap
import DavisKahan.SpectralTheory.ClosedOperator.RealSpectrum

/-!
# Form-bounded gap hypotheses discharge the spectral ones

`Sylvester/Gap.lean` states its gap over `ClosedOperator.realSpectrum` and
packages ordered form bounds together with interval/exterior spectral
separation.  `UnboundedSylvesterGap` instead states all three configurations
spectrally, using Spectra for the spectral branch and the direct cutoff engine
for the ordered branches.  This file connects the two surfaces without importing
any theorem from the obsolete cutoff facade.

**The connection runs one way.**  Both theorems here take a form-bounded
hypothesis and produce a spectral one; neither converse is proved.  That is why
`Sylvester/Gap.lean` carries the qualified names: it is the stronger hypothesis,
so a theorem stated over it is the weaker theorem, and the unqualified name
belongs to the spectral surface.
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

omit [CompleteSpace E] [CompleteSpace F] in
/-- A `realSpectrum` interval/exterior hypothesis becomes the spectral
interval/exterior hypothesis after identifying the two spectra. -/
theorem sylvesterIntervalExteriorGap_of_realSpectrum
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    {β α δ : ℝ}
    (hgap : RealSpectrumIntervalExteriorGap A B β α δ) :
    SylvesterIntervalExteriorGap A B β α δ := by
  rcases hgap with hgap | hgap
  · left
    constructor
    · simpa only [realSpectrum_eq_spectraSpectrum] using hgap.1
    · intro lam hlam hlamSpec
      have hreal : lam ∈ B.realSpectrum := by
        simpa only [realSpectrum_eq_spectraSpectrum, Set.mem_preimage]
          using hlamSpec
      rcases hgap.2 hreal with hleft | hright
      · exact (not_lt_of_ge hleft) hlam.1
      · exact (not_lt_of_ge hright) hlam.2
  · right
    constructor
    · simpa only [realSpectrum_eq_spectraSpectrum] using hgap.1
    · intro lam hlam hlamSpec
      have hreal : lam ∈ A.realSpectrum := by
        simpa only [realSpectrum_eq_spectraSpectrum, Set.mem_preimage]
          using hlamSpec
      rcases hgap.2 hreal with hleft | hright
      · exact (not_lt_of_ge hleft) hlam.1
      · exact (not_lt_of_ge hright) hlam.2

omit [CompleteSpace E] [CompleteSpace F] in
/-- The interval/exterior constructor of the form-bounded gap embeds into the
spectral all-gap predicate.  Ordered constructors are intentionally handled by
their form bounds rather than translated into spectral containments. -/
theorem UnboundedSylvesterGap.intervalExterior_of_formBounded
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    {β α δ : ℝ}
    (hβα : β ≤ α)
    (hgap : RealSpectrumIntervalExteriorGap A B β α δ) :
    UnboundedSylvesterGap A B δ :=
  UnboundedSylvesterGap.intervalExterior hβα
    (sylvesterIntervalExteriorGap_of_realSpectrum hgap)

/-- Admission-free complex specialization of the manuscript Section 5
Sylvester theorem.  The spectral constructor is routed through the Spectra
spectrum theorem, while the two ordered constructors retain their form-bound
hypotheses and call the direct engine verbatim. -/
theorem davisKahan1970_sylvester_complex
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gauge X ≤
        N.gauge C := by
  cases hgap with
  | intervalExterior hβα hgap =>
      exact davisKahan1970_sylvester_of_spectrumGap
        N hA hB hδ
          (UnboundedSylvesterGap.intervalExterior_of_formBounded hβα hgap)
          hEq hC
  | leftAboveRightBelow c hAc hBc =>
      exact directOrderedSylvesterEngine_lowerUpper
        N hA hB hδ hAc hBc hEq hC
  | leftBelowRightAbove c hAc hBc =>
      exact directOrderedSylvesterEngine_upperLower
        N hA hB hδ hAc hBc hEq hC

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti