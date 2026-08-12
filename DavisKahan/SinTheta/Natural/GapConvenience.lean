/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.Unbounded.AllGap
import DavisKahan.SinTheta.Unbounded.AllGap
import DavisKahan.Sylvester.Gap
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Source-oriented constructors for the three unbounded gap configurations

The underlying Sylvester predicates name their two operators `left` and
`right`. In sine-theta applications the left operator is the trial operator and
the right operator is the complementary exact restriction. These constructor
aliases expose that interpretation directly and keep theorem call sites from
having to remember the orientation convention.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

universe u v

namespace SpectralSylvesterGap

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Genuine interval/exterior separation, named for a trial/complementary
sine-theta application. -/
theorem trialInterval_complementExterior
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    {β α δ : ℝ} (hβα : β ≤ α)
    (hgap : SpectralIntervalExteriorGap A B β α δ) :
    SpectralSylvesterGap A B δ :=
  .intervalExterior hβα hgap

omit [CompleteSpace E] [CompleteSpace F] in
/-- The trial spectrum lies above the complementary spectrum. -/
theorem trialAbove_complementBelow
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    {δ c : ℝ}
    (hA : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A.toLinearPMap ⊆
        Set.Ici (c + δ))
    (hB : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B.toLinearPMap ⊆
        Set.Iic c) :
    SpectralSylvesterGap A B δ :=
  .leftAboveRightBelow c hA hB

omit [CompleteSpace E] [CompleteSpace F] in
/-- The trial spectrum lies below the complementary spectrum. -/
theorem trialBelow_complementAbove
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    {δ c : ℝ}
    (hA : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A.toLinearPMap ⊆
        Set.Iic c)
    (hB : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B.toLinearPMap ⊆
        Set.Ici (c + δ)) :
    SpectralSylvesterGap A B δ :=
  .leftBelowRightAbove c hA hB

omit [CompleteSpace E] [CompleteSpace F] in
/-- Raw partial-map form of `trialInterval_complementExterior`. -/
theorem linearPMap_trialInterval_complementExterior
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    {β α δ : ℝ} (hβα : β ≤ α)
    (hgap : UnboundedIntervalExteriorGapPMap A B β α δ) :
    UnboundedSylvesterGapPMap A B δ :=
  .intervalExterior hβα hgap

omit [CompleteSpace E] [CompleteSpace F] in
/-- Raw partial-map form of `trialAbove_complementBelow`. -/
theorem linearPMap_trialAbove_complementBelow
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F} {δ c : ℝ}
    (hA : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A ⊆ Set.Ici (c + δ))
    (hB : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B ⊆ Set.Iic c) :
    UnboundedSylvesterGapPMap A B δ :=
  .leftAboveRightBelow c hA hB

omit [CompleteSpace E] [CompleteSpace F] in
/-- Raw partial-map form of `trialBelow_complementAbove`. -/
theorem linearPMap_trialBelow_complementAbove
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F} {δ c : ℝ}
    (hA : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A ⊆ Set.Iic c)
    (hB : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B ⊆ Set.Ici (c + δ)) :
    UnboundedSylvesterGapPMap A B δ :=
  .leftBelowRightAbove c hA hB

end SpectralSylvesterGap

namespace FormBoundedSylvesterGap

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Legacy-spectrum interval/exterior separation, named for a
trial/complementary sine-theta application. -/
theorem trialInterval_complementExterior
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    {β α δ : ℝ} (hβα : β ≤ α)
    (hgap : RealSpectrumIntervalExteriorGap A B β α δ) :
    FormBoundedSylvesterGap A B δ :=
  .intervalExterior hβα hgap

omit [CompleteSpace E] [CompleteSpace F] in
/-- The trial operator is semibounded above the complementary operator. -/
theorem trialAbove_complementBelow
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    {δ c : ℝ}
    (hA : SemiboundedBelow A (c + δ))
    (hB : SemiboundedAbove B c) :
    FormBoundedSylvesterGap A B δ :=
  .leftAboveRightBelow c hA hB

omit [CompleteSpace E] [CompleteSpace F] in
/-- The trial operator is semibounded below the complementary operator. -/
theorem trialBelow_complementAbove
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    {δ c : ℝ}
    (hA : SemiboundedAbove A c)
    (hB : SemiboundedBelow B (c + δ)) :
    FormBoundedSylvesterGap A B δ :=
  .leftBelowRightAbove c hA hB

omit [CompleteSpace E] [CompleteSpace F] in
/-- Raw partial-map form of `trialInterval_complementExterior`. -/
theorem linearPMap_trialInterval_complementExterior
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {β α δ : ℝ} (hβα : β ≤ α)
    (hgap : linearPMap_RealSpectrumIntervalExteriorGap A B β α δ) :
    linearPMap_FormBoundedSylvesterGap A B δ :=
  .intervalExterior hβα hgap

omit [CompleteSpace E] [CompleteSpace F] in
/-- Raw partial-map form of `trialAbove_complementBelow`. -/
theorem linearPMap_trialAbove_complementBelow
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {δ c : ℝ}
    (hA : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hB : TauCeti.LinearPMap.SemiboundedAbove B c) :
    linearPMap_FormBoundedSylvesterGap A B δ :=
  .leftAboveRightBelow c hA hB

omit [CompleteSpace E] [CompleteSpace F] in
/-- Raw partial-map form of `trialBelow_complementAbove`. -/
theorem linearPMap_trialBelow_complementAbove
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {δ c : ℝ}
    (hA : TauCeti.LinearPMap.SemiboundedAbove A c)
    (hB : TauCeti.LinearPMap.SemiboundedBelow B (c + δ)) :
    linearPMap_FormBoundedSylvesterGap A B δ :=
  .leftBelowRightAbove c hA hB

end FormBoundedSylvesterGap

end ExactSinTheta
end DavisKahan
end TauCeti