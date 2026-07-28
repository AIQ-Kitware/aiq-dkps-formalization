/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.Unbounded.AllGap
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
namespace Experimental
namespace ExactSinTheta

universe u v

namespace GenuineUnboundedSylvesterGap

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Genuine interval/exterior separation, named for a trial/complementary
sine-theta application. -/
theorem trialInterval_complementExterior
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    {β α δ : ℝ} (hβα : β ≤ α)
    (hgap : GenuineSylvesterIntervalExteriorGap A B β α δ) :
    GenuineUnboundedSylvesterGap A B δ :=
  .intervalExterior hβα hgap

/-- The trial spectrum lies above the complementary spectrum. -/
theorem trialAbove_complementBelow
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    {δ c : ℝ}
    (hA : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A.toLinearPMap ⊆
        Set.Ici (c + δ))
    (hB : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B.toLinearPMap ⊆
        Set.Iic c) :
    GenuineUnboundedSylvesterGap A B δ :=
  .leftAboveRightBelow c hA hB

/-- The trial spectrum lies below the complementary spectrum. -/
theorem trialBelow_complementAbove
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    {δ c : ℝ}
    (hA : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A.toLinearPMap ⊆
        Set.Iic c)
    (hB : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B.toLinearPMap ⊆
        Set.Ici (c + δ)) :
    GenuineUnboundedSylvesterGap A B δ :=
  .leftBelowRightAbove c hA hB

end GenuineUnboundedSylvesterGap

namespace UnboundedSylvesterGap

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Legacy-spectrum interval/exterior separation, named for a
trial/complementary sine-theta application. -/
theorem trialInterval_complementExterior
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    {β α δ : ℝ} (hβα : β ≤ α)
    (hgap : UnboundedIntervalExteriorGap A B β α δ) :
    UnboundedSylvesterGap A B δ :=
  .intervalExterior hβα hgap

/-- The trial operator is semibounded above the complementary operator. -/
theorem trialAbove_complementBelow
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    {δ c : ℝ}
    (hA : SemiboundedBelow A (c + δ))
    (hB : SemiboundedAbove B c) :
    UnboundedSylvesterGap A B δ :=
  .leftAboveRightBelow c hA hB

/-- The trial operator is semibounded below the complementary operator. -/
theorem trialBelow_complementAbove
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    {δ c : ℝ}
    (hA : SemiboundedAbove A c)
    (hB : SemiboundedBelow B (c + δ)) :
    UnboundedSylvesterGap A B δ :=
  .leftBelowRightAbove c hA hB

end UnboundedSylvesterGap

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti