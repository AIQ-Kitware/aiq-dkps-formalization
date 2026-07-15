/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationNumbers

/-!
# Fully unbounded Sylvester estimates

This module combines two routes to Davis--Kahan Theorem 5.2.  The
Laplace-semigroup route yields the final theorem from ordinary rectangular
Banach ideal laws.  The spectral-cutoff route follows the paper through finite
Ky Fan estimates and therefore uses `KyFanDominantIdealFamily`; that stronger
property is not derived from the ordinary ideal laws.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

abbrev ClosedOperatorOnE :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)
abbrev ClosedOperatorOnF :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)

/-- Spectral cutoff converts the right block to a bounded Sylvester equation. -/
theorem spectralCutoff_sylvester_equation
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E}
    (hEq : HasClosedSylvesterEquation A B X C)
    (τ : ℝ) :
    HasUnboundedBoundedSylvesterEquation A
      (boundedSpectralTruncation B hB τ)
      (X ∘L spectralCutoff B hB τ)
      (C ∘L spectralCutoff B hB τ) := by
  sorry

/-- Ky Fan estimate obtained from bounded spectral truncations. -/
theorem kyFan_unbounded_sylvester_le_of_semibounded
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedBelow A (c + δ))
    (hBc : SemiboundedAbove B c)
    (hEq : HasClosedSylvesterEquation A B X C) :
    ∀ k, δ * kyFanApproximationGauge k X
      ≤ kyFanApproximationGauge k C := by
  sorry

/-- The opposite ordered orientation, obtained by adjointing and swapping the
two closed blocks. -/
theorem kyFan_unbounded_sylvester_le_of_semibounded_swapped
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedAbove A c)
    (hBc : SemiboundedBelow B (c + δ))
    (hEq : HasClosedSylvesterEquation A B X C) :
    ∀ k, δ * kyFanApproximationGauge k X
      ≤ kyFanApproximationGauge k C := by
  sorry

/-- Ideal membership of the Sylvester solution from ordered cutoff estimates. -/
theorem unbounded_sylvester_mem_of_semibounded_viaKyFan
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedBelow A (c + δ))
    (hBc : SemiboundedAbove B c)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X := by
  exact (mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hδ hC
      (kyFan_unbounded_sylvester_le_of_semibounded
        hA hB hδ hAc hBc hEq)).1

/-- Davis--Kahan Theorem 5.2 in the lower-left/upper-right orientation. -/
theorem unbounded_sylvester_mem_and_gauge_le_viaKyFan
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedBelow A (c + δ))
    (hBc : SemiboundedAbove B c)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧ δ * N.toRectangularSymmetricIdealFamily.gauge X ≤ N.toRectangularSymmetricIdealFamily.gauge C := by
  exact mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hδ hC
      (kyFan_unbounded_sylvester_le_of_semibounded
        hA hB hδ hAc hBc hEq)

/-- Davis--Kahan Theorem 5.2 in the upper-left/lower-right orientation. -/
theorem unbounded_sylvester_mem_and_gauge_le_swapped_viaKyFan
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedAbove A c)
    (hBc : SemiboundedBelow B (c + δ))
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧ δ * N.toRectangularSymmetricIdealFamily.gauge X ≤ N.toRectangularSymmetricIdealFamily.gauge C := by
  exact mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hδ hC
      (kyFan_unbounded_sylvester_le_of_semibounded_swapped
        hA hB hδ hAc hBc hEq)

/-- Exact interval/exterior form with one bounded spectral block and one
possibly unbounded exterior block.  This theorem only needs the ordinary
rectangular ideal interface. -/
theorem unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {β α δ : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : UnboundedIntervalExteriorGap A B β α δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  sorry

/-- All source-faithful unbounded gap configurations needed by the `sin Θ`
endpoint.  The ordered constructors allow both diagonal blocks to be genuinely
unbounded; the interval/exterior constructor has a bounded spectral block. -/
inductive UnboundedSylvesterGap
    (A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E))
    (B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F))
    (δ : ℝ) : Prop where
  | intervalExterior
      {β α : ℝ}
      (hβα : β ≤ α)
      (hgap : UnboundedIntervalExteriorGap A B β α δ)
  | leftAboveRightBelow
      (c : ℝ)
      (hA : SemiboundedBelow A (c + δ))
      (hB : SemiboundedAbove B c)
  | leftBelowRightAbove
      (c : ℝ)
      (hA : SemiboundedAbove A c)
      (hB : SemiboundedBelow B (c + δ))

/-- Complete unified unbounded Sylvester estimate.  The finite-interval branch
uses the one-unbounded theorem; the two ordered branches use the paper's
spectral-cutoff and finite-Ky-Fan argument.  The stronger family is the precise
abstraction needed for this passage and is not derived from ordinary ideal
laws. -/
theorem unbounded_sylvester_mem_and_gauge_le_of_gap
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge X ≤
        N.toRectangularSymmetricIdealFamily.gauge C := by
  cases hgap with
  | intervalExterior hβα hgap =>
      exact unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap
        N.toRectangularSymmetricIdealFamily hA hB hβα hδ hgap hEq hC
  | leftAboveRightBelow c hAc hBc =>
      exact unbounded_sylvester_mem_and_gauge_le_viaKyFan
        N hA hB hδ hAc hBc hEq hC
  | leftBelowRightAbove c hAc hBc =>
      exact unbounded_sylvester_mem_and_gauge_le_swapped_viaKyFan
        N hA hB hδ hAc hBc hEq hC

/-- Canonical source-facing Section 5 engine consumed by the general sine
 theorem.  The scoped name emphasizes that bounded Sylvester estimates are
 specializations or independent alternatives rather than the root theorem. -/
theorem davisKahan1970_sylvester
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge X ≤
        N.toRectangularSymmetricIdealFamily.gauge C :=
  unbounded_sylvester_mem_and_gauge_le_of_gap N hA hB hδ hgap hEq hC

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
