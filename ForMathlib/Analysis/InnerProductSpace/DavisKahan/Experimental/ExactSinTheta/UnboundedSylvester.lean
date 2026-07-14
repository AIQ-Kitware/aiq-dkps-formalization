/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.ExactSinTheta.ApproximationNumbers

/-!
# Fully unbounded Sylvester estimate

This module records the domain-aware equation and the spectral-truncation path
to Davis--Kahan Theorem 5.2.  The Ky Fan truncation theorem is kept separate
from the final ideal-norm consequence.
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

/-- Lower semibound for a closed operator. -/
def SemiboundedBelow
    (A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    c * ‖(x : E)‖ ^ 2 ≤
      RCLike.re ⟪A.toLinearMap x, (x : E)⟫_𝕜

/-- Upper semibound for a closed operator. -/
def SemiboundedAbove
    (A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    RCLike.re ⟪A.toLinearMap x, (x : E)⟫_𝕜
      ≤ c * ‖(x : E)‖ ^ 2

/-- Domain-aware equation `A X - X B = C`. -/
def HasClosedSylvesterEquation
    (A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E))
    (B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F))
    (X C : F →L[𝕜] E) : Prop :=
  ∀ x : B.domain,
    ∃ hx : X (x : F) ∈ A.domain,
      A.toLinearMap ⟨X (x : F), hx⟩ -
        X (B.toLinearMap x) = C (x : F)

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

/-- Ideal membership of the Sylvester solution from the cutoff estimates. -/
theorem unbounded_sylvester_mem_of_semibounded
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedBelow A (c + δ))
    (hBc : SemiboundedAbove B c)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X := by
  sorry

/-- Davis--Kahan Theorem 5.2 for a rectangular ideal family. -/
theorem unbounded_sylvester_mem_and_gauge_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedBelow A (c + δ))
    (hBc : SemiboundedAbove B c)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  sorry

/-- Exact interval/exterior form with one bounded spectral block and one
possibly unbounded exterior block. -/
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

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
