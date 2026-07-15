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
  classical
  intro x hx
  have hcutDom : spectralCutoff B hB τ x ∈ B.domain :=
    spectralCutoff_range_le_domain B hB τ x
  have hbase := hEq (spectralCutoff B hB τ x) hcutDom
  rw [boundedSpectralTruncation_eq_on_cutoff B hB τ]
  rw [spectralCutoff_commutes_on_domain B hB τ x hcutDom]
  simpa [ContinuousLinearMap.comp_apply] using hbase

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
  classical
  intro k
  have hfinite : ∀ τ : ℝ,
      δ * kyFanApproximationGauge k (X ∘L spectralCutoff B hB τ) ≤
        kyFanApproximationGauge k (C ∘L spectralCutoff B hB τ) := by
    intro τ
    have hEqτ := spectralCutoff_sylvester_equation hA hB hEq τ
    have hBτ := boundedSpectralTruncation_upperBound B hB τ hBc
    exact kyFan_unboundedBounded_sylvester_le_of_semibounded
      hA hBτ hδ hAc hEqτ k
  have hlimX : Tendsto
      (fun τ : ℝ => δ * kyFanApproximationGauge k
        (X ∘L spectralCutoff B hB τ)) atTop
      (𝓝 (δ * kyFanApproximationGauge k X)) := by
    exact (kyFanApproximationGauge_comp_strongProjection_tendsto X
      (spectralCutoff_tendsto_identity B hB)).const_mul δ
  have hlimC : Tendsto
      (fun τ : ℝ => kyFanApproximationGauge k
        (C ∘L spectralCutoff B hB τ)) atTop
      (𝓝 (kyFanApproximationGauge k C)) :=
    kyFanApproximationGauge_comp_strongProjection_tendsto C
      (spectralCutoff_tendsto_identity B hB)
  exact le_of_tendsto_of_tendsto hlimX hlimC
    (eventually_of_forall hfinite)

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
  classical
  intro k
  have hstarEq : HasClosedSylvesterEquation B A X.adjoint C.adjoint :=
    hEq.adjoint
  have h := kyFan_unbounded_sylvester_le_of_semibounded
    hB hA hδ hBc hAc hstarEq k
  simpa [kyFanApproximationGauge_adjoint] using h

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
  classical
  have hKyFan : ∀ k, δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k C :=
    kyFan_unbounded_sylvester_le_of_semibounded hA hB hδ hAc hBc hEq
  exact (N.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    hδ hC hKyFan).1

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
  classical
  have hKyFan : ∀ k, δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k C :=
    kyFan_unbounded_sylvester_le_of_semibounded hA hB hδ hAc hBc hEq
  exact N.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le hδ hC hKyFan

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
  classical
  have hKyFan : ∀ k, δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k C :=
    kyFan_unbounded_sylvester_le_of_semibounded_swapped
      hA hB hδ hAc hBc hEq
  exact N.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le hδ hC hKyFan

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
  classical
  obtain hleft | hright := hgap.exterior_split
  · have hInv := boundedInverse_of_spectrumOutside A hA
      (Set.Iic (β-δ)) hleft
    have hBounded := boundedRealization_of_spectrumIn_Icc B hB hgap.intervalBlock
    exact sylvester_mem_and_gauge_le_of_unbounded_bound_inverse
      N hA hInv hBounded hβα hδ hEq hC
  · have hInv := boundedInverse_of_spectrumOutside A hA
      (Set.Ici (α+δ)) hright
    have hBounded := boundedRealization_of_spectrumIn_Icc B hB hgap.intervalBlock
    exact sylvester_mem_and_gauge_le_of_unbounded_bound_inverse_swapped
      N hA hInv hBounded hβα hδ hEq hC

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
  classical
  cases hgap with
  | intervalExterior hβα hgap =>
      have h := unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap
        N.toRectangularSymmetricIdealFamily hA hB hβα hδ hgap hEq hC
      exact h
  | leftAboveRightBelow c hAc hBc =>
      exact unbounded_sylvester_mem_and_gauge_le_viaKyFan
        N hA hB hδ hAc hBc hEq hC
  | leftBelowRightAbove c hAc hBc =>
      exact unbounded_sylvester_mem_and_gauge_le_swapped_viaKyFan
        N hA hB hδ hAc hBc hEq hC

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
