/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedKernelPlanes
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPrincipalAngles
public import ForTauCeti.Analysis.InnerProductSpace.Projection.BalancedReflectionTrace

/-!
# Balanced reflections attain the unrestricted smoothed minimum

The exact fixed/right principal-angle trace equals the literal cost of
the balanced reflection. The already established global angle lower bound
then compares it with every ambient unitary competitor.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every balanced reflecting transport attains the exact unrestricted
Charbonnier principal-angle minimum, including all fixed directions. -/
theorem balanced_reflection_cost_eq_sum_principalAngles_complex
    (tau : ℝ) (htau : 0 < tau) (K L : Submodule ℂ E)
    (A : E →L[ℂ] E) (hA : IsStarProjection A)
    (hbalance : (2 : ℂ) • (A * K.starProjection * A) = A)
    (V : E ≃ₗᵢ[ℂ] E) (hV : (V : E →L[ℂ] E) = 1 - (2 : ℂ) • A)
    (hmap : K.map V.toLinearMap = L) :
    smoothedDisplacementCost tau V.toLinearMap =
      ∑ i : Fin (Module.finrank ℂ K), smoothedPhaseMinimum tau (K.principalAngles L i) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hcost⟩ :=
    balanced_reflection_smoothed_paired_planes_complex tau htau.le K A hA hbalance V hV
  have hsum := K.sum_principalAngles_of_balanced_reflection_complex L A hA hbalance V hV hmap
    (smoothedPhaseMinimum tau) (smoothedPhaseMinimum_zero_angle tau htau)
  rw [smoothedPhaseMinimum_right_angle tau htau] at hsum
  exact hcost.trans hsum.symm

/-- Balance certifies a reflecting transport against all ambient unitary
competitors, without requiring them to preserve the reflection planes. -/
theorem balanced_reflection_minimizes_smoothed_transport_complex
    (tau : ℝ) (htau : 0 < tau) (K L : Submodule ℂ E)
    (A : E →L[ℂ] E) (hA : IsStarProjection A)
    (hbalance : (2 : ℂ) • (A * K.starProjection * A) = A)
    (V : E ≃ₗᵢ[ℂ] E) (hV : (V : E →L[ℂ] E) = 1 - (2 : ℂ) • A)
    (hmap : K.map V.toLinearMap = L) :
    ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      smoothedDisplacementCost tau V.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap := by
  have hKL : Module.finrank ℂ K = Module.finrank ℂ L := by
    rw [← hmap]
    exact (V.toLinearEquiv.finrank_map_eq K).symm
  obtain ⟨_, _, _, hbound⟩ :=
    exists_unitary_minimizing_smoothed_transport_principalAngles tau htau K L hKL
  intro T hT
  rw [balanced_reflection_cost_eq_sum_principalAngles_complex tau htau K L A hA hbalance V hV hmap]
  exact hbound T hT

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
