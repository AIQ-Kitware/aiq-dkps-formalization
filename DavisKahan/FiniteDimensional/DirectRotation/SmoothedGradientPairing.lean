/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedGradientSpectrum
public import ForTauCeti.Analysis.InnerProductSpace.AnticommutingInvolution
public import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# Pairing opposite Charbonnier-gradient eigenspaces

At a constrained local minimum, reflection across the source subspace
interchanges the opposite gradient eigenspaces. The pairing is the restriction
of that actual reflection, not only an abstract equality of dimensions.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Source reflection gives an isometric pairing of opposite gradient
levels at every local Charbonnier transport minimum. -/
theorem gradient_eigenspace_pairing_of_isLocalMinOn_transports
    (tau : ℝ) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) (g : ℂ) :
    ∃ e : Module.End.eigenspace
          (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap g ≃ₗᵢ[ℂ]
        Module.End.eigenspace
          (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap (-g),
      ∀ x, (e x : E) = K.reflection x := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    tau htau K.starProjection Q hP U htrans hmin
  have hreflection : (K.reflection : E →L[ℂ] E) =
      (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hreflection] at hconj
  have hanti (x : E) : G (K.reflection x) = -K.reflection (G x) := by
    have h := congrArg (fun A : E →L[ℂ] E => A (K.reflection x)) hconj
    change K.reflection (G (K.reflection (K.reflection x))) = -G (K.reflection x) at h
    rw [K.reflection_reflection] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  refine ⟨eigenspaceNegEquivOfInvolution K.reflection K.reflection_involutive
    G.toLinearMap hanti g, ?_⟩
  intro x
  exact eigenspaceNegEquivOfInvolution_apply _ _ _ _ _ x

/-- The square of the Charbonnier gradient commutes with both transported
projections at every constrained local minimum. Its spectral blocks
therefore reduce the source and target simultaneously. -/
theorem gradient_square_reduces_projections_of_isLocalMinOn_transports
    (tau : ℝ) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) :
    let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
    Commute K.starProjection (G * G) ∧ Commute Q (G * G) := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    tau htau K.starProjection Q hP U htrans hmin
  have hreflection : (K.reflection : E →L[ℂ] E) =
      (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hreflection] at hconj
  have hsource : Commute K.starProjection (G * G) :=
    commute_square_of_reflection_conjugate_eq_neg G K hconj
  refine ⟨hsource, ?_⟩
  have hGU : Commute G (U : E →L[ℂ] E) :=
    commute_smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  have hG : IsSelfAdjoint G := isSelfAdjoint_smoothedUnitaryGradient _ _
  have hGUstar : Commute G (star (U : E →L[ℂ] E)) := by
    simpa only [hG.star_eq] using hGU.star_star
  rw [← htrans]
  exact ((hGU.mul_left hGU).symm.mul_left hsource).mul_left
    (hGUstar.mul_left hGUstar).symm

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
