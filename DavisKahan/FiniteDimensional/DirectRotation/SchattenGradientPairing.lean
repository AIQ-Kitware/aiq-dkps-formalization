/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenStationarity
public import ForTauCeti.Analysis.InnerProductSpace.AnticommutingInvolution
public import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# Pairing opposite Schatten-gradient eigenspaces

At a constrained local minimum, reflection across the source subspace
interchanges the opposite gradient eigenspaces. The pairing is the restriction
of that actual reflection, not only an abstract equality of dimensions.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Source reflection gives an isometric pairing of opposite gradient
levels at every local Schatten transport minimum. -/
theorem gradient_eigenspace_pairing_of_isLocalMinOn_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) (g : ℂ) :
    ∃ e : Module.End.eigenspace
          (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap g ≃ₗᵢ[ℂ]
        Module.End.eigenspace
          (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap (-g),
      ∀ x, (e x : E) = K.reflection x := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    p hp hp1 K.starProjection Q hP U htrans hmin
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

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
