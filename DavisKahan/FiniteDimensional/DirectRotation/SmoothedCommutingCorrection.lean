/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedExplicitOptimizer

/-!
# Exact smoothed correction to a subspace-preserving unitary

The transporter minimum gives an explicit closest unitary preserving a fixed
subspace. The objective below is the literal singular-value cost of the
operator difference, not a surrogate bound on a commutator.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The literal Charbonnier singular-value distance between two operators. -/
@[expose]
def smoothedOperatorDistance (tau : ℝ) (A B : E →ₗ[ℂ] E) : ℝ :=
  ∑ i : Fin (Module.finrank ℂ E),
    (Real.sqrt (tau ^ 2 + ((A - B).singularValues i) ^ 2) - tau)

omit [CompleteSpace E] in
/-- Right unitary invariance turns operator distance into displacement. -/
theorem smoothedOperatorDistance_eq_displacement
    (tau : ℝ) (A B : E ≃ₗᵢ[ℂ] E) :
    smoothedOperatorDistance tau A.toLinearMap B.toLinearMap =
      smoothedDisplacementCost tau (B.symm.trans A).toLinearMap := by
  have hfac :
      (LinearMap.id - (B.symm.trans A).toLinearMap) ∘ₗ B.toLinearMap =
        B.toLinearMap - A.toLinearMap := by
    ext x
    simp
  have hsv : (A.toLinearMap - B.toLinearMap).singularValues =
      (B.toLinearMap - A.toLinearMap).singularValues := by
    apply LinearMap.singularValues_eq_of_norm_apply_eq
    intro x
    simp only [LinearMap.sub_apply, norm_sub_rev]
  unfold smoothedOperatorDistance smoothedDisplacementCost
  have hsing := LinearMap.singularValues_comp_linearIsometryEquiv
    (LinearMap.id - (B.symm.trans A).toLinearMap) B
  change ((LinearMap.id - (B.symm.trans A).toLinearMap) ∘ₗ B.toLinearMap).singularValues =
    (LinearMap.id - (B.symm.trans A).toLinearMap).singularValues at hsing
  rw [hsv, ← hfac, hsing]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- Composing a subspace transporter with the inverse target unitary gives
an operator preserving the source subspace. -/
theorem correction_preserves_subspace
    (K : Submodule ℂ E) (A W : E ≃ₗᵢ[ℂ] E)
    (hW : K.map W.toLinearMap = K.map A.toLinearMap) :
    K.map (A.trans W.symm).toLinearMap = K := by
  change K.map (W.symm.toLinearMap ∘ₗ A.toLinearMap) = K
  rw [Submodule.map_comp, ← hW, ← Submodule.map_comp]
  simp

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- A source-preserving correction determines an admissible transporter. -/
theorem transporter_of_correction_preserves_subspace
    (K : Submodule ℂ E) (A V : E ≃ₗᵢ[ℂ] E)
    (hV : K.map V.toLinearMap = K) :
    K.map (V.symm.trans A).toLinearMap = K.map A.toLinearMap := by
  have hsymm : K.map V.symm.toLinearMap = K := by
    calc
      _ = (K.map V.toLinearMap).map V.symm.toLinearMap := congrArg _ hV.symm
      _ = K := by rw [← Submodule.map_comp]; simp
  change K.map (A.toLinearMap ∘ₗ V.symm.toLinearMap) = _
  rw [Submodule.map_comp, hsymm]

/-- The explicit closest subspace-preserving unitary, obtained from the
spectral optimizer for the source and its actual image. -/
@[expose]
def optimalSmoothedCorrection (tau : ℝ) (K : Submodule ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) : E ≃ₗᵢ[ℂ] E :=
  A.trans (optimalSmoothedTransport tau K (K.map A.toLinearMap)
    (A.toLinearEquiv.finrank_map_eq K).symm).symm

/-- The explicit correction preserves the prescribed subspace. -/
theorem optimalSmoothedCorrection_preserves (tau : ℝ) (K : Submodule ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) :
    K.map (optimalSmoothedCorrection tau K A).toLinearMap = K := by
  exact correction_preserves_subspace K A _
    (optimalSmoothedTransport_maps tau K (K.map A.toLinearMap) _)

/-- The exact distance to the explicit correction is the angle formula for
the subspace and its image under the given unitary. -/
theorem smoothedOperatorDistance_optimalSmoothedCorrection
    (tau : ℝ) (hτ : 0 < tau) (K : Submodule ℂ E) (A : E ≃ₗᵢ[ℂ] E) :
    smoothedOperatorDistance tau A.toLinearMap
        (optimalSmoothedCorrection tau K A).toLinearMap =
      ∑ i : Fin (Module.finrank ℂ K),
        smoothedPhaseMinimum tau (K.principalAngles (K.map A.toLinearMap) i) := by
  let W := optimalSmoothedTransport tau K (K.map A.toLinearMap)
    (A.toLinearEquiv.finrank_map_eq K).symm
  have hrel : (optimalSmoothedCorrection tau K A).symm.trans A = W := by
    ext x
    simp [optimalSmoothedCorrection, W]
  rw [smoothedOperatorDistance_eq_displacement, hrel]
  exact smoothedDisplacementCost_optimalSmoothedTransport tau hτ K (K.map A.toLinearMap) _

/-- The spectral correction is globally closest among all unitary
operators preserving the prescribed subspace. -/
theorem optimalSmoothedCorrection_isMin
    (tau : ℝ) (hτ : 0 < tau) (K : Submodule ℂ E) (A V : E ≃ₗᵢ[ℂ] E)
    (hV : K.map V.toLinearMap = K) :
    smoothedOperatorDistance tau A.toLinearMap
        (optimalSmoothedCorrection tau K A).toLinearMap ≤
      smoothedOperatorDistance tau A.toLinearMap V.toLinearMap := by
  rw [smoothedOperatorDistance_optimalSmoothedCorrection tau hτ,
    smoothedOperatorDistance_eq_displacement]
  obtain ⟨_, _, _, hmin⟩ := exists_unitary_minimizing_smoothed_transport_principalAngles
    tau hτ K (K.map A.toLinearMap) (A.toLinearEquiv.finrank_map_eq K).symm
  exact hmin _ (transporter_of_correction_preserves_subspace K A V hV)

/-- The explicit correction commutes with the prescribed orthogonal
projection, so it preserves both complementary subspaces. -/
theorem optimalSmoothedCorrection_commutes
    (tau : ℝ) (K : Submodule ℂ E) (A : E ≃ₗᵢ[ℂ] E) (x : E) :
    optimalSmoothedCorrection tau K A (K.starProjection x) =
      K.starProjection (optimalSmoothedCorrection tau K A x) := by
  let V := optimalSmoothedCorrection tau K A
  have h := Submodule.starProjection_map_apply V K (V x)
  simpa only [show K.map V.toLinearMap = K from optimalSmoothedCorrection_preserves tau K A,
    V.symm_apply_apply] using h.symm

/-- The literal smoothed distance is minimized over all unitaries commuting
with the prescribed projection. -/
theorem optimalSmoothedCorrection_isMin_of_commute
    (tau : ℝ) (hτ : 0 < tau) (K : Submodule ℂ E) (A V : E ≃ₗᵢ[ℂ] E)
    (hV : ∀ x, V (K.starProjection x) = K.starProjection (V x)) :
    smoothedOperatorDistance tau A.toLinearMap
        (optimalSmoothedCorrection tau K A).toLinearMap ≤
      smoothedOperatorDistance tau A.toLinearMap V.toLinearMap := by
  apply optimalSmoothedCorrection_isMin tau hτ K A V
  apply (K.map_eq_iff_intertwines_reflection K V).mpr
  intro x
  simp only [Submodule.reflection_apply, map_sub, map_nsmul, hV]

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
