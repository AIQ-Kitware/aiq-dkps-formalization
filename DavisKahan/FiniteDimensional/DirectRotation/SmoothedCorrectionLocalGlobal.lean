/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedLocalGlobal
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCommutingCorrection
public import ForTauCeti.Analysis.InnerProductSpace.UnitaryCorrectionLocalGlobal

/-!
# Every local smoothed unitary correction is globally nearest

The literal singular-value cost of correcting an input unitary while
preserving a prescribed subspace has no nonglobal local minima. Right
unitary invariance identifies it with the solved transport problem.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every local Charbonnier-nearest unitary preserving a prescribed
subspace is globally nearest. The literal operator-difference cost and
all feasible ambient unitary competitors are retained. -/
theorem isMinOn_correction_of_isLocalMinOn_preserving_subspace_complex
    (tau : ℝ) (htau : 0 < tau) (K : Submodule ℂ E)
    (A V : E ≃ₗᵢ[ℂ] E) (hV : K.map V.toLinearMap = K)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedOperatorDistance tau A.toLinearMap W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = K.starProjection}
      (V : E →L[ℂ] E)) :
    IsMinOn (fun W : E →L[ℂ] E => smoothedOperatorDistance tau A.toLinearMap W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = K.starProjection}
      (V : E →L[ℂ] E) := by
  let L := K.map A.toLinearMap
  let A' := Unitary.linearIsometryEquiv.symm A
  let V' := Unitary.linearIsometryEquiv.symm V
  have hAmap : K.map (Unitary.linearIsometryEquiv A').toLinearMap = L := by
    simpa only [A', MulEquiv.apply_symm_apply] using (show K.map A.toLinearMap = L from rfl)
  have hVmap : K.map (Unitary.linearIsometryEquiv V').toLinearMap = K := by
    simpa only [V', MulEquiv.apply_symm_apply] using hV
  have hAtrans := (SchattenPhaseTransition.map_eq_iff_conjugate_starProjection_complex K L A').mp hAmap
  have hVtrans := (SchattenPhaseTransition.map_eq_iff_conjugate_starProjection_complex K K V').mp hVmap
  have hcost (W : E →L[ℂ] E) :
      smoothedOperatorDistance tau A.toLinearMap (W * (A : E →L[ℂ] E)).toLinearMap =
        smoothedDisplacementCost tau W.toLinearMap := by
    have hfactor : A.toLinearMap - (W * (A : E →L[ℂ] E)).toLinearMap =
        (LinearMap.id - W.toLinearMap) ∘ₗ A.toLinearMap := by ext x; rfl
    have hsv := LinearMap.singularValues_comp_linearIsometryEquiv
      (LinearMap.id - W.toLinearMap) A
    change ((LinearMap.id - W.toLinearMap) ∘ₗ A.toLinearMap).singularValues =
      (LinearMap.id - W.toLinearMap).singularValues at hsv
    rw [smoothedOperatorDistance, smoothedDisplacementCost, hfactor, hsv]
  exact isMinOn_unitary_correction_of_transport_local_global K.starProjection L.starProjection A' V'
    hAtrans hVtrans
    (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
    (fun W : E →L[ℂ] E => smoothedOperatorDistance tau A.toLinearMap W.toLinearMap)
    hcost (fun T ht hlocal => isMinOn_of_isLocalMinOn_transports_complex tau htau L K T
      ((SchattenPhaseTransition.map_eq_iff_conjugate_starProjection_complex L K T).mpr ht) hlocal) hmin

/-- Every local minimum of the literal Charbonnier correction cost in the
unitary commutant of a prescribed projection is globally nearest. -/
theorem isMinOn_correction_of_isLocalMinOn_commutant_complex
    (tau : ℝ) (htau : 0 < tau) (K : Submodule ℂ E) (A V : E ≃ₗᵢ[ℂ] E)
    (hV : Commute (V : E →L[ℂ] E) K.starProjection)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedOperatorDistance tau A.toLinearMap W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ Commute W K.starProjection}
      (V : E →L[ℂ] E)) :
    IsMinOn (fun W : E →L[ℂ] E => smoothedOperatorDistance tau A.toLinearMap W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ Commute W K.starProjection}
      (V : E →L[ℂ] E) := by
  let V' := Unitary.linearIsometryEquiv.symm V
  have hVtrans : (V : E →L[ℂ] E) * K.starProjection * star (V : E →L[ℂ] E) =
      K.starProjection := (commute_unitary_iff_star_right_conjugate V'.property).mp hV
  have hVmap : K.map V.toLinearMap = K := by
    have h := (SchattenPhaseTransition.map_eq_iff_conjugate_starProjection_complex K K V').mpr hVtrans
    simpa only [V', MulEquiv.apply_symm_apply] using h
  have hsets : {W : E →L[ℂ] E | W ∈ unitary (E →L[ℂ] E) ∧
      W * K.starProjection * star W = K.starProjection} =
      {W | W ∈ unitary (E →L[ℂ] E) ∧ Commute W K.starProjection} := by
    ext W
    constructor
    · rintro ⟨hW, ht⟩
      exact ⟨hW, (commute_unitary_iff_star_right_conjugate hW).mpr ht⟩
    · rintro ⟨hW, hc⟩
      exact ⟨hW, (commute_unitary_iff_star_right_conjugate hW).mp hc⟩
  have hlocal : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedOperatorDistance tau A.toLinearMap W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = K.starProjection}
      (V : E →L[ℂ] E) := by rw [hsets]; exact hmin
  have hglobal := isMinOn_correction_of_isLocalMinOn_preserving_subspace_complex
    tau htau K A V hVmap hlocal
  rwa [hsets] at hglobal

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
