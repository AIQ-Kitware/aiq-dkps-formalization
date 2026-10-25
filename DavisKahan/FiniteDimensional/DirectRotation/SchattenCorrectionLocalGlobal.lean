/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenLocalGlobal
import ForTauCeti.Analysis.InnerProductSpace.UnitaryCorrectionLocalGlobal

/-!
# No nonglobal local minima for nearest subspace-preserving unitaries

Right multiplication by the input unitary identifies its correction
problem with the transport fiber from the image subspace back to the
prescribed subspace. The change is continuous, preserves the actual
Schatten cost, and covers every admissible competitor.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every local Schatten-nearest unitary preserving a prescribed
subspace is globally nearest, for `1<p<2`. The input unitary, subspace,
principal angles and all feasible ambient competitors are unrestricted. -/
theorem isMinOn_correction_of_isLocalMinOn_preserving_subspace_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) (A V : E ≃ₗᵢ[ℂ] E) (hV : K.map V.toLinearMap = K)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (A.toLinearMap - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = K.starProjection}
      (V : E →L[ℂ] E)) :
    IsMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (A.toLinearMap - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = K.starProjection}
      (V : E →L[ℂ] E) := by
  let L := K.map A.toLinearMap
  let A' := Unitary.linearIsometryEquiv.symm A
  let V' := Unitary.linearIsometryEquiv.symm V
  have hAmap : K.map (Unitary.linearIsometryEquiv A').toLinearMap = L := by
    simpa only [A', MulEquiv.apply_symm_apply] using (show K.map A.toLinearMap = L from rfl)
  have hVmap : K.map (Unitary.linearIsometryEquiv V').toLinearMap = K := by
    simpa only [V', MulEquiv.apply_symm_apply] using hV
  have hAtrans := (map_eq_iff_conjugate_starProjection_complex K L A').mp hAmap
  have hVtrans := (map_eq_iff_conjugate_starProjection_complex K K V').mp hVmap
  have hcost (W : E →L[ℂ] E) :
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (A.toLinearMap - (W * (A : E →L[ℂ] E)).toLinearMap) ^ p.toReal =
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal := by
    have hfactor : A.toLinearMap - (W * (A : E →L[ℂ] E)).toLinearMap =
        (LinearMap.id - W.toLinearMap) ∘ₗ A.toLinearMap := by ext x; rfl
    rw [hfactor]
    exact congrArg (fun t : ℝ => t ^ p.toReal)
      ((UnitarilyInvariantSeminorm.schatten ℂ E E p).map_comp_linearIsometryEquiv A
        (LinearMap.id - W.toLinearMap))
  exact isMinOn_unitary_correction_of_transport_local_global K.starProjection L.starProjection A' V'
    hAtrans hVtrans
    (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - W.toLinearMap) ^ p.toReal)
    (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
      (A.toLinearMap - W.toLinearMap) ^ p.toReal)
    hcost (fun T ht hlocal => isMinOn_of_isLocalMinOn_transports_complex p hp hp1 hp2 L K T
      ((map_eq_iff_conjugate_starProjection_complex L K T).mpr ht) hlocal) hmin

/-- Every local minimum of the actual Schatten correction norm is
global among all unitaries preserving the prescribed subspace. -/
theorem isMinOn_schatten_correction_of_isLocalMinOn_preserving_subspace_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) (A V : E ≃ₗᵢ[ℂ] E) (hV : K.map V.toLinearMap = K)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (A.toLinearMap - W.toLinearMap))
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = K.starProjection}
      (V : E →L[ℂ] E)) :
    IsMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (A.toLinearMap - W.toLinearMap))
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = K.starProjection}
      (V : E →L[ℂ] E) := by
  have hlocal : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (A.toLinearMap - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = K.starProjection}
      (V : E →L[ℂ] E) := by
    filter_upwards [hmin] with W hW
    exact Real.rpow_le_rpow (apply_nonneg _ _) hW (by linarith)
  have hglobal := isMinOn_correction_of_isLocalMinOn_preserving_subspace_complex
    p hp hp1 hp2 K A V hV hlocal
  intro W hW
  exact (Real.rpow_le_rpow_iff (apply_nonneg _ _) (apply_nonneg _ _) (by linarith)).mp
    (hglobal hW)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
