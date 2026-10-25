/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenLocalGlobal

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
  let T := A.symm.trans V
  let U := Unitary.linearIsometryEquiv.symm T
  let f := fun W : E →L[ℂ] E => W * (A : E →L[ℂ] E)
  have hTA : T.toLinearMap ∘ₗ A.toLinearMap = V.toLinearMap := by
    ext x
    exact congrArg V (A.symm_apply_apply x)
  have hTmap : L.map T.toLinearMap = K := by
    change (K.map A.toLinearMap).map T.toLinearMap = K
    rw [← Submodule.map_comp, hTA, hV]
  have hUmap : L.map (Unitary.linearIsometryEquiv U).toLinearMap = K := by
    simpa only [U, MulEquiv.apply_symm_apply] using hTmap
  have hTtrans : (T : E →L[ℂ] E) * L.starProjection * star (T : E →L[ℂ] E) =
      K.starProjection := (map_eq_iff_conjugate_starProjection_complex L K U).mp hUmap
  have hAmap : K.map (Unitary.linearIsometryEquiv
      (Unitary.linearIsometryEquiv.symm A)).toLinearMap = L := by
    simpa only [MulEquiv.apply_symm_apply] using (show K.map A.toLinearMap = L from rfl)
  have hAtrans : (A : E →L[ℂ] E) * K.starProjection * star (A : E →L[ℂ] E) =
      L.starProjection := (map_eq_iff_conjugate_starProjection_complex K L
        (Unitary.linearIsometryEquiv.symm A)).mp hAmap
  have hconj (W : E →L[ℂ] E) :
      f W * K.starProjection * star (f W) = W * L.starProjection * star W := by
    dsimp only [f]
    rw [star_mul, ← hAtrans]
    simp only [mul_assoc]
  have hcost (W : E →L[ℂ] E) :
      UnitarilyInvariantSeminorm.schatten ℂ E E p (A.toLinearMap - (f W).toLinearMap) ^ p.toReal =
        UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal := by
    have hfactor : A.toLinearMap - (f W).toLinearMap =
        (LinearMap.id - W.toLinearMap) ∘ₗ A.toLinearMap := by ext x; rfl
    rw [hfactor]
    exact congrArg (fun t : ℝ => t ^ p.toReal)
      ((UnitarilyInvariantSeminorm.schatten ℂ E E p).map_comp_linearIsometryEquiv A
        (LinearMap.id - W.toLinearMap))
  have hfeasible (W : E →L[ℂ] E)
      (hW : W ∈ unitary (E →L[ℂ] E) ∧ W * L.starProjection * star W = K.starProjection) :
      f W ∈ unitary (E →L[ℂ] E) ∧
        f W * K.starProjection * star (f W) = K.starProjection :=
    ⟨mul_mem hW.1 (Unitary.linearIsometryEquiv.symm A).property, (hconj W).trans hW.2⟩
  have hfT : f (T : E →L[ℂ] E) = (V : E →L[ℂ] E) := by
    ext x
    exact congrArg V (A.symm_apply_apply x)
  have hmin' : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (A.toLinearMap - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = K.starProjection}
      (f (T : E →L[ℂ] E)) := by rw [hfT]; exact hmin
  have hlocal := hmin'.comp_continuousOn (g := f)
    (s := {W | W ∈ unitary (E →L[ℂ] E) ∧ W * L.starProjection * star W = K.starProjection})
    (fun W hW => hfeasible W hW) (continuous_id.mul_const (A : E →L[ℂ] E)).continuousOn
    ⟨U.property, hTtrans⟩
  have hlocalT : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * L.starProjection * star W = K.starProjection}
      (T : E →L[ℂ] E) := by
    change ∀ᶠ W in 𝓝[{W | W ∈ unitary (E →L[ℂ] E) ∧
      W * L.starProjection * star W = K.starProjection}] (T : E →L[ℂ] E), _ ≤ _ at hlocal ⊢
    filter_upwards [hlocal] with W hW
    simpa only [Function.comp_apply, hcost] using hW
  have hglobal := isMinOn_of_isLocalMinOn_transports_complex p hp hp1 hp2 L K U hUmap hlocalT
  intro S hS
  let B := S * (A.symm : E →L[ℂ] E)
  have hBunit : B ∈ unitary (E →L[ℂ] E) :=
    mul_mem hS.1 (Unitary.linearIsometryEquiv.symm A.symm).property
  have hfB : f B = S := by
    ext x
    exact congrArg S (A.symm_apply_apply x)
  have hBtrans : B * L.starProjection * star B = K.starProjection := by
    rw [← hconj, hfB]
    exact hS.2
  have hg := hglobal ⟨hBunit, hBtrans⟩
  change UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - (T : E →L[ℂ] E).toLinearMap) ^ p.toReal ≤
    UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - B.toLinearMap) ^ p.toReal at hg
  rw [← hcost (T : E →L[ℂ] E), ← hcost B, hfT, hfB] at hg
  exact hg

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
