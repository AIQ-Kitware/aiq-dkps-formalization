/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalAttainment

/-!
# Rigidity of the exceptional block of every Schatten optimizer

At a local transport minimum the cost deficit is entirely in the gradient
kernel. At a global minimum that restriction must itself attain the scalar
principal-angle value. A reflecting transporter with an interior principal
angle has a strict deficit, so the optimal kernel has only zero and right
angles. For an acute ambient pair its entire kernel restriction is the
identity. These assertions concern the actual ambient optimizer; no model
or supplied block decomposition is assumed.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every global minimizer restricts on its actual gradient kernel to
an attaining reflecting transport, with only zero and right angles. -/
theorem gradient_kernel_optimal_of_isMinOn_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    let Z := (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.ker
    let K₀ := K.comap Z.subtype
    let L₀ := L.comap Z.subtype
    ∃ R : Z ≃ₗᵢ[ℂ] Z,
      (∀ z : Z, (R z : E) = (U : E →L[ℂ] E) z) ∧
      IsSelfAdjoint (R : Z →L[ℂ] Z) ∧ K₀.map R.toLinearMap = L₀ ∧
      UnitarilyInvariantSeminorm.schatten ℂ Z Z p
          (LinearMap.id - R.toLinearMap) ^ p.toReal =
        (∑ j : Fin (Module.finrank ℂ K₀), phaseMinimum p.toReal (K₀.principalAngles L₀ j)) ∧
      ∀ j : Fin (Module.finrank ℂ K₀),
        K₀.principalAngles L₀ j = 0 ∨ K₀.principalAngles L₀ j = Real.pi / 2 := by
  have hKL : Module.finrank ℂ K = Module.finrank ℂ L := by
    rw [← hmap]
    exact ((Unitary.linearIsometryEquiv U).toLinearEquiv.finrank_map_eq K).symm
  obtain ⟨W, hWmap, hWcost⟩ := exists_unitary_attaining_schatten_principalAngles_complex p hp K L hKL
  let W' := Unitary.linearIsometryEquiv.symm W
  have hW'map : K.map (Unitary.linearIsometryEquiv W').toLinearMap = L := by
    simpa only [W', MulEquiv.apply_symm_apply] using hWmap
  have hupper := hmin ⟨W'.property, (map_eq_iff_conjugate_starProjection_complex K L W').mp hW'map⟩
  change UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - (U : E →L[ℂ] E).toLinearMap) ^ p.toReal ≤
    UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - W.toLinearMap) ^ p.toReal at hupper
  rw [hWcost] at hupper
  have hatt := le_antisymm hupper
    (sum_phaseMinimum_le_schatten_transport_complex p hp hp1 hp2 K L U hmap)
  obtain ⟨R, hR, hself, hmapR, hdefect⟩ :=
    gradient_kernel_cost_defect_of_isLocalMinOn_transports_complex
      p hp hp1 hp2 K L U hmap hmin.isLocalMinOn
  rw [hatt, sub_self] at hdefect
  have hcost := sub_eq_zero.mp hdefect.symm
  exact ⟨R, hR, hself, hmapR, hcost,
    principalAngles_eq_zero_or_right_of_selfAdjoint_attains_complex
      p hp hp1 _ _ R hself hmapR hcost⟩

/-- For an acute pair every global minimizing transporter fixes its
whole zero-gradient space pointwise. This removes the exceptional block
from the classification without a second derivative at eigenvalue one. -/
theorem apply_eq_self_on_gradient_kernel_of_isMinOn_acute_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (hacute : ∀ i : ℕ, K.principalAngles L i < Real.pi / 2) :
    ∀ x : E, schattenUnitaryGradient p.toReal (U : E →L[ℂ] E) x = 0 →
      (U : E →L[ℂ] E) x = x := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let Z := G.toLinearMap.ker
  obtain ⟨R, hR, hself, hmapR, hcost, _⟩ :=
    gradient_kernel_optimal_of_isMinOn_transports_complex p hp hp1 hp2 K L U hmap hmin
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  have hcomm := (gradient_square_reduces_projections_of_isLocalMinOn_transports
    p hp hp1 K L.starProjection U ht hmin.isLocalMinOn).2
  have hL : ∀ x ∈ Z, L.starProjection x ∈ Z := by
    have hG := (isSelfAdjoint_schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).isSymmetric
    exact hG.mapsTo_ker_of_commute_square
      (show Commute L.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hcomm.eq)
  have hacute := Submodule.principalAngles_comap_lt_pi_div_two_of_invariant K L Z hL hacute
  have hRid := selfAdjoint_attaining_eq_refl_of_acute_complex p hp hp1
    (K.comap Z.subtype) (L.comap Z.subtype) R hself hmapR hcost (fun i => hacute i)
  intro x hx
  let z : Z := ⟨x, hx⟩
  have h := hR z
  rw [hRid] at h
  exact h.symm

/-- A constrained local minimum whose zero-gradient space is fixed
pointwise is already a global minimum. Only the exceptional reflecting
kernel can obstruct the local-to-global conclusion. -/
theorem isMinOn_of_isLocalMinOn_transports_of_gradient_kernel_fixed_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (hfixed : ∀ x : E, schattenUnitaryGradient p.toReal (U : E →L[ℂ] E) x = 0 →
      (U : E →L[ℂ] E) x = x) :
    IsMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E) := by
  classical
  let Z := (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.ker
  obtain ⟨R, hR, _, hmapR, hdefect⟩ :=
    gradient_kernel_cost_defect_of_isLocalMinOn_transports_complex p hp hp1 hp2 K L U hmap hmin
  have hRid : R = LinearIsometryEquiv.refl ℂ Z := by
    ext z
    exact (hR z).trans (hfixed z z.property)
  have hRlin : R.toLinearMap = (LinearMap.id : Z →ₗ[ℂ] Z) := by rw [hRid]; rfl
  have hKL₀ : K.comap Z.subtype = L.comap Z.subtype := by
    simpa only [hRlin, Submodule.map_id] using hmapR
  have hcostR : UnitarilyInvariantSeminorm.schatten ℂ Z Z p
      (LinearMap.id - R.toLinearMap) ^ p.toReal = 0 := by
    simp only [hRlin, sub_self, map_zero,
      Real.zero_rpow (by linarith : p.toReal ≠ 0)]
  have hsumR : (∑ j : Fin (Module.finrank ℂ (K.comap Z.subtype)),
      phaseMinimum p.toReal
        ((K.comap Z.subtype).principalAngles (L.comap Z.subtype) j)) = 0 := by
    have hangle : (K.comap Z.subtype).principalAngles (L.comap Z.subtype) = 0 := by
      simpa only [← hKL₀] using (K.comap Z.subtype).principalAngles_self
    simp only [hangle, Finsupp.zero_apply,
      phaseMinimum_zero_angle p.toReal hp1.le, Finset.sum_const_zero]
  rw [hcostR, hsumR, sub_self] at hdefect
  have hatt := sub_eq_zero.mp hdefect
  intro W hW
  let V : unitary (E →L[ℂ] E) := ⟨W, hW.1⟩
  have hVmap := (map_eq_iff_conjugate_starProjection_complex K L V).mpr hW.2
  change UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - (U : E →L[ℂ] E).toLinearMap) ^ p.toReal ≤
    UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - W.toLinearMap) ^ p.toReal
  rw [hatt]
  exact sum_phaseMinimum_le_schatten_transport_complex p hp hp1 hp2 K L V hVmap

/-- Every constrained local minimum with no eigenvalue `-1` is global.
The assertion allows zero displacement singular values; it excludes only
the opposite endpoint of the unitary spectrum. -/
theorem isMinOn_of_isLocalMinOn_transports_of_no_neg_one_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (hno : ∀ x : E, (U : E →L[ℂ] E) x = -x → x = 0) :
    IsMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E) := by
  apply isMinOn_of_isLocalMinOn_transports_of_gradient_kernel_fixed_complex
    p hp hp1 hp2 K L U hmap hmin
  let Z := (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.ker
  obtain ⟨R, hR, hself, _, _⟩ :=
    gradient_kernel_cost_defect_of_isLocalMinOn_transports_complex p hp hp1 hp2 K L U hmap hmin
  have hRR (z : Z) : R (R z) = z := by
    have h := congrArg (fun T : Z →L[ℂ] Z => T z)
      (Unitary.coe_star_mul_self (Unitary.linearIsometryEquiv.symm R))
    change (star (R : Z →L[ℂ] Z)) (R z) = z at h
    rwa [hself.star_eq] at h
  intro x hx
  let z : Z := ⟨x, hx⟩
  have hv : (U : E →L[ℂ] E) ((z : E) - (R z : E)) = -((z : E) - (R z : E)) := by
    rw [map_sub, ← hR, ← hR, hRR]
    abel
  have hz := sub_eq_zero.mp (hno _ hv)
  exact (hR z).symm.trans hz.symm

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
