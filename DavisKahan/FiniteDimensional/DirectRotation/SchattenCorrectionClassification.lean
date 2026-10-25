/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenNonacuteClassification

/-!
# Every Schatten-nearest subspace-preserving unitary

The correction-to-transport bijection preserves the literal Schatten
distance. The full phase/defect classification therefore describes every
nearest unitary preserving a prescribed subspace. Candidate corrections
and all competing ambient unitaries are unrestricted within that constraint.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Literal Schatten correction minimality is equivalent to transport
power minimality under `V -> V*A.adjoint`, for every positive finite
Schatten exponent. No angle or candidate feasibility assumption is needed
for this comparison equivalence. -/
theorem schatten_correction_isMin_iff_transport_power_isMin_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hppos : 0 < p.toReal)
    (K : Submodule ℂ E) (A V : E ≃ₗᵢ[ℂ] E) :
    (∀ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = K →
      UnitarilyInvariantSeminorm.schatten ℂ E E p (A.toLinearMap - V.toLinearMap) ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p (A.toLinearMap - W.toLinearMap)) ↔
    (∀ S : E ≃ₗᵢ[ℂ] E, (K.map A.toLinearMap).map S.toLinearMap = K →
      UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - (A.symm.trans V).toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - S.toLinearMap) ^ p.toReal) := by
  let L := K.map A.toLinearMap
  let e : (E ≃ₗᵢ[ℂ] E) ≃ (E ≃ₗᵢ[ℂ] E) :=
    { toFun := fun W => A.symm.trans W
      invFun := fun S => A.trans S
      left_inv := by intro W; ext x; simp
      right_inv := by intro S; ext x; simp }
  have hmap (W : E ≃ₗᵢ[ℂ] E) : L.map (e W).toLinearMap = K.map W.toLinearMap := by
    change (K.map A.toLinearMap).map (A.symm.trans W).toLinearMap = _
    rw [← Submodule.map_comp]
    congr 1
    ext x
    exact congrArg W (A.symm_apply_apply x)
  have hcost (W : E ≃ₗᵢ[ℂ] E) :
      UnitarilyInvariantSeminorm.schatten ℂ E E p (A.toLinearMap - W.toLinearMap) ^ p.toReal =
        UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - (e W).toLinearMap) ^ p.toReal := by
    have hfac : A.toLinearMap - W.toLinearMap =
        (LinearMap.id - (e W).toLinearMap) ∘ₗ A.toLinearMap := by
      ext x
      change A x - W x = A x - W (A.symm (A x))
      rw [A.symm_apply_apply]
    rw [hfac]
    exact congrArg (fun t : ℝ => t ^ p.toReal)
      ((UnitarilyInvariantSeminorm.schatten ℂ E E p).map_comp_linearIsometryEquiv A _)
  constructor
  · intro h S hS
    obtain ⟨W, rfl⟩ := e.surjective S
    have hh := Real.rpow_le_rpow (apply_nonneg _ _)
      (h W ((hmap W).symm.trans hS)) hppos.le
    rw [hcost V, hcost W] at hh
    exact hh
  · intro h W hW
    have hh := h (e W) ((hmap W).trans hW)
    change UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - (e V).toLinearMap) ^ p.toReal ≤
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - (e W).toLinearMap) ^ p.toReal at hh
    rw [← hcost V, ← hcost W] at hh
    exact (Real.rpow_le_rpow_iff (apply_nonneg _ _) (apply_nonneg _ _) hppos).mp hh

/-- Every Schatten-nearest unitary preserving a prescribed subspace is
characterized by compatible phase and defect data for the image-to-source
transport. This is an iff for all ambient correction competitors. -/
theorem schatten_correction_isMin_iff_phase_and_defect_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) (A V : E ≃ₗᵢ[ℂ] E) (hV : K.map V.toLinearMap = K) :
    let L := K.map A.toLinearMap
    let hLK := A.toLinearEquiv.finrank_map_eq K
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation L K (finiteCrossedDefectEquiv L K hLK),
        nonacuteDirectRotation_mem_unitary L K (finiteCrossedDefectEquiv L K hLK)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator L K
    let F := schattenPhaseFactor p.toReal C
    let T := A.symm.trans V
    (∀ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = K →
      UnitarilyInvariantSeminorm.schatten ℂ E E p (A.toLinearMap - V.toLinearMap) ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p (A.toLinearMap - W.toLinearMap)) ↔
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
        (∀ x, P (L.reflection x) = L.reflection (P x)) ∧
        ∃ D : halmosSourceDefect L K ≃ₗᵢ[ℂ] halmosTargetDefect L K,
          (∀ x : halmosSourceDefect L K, T x = (D x : E)) ∧
          (∀ y : halmosTargetDefect L K, T y = (D.symm y : E)) ∧
          C * (T.trans R.symm : E →L[ℂ] E) = C * (F * P + star F * (1 - P)) := by
  let L := K.map A.toLinearMap
  let T := A.symm.trans V
  have hTA : T.toLinearMap ∘ₗ A.toLinearMap = V.toLinearMap := by
    ext x
    exact congrArg V (A.symm_apply_apply x)
  have hTmap : L.map T.toLinearMap = K := by
    change (K.map A.toLinearMap).map T.toLinearMap = K
    rw [← Submodule.map_comp, hTA, hV]
  exact (schatten_correction_isMin_iff_transport_power_isMin_complex p
    (zero_lt_one.trans hp1) K A V).trans
    (schatten_transport_isMin_iff_phase_and_defect_complex p hp hp1 hp2 L K
      (A.toLinearEquiv.finrank_map_eq K) T hTmap)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
