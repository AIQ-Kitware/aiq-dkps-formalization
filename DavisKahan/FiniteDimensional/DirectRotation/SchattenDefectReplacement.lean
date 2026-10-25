/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenRightDefect
import DavisKahan.FiniteDimensional.DirectRotation.SchattenLocalGlobal
import DavisKahan.FiniteDimensional.DirectRotation.KernelTransportReplacement

/-!
# Independent and arbitrary Schatten defect parameters

Every unitary identification of the crossed defects, paired with its
inverse, occurs in a global Schatten optimizer with any given local
optimizer's entire positive-cosine action. The resulting ambient unitary
is unique for those prescribed actions. No multiplicity, angle gap or
prescribed block extension is assumed.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every prescribed crossed-defect isometry determines exactly one
global Schatten optimizer with a given local optimizer's action on the
whole complementary space. Its exact principal-angle value and comparison
with all ambient competitors are conclusions. -/
theorem exists_unique_schatten_minimizer_prescribing_defects_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    ∃! W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
      (∀ x : halmosSourceDefect K L, W x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, W y = (D.symm y : E)) ∧
      (∀ x ∈ (Proposition35.section3CosAngleOperator K L).kerᗮ,
        W x = (U : E →L[ℂ] E) x) ∧
      UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal =
        (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i)) ∧
      ∀ A : E ≃ₗᵢ[ℂ] E, K.map A.toLinearMap = L →
        UnitarilyInvariantSeminorm.schatten ℂ E E p
            (LinearMap.id - W.toLinearMap) ^ p.toReal ≤
          UnitarilyInvariantSeminorm.schatten ℂ E E p
            (LinearMap.id - A.toLinearMap) ^ p.toReal := by
  let T := Unitary.linearIsometryEquiv U
  let C := Proposition35.section3CosAngleOperator K L
  let N := C.ker
  have hTU : (T : E →L[ℂ] E) = (U : E →L[ℂ] E) :=
    Unitary.coe_linearIsometryEquiv_apply U
  have hTC : Commute (T : E →L[ℂ] E) C := by
    rw [hTU]
    exact Proposition35.commute_section3CosAngleOperator_of_commute_sinAngleOperator
      K L (U : E →L[ℂ] E)
      (commute_sinAngleOperator_of_isLocalMinOn_transports_complex p hp hp1 hp2 K L U hmap hmin)
  have hTself (x : E) (hx : C x = 0) : T x = star (T : E →L[ℂ] E) x := by
    rw [hTU]
    exact selfAdjoint_on_right_defect_of_isLocalMinOn_transports_complex
      p hp hp1 hp2 K L U hmap hmin x hx
  obtain ⟨W, hW, hWC, hWself, hWsource, hWtarget, hagree⟩ :=
    exists_transport_prescribing_defects K L T hmap hTC D
  have hWcost := schatten_transport_cost_eq_of_eq_on_cosine_kernel_orthogonal
    p hp K L W T hW hmap hWC hTC hWself hTself hagree
  have hTcost := schatten_transport_cost_eq_sum_of_isLocalMinOn_complex
    p hp hp1 hp2 K L U hmap hmin
  have hTlin : T.toLinearMap = (U : E →L[ℂ] E).toLinearMap := by ext x; rfl
  rw [hTlin] at hWcost
  have hatt := hWcost.trans hTcost
  have hWagree (x : E) (hx : x ∈ Nᗮ) : W x = (U : E →L[ℂ] E) x := hagree x hx
  refine ⟨W, ⟨hW, hWsource, hWtarget, hWagree, hatt, ?_⟩, ?_⟩
  · intro A hA
    rw [hatt]
    exact sum_phaseMinimum_le_schatten_transport_complex p hp hp1 hp2 K L
      (Unitary.linearIsometryEquiv.symm A)
      (by simpa only [MulEquiv.apply_symm_apply] using hA)
  · rintro A ⟨_, hAsource, hAtarget, hAagree, _, _⟩
    have hker (x : E) (hx : x ∈ N) : A x = W x := by
      change x ∈ (Proposition35.section3CosAngleOperator K L).ker at hx
      rw [Proposition35.ker_section3CosAngleOperator_eq_crossedDefectSum] at hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add, map_add, hAsource ⟨u, hu⟩, hWsource ⟨u, hu⟩,
        hAtarget ⟨v, hv⟩, hWtarget ⟨v, hv⟩]
    ext x
    rw [← N.starProjection_add_starProjection_orthogonal x, map_add, map_add,
      hker _ (N.starProjection_apply_mem x), hAagree _ (Nᗮ.starProjection_apply_mem x),
      hWagree _ (Nᗮ.starProjection_apply_mem x)]

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
