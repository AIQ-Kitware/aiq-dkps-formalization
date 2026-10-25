/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenReflectingPlanes
import ForTauCeti.Analysis.InnerProductSpace.UnitaryTransportFrobenius

/-!
# Every complex Schatten transport local minimum is global

The actual gradient kernel has a complete fixed/right block family.
Its source-diagonal compression is therefore positive. The Frobenius
trace certificate and sharp bounded Schatten comparison prove global
optimality of that kernel reflection without reindexing its angle list.
The existing cost-deficit identity then closes unrestricted local-to-global
optimality for `1<p<2`, including every exceptional spectral block.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every constrained local minimum attains the exact unrestricted
principal-angle sum. No spectral endpoint, angle, rank or mixing
restriction is imposed on the ambient unitary transporter. -/
theorem schatten_transport_cost_eq_sum_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - (U : E →L[ℂ] E).toLinearMap) ^ p.toReal =
        ∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i) := by
  let Z := (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.ker
  let K₀ := K.comap Z.subtype
  let L₀ := L.comap Z.subtype
  obtain ⟨R, hR, hself, hmapR, hdefect⟩ :=
    gradient_kernel_cost_defect_of_isLocalMinOn_transports_complex
      p hp hp1 hp2 K L U hmap hmin
  change K₀.map R.toLinearMap = L₀ at hmapR
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  obtain ⟨R₀, hR₀, F, hF, _, hspan⟩ :=
    gradient_kernel_fixed_or_right_blocks_of_isLocalMinOn_transports_complex
      p hp hp1 K L.starProjection U ht hmin
  have hRR : R₀ = R := by
    apply LinearIsometryEquiv.ext
    intro z
    apply Subtype.ext
    exact (hR₀ z).trans (hR z).symm
  rw [hRR] at hF
  have hblocks : ∀ N ∈ F, (∀ z ∈ N, K₀.starProjection z ∈ N) ∧
      (∀ z ∈ N, R z ∈ N) ∧
      ((∀ z ∈ N, R z = z) ∨ (∀ z ∈ N, R (K₀.starProjection (R z)) = z - K₀.starProjection z)) := by
    intro N hNF
    obtain ⟨_, _, hPN, hRN, hcase⟩ := hF N hNF
    exact ⟨hPN, hRN, hcase.imp id (fun h => h.2)⟩
  have hKL₀ : Module.finrank ℂ K₀ = Module.finrank ℂ L₀ := by
    rw [← hmapR]
    exact (R.toLinearEquiv.finrank_map_eq K₀).symm
  obtain ⟨W, hWmap, hWcost⟩ := exists_unitary_attaining_schatten_principalAngles_complex
    p hp K₀ L₀ hKL₀
  let R' := Unitary.linearIsometryEquiv.symm R
  let W' := Unitary.linearIsometryEquiv.symm W
  have hR'map : K₀.map (Unitary.linearIsometryEquiv R').toLinearMap = L₀ := by
    simpa only [R', MulEquiv.apply_symm_apply] using hmapR
  have hW'map : K₀.map (Unitary.linearIsometryEquiv W').toLinearMap = L₀ := by
    simpa only [W', MulEquiv.apply_symm_apply] using hWmap
  have hRtrans := (map_eq_iff_conjugate_starProjection_complex K₀ L₀ R').mp hR'map
  have hWtrans := (map_eq_iff_conjugate_starProjection_complex K₀ L₀ W').mp hW'map
  have htrans : (W : Z →L[ℂ] Z) * K₀.starProjection * star (W : Z →L[ℂ] Z) =
      (R : Z →L[ℂ] Z) * K₀.starProjection * star (R : Z →L[ℂ] Z) :=
    hWtrans.trans hRtrans.symm
  have hupper := schatten_transport_le_of_fixed_or_exchange_blocks
    K₀.starProjection isStarProjection_starProjection R W hself F hspan hblocks htrans p hp hp2.le
  rw [hWcost] at hupper
  have hlower := sum_phaseMinimum_le_schatten_transport_complex
    p hp hp1 hp2 K₀ L₀ R' hR'map
  have hcost : UnitarilyInvariantSeminorm.schatten ℂ Z Z p
      (LinearMap.id - R.toLinearMap) ^ p.toReal =
        ∑ i : Fin (Module.finrank ℂ K₀), phaseMinimum p.toReal (K₀.principalAngles L₀ i) :=
    le_antisymm hupper hlower
  rw [hcost, sub_self] at hdefect
  exact sub_eq_zero.mp hdefect

/-- Every constrained local minimum is a global minimum of the
unrestricted finite complex Schatten transport problem, for `1<p<2`.
Zero and right angles, repeated angles, fixed directions and arbitrary
ambient unitary competitors are included. -/
theorem isMinOn_of_isLocalMinOn_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    IsMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E) := by
  have hatt := schatten_transport_cost_eq_sum_of_isLocalMinOn_complex
    p hp hp1 hp2 K L U hmap hmin
  intro W hW
  let V : unitary (E →L[ℂ] E) := ⟨W, hW.1⟩
  have hVmap := (map_eq_iff_conjugate_starProjection_complex K L V).mpr hW.2
  change UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - (U : E →L[ℂ] E).toLinearMap) ^ p.toReal ≤
    UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - W.toLinearMap) ^ p.toReal
  rw [hatt]
  exact sum_phaseMinimum_le_schatten_transport_complex p hp hp1 hp2 K L V hVmap

/-- The no-spurious-minima theorem also holds for the Schatten norm
itself. Taking its positive power neither creates nor removes local
or global minimizers. -/
theorem isMinOn_schatten_of_isLocalMinOn_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap))
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    IsMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap))
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E) := by
  have hlocal : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E) := by
    filter_upwards [hmin] with W hW
    exact Real.rpow_le_rpow (apply_nonneg _ _) hW (by linarith)
  have hglobal := isMinOn_of_isLocalMinOn_transports_complex p hp hp1 hp2 K L U hmap hlocal
  intro W hW
  exact (Real.rpow_le_rpow_iff (apply_nonneg _ _) (apply_nonneg _ _) (by linarith)).mp
    (hglobal hW)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
