/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenCanonicalCommutation
import ForTauCeti.Analysis.InnerProductSpace.Projection.PairedPhaseTrace

/-!
# Canonical uniqueness through the Schatten phase transition

Every local minimum equals canonical rotation when all accepted principal
angles are at most the critical angle. The complete paired decomposition
transfers this bound to every actual paired mean. Its optimal scalar
phase therefore vanishes, including at equality. Both maps fix the
gradient kernel. No simplicity, positive-angle or prescribed-block
assumption is needed.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Below and at the critical angle, every ambient local minimum is
exactly the canonical rotation. Repeated, zero and critical angles and
empty subspaces are included. -/
theorem eq_canonicalRotation_of_isLocalMinOn_angles_le_critical_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (hcrit : ∀ i : Fin (Module.finrank ℂ K),
      K.principalAngles L i ≤ criticalAngle p.toReal)
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    (U : E →L[ℂ] E) = nonacuteDirectRotation K L D := by
  classical
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
  let Z := G.toLinearMap.ker
  let R := nonacuteDirectRotation K L D
  have hc := criticalAngle_mem p.toReal hp1 hp2
  have hacute (i : ℕ) : K.principalAngles L i < Real.pi / 2 := by
    by_cases hi : i < Module.finrank ℂ K
    · exact (hcrit ⟨i, hi⟩).trans_lt hc.2
    · rw [K.principalAngles_of_finrank_le L (Nat.le_of_not_gt hi)]
      linarith [Real.pi_pos]
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  have hG : IsSelfAdjoint G := isSelfAdjoint_schattenUnitaryGradient _ _
  obtain ⟨hPK, hPL⟩ := gradient_square_reduces_projections_of_isLocalMinOn_transports
    p hp hp1 K L.starProjection U ht hmin
  have hK : ∀ x ∈ Z, K.starProjection x ∈ Z :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute K.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPK.eq)
  have hL : ∀ x ∈ Z, L.starProjection x ∈ Z :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute L.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPL.eq)
  obtain ⟨n, e, theta, eps, hθ, _, hu, hw, hR0, hR1, _, _, _, _⟩ :=
    positive_gradient_canonical_relative_phase_basis_of_isLocalMinOn_complex
      p hp hp1 hp2 K L U hmap hmin D
  obtain ⟨_, _, _, _, _, _, _, d, _, _, _, _, hd, _, _, _, _, _, _⟩ :=
    schatten_transport_spectral_decomposition_of_isLocalMinOn_complex p hp hp1 hp2
      K L.starProjection U ht hmin
  let alpha := fun i => theta i + eps i * optimalPhase p.toReal (theta i)
  let beta := fun i => theta i - eps i * optimalPhase p.toReal (theta i)
  have hmean (i) : (alpha i + beta i) / 2 = theta i := by dsimp [alpha, beta]; ring
  have hw' (i) : (Unitary.linearIsometryEquiv U) (K.reflection (e i)) =
      Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i) := by
    have hneg : -beta i = -theta i + eps i * optimalPhase p.toReal (theta i) := by
      dsimp [beta]
      ring
    rw [hneg]
    exact hw i
  have hbound := Submodule.paired_phase_mean_le_of_principalAngles_le_complex
    K L H Z (Unitary.linearIsometryEquiv U) hmap e alpha beta hu hw'
    (fun i => by rw [hmean]; exact ⟨(hθ i).1.le, (hθ i).2.le⟩)
    d hd hK hL (criticalAngle p.toReal) hc.1.le hcrit
  have hzero (i) : optimalPhase p.toReal (theta i) = 0 :=
    (optimalPhase_eq_zero_iff_le_criticalAngle p.toReal (theta i) hp1 hp2
      (hθ i).1 (hθ i).2).mpr (by simpa only [hmean] using hbound i)
  have hH : (U : E →L[ℂ] E).toLinearMap ∘ₗ H.subtype = R.toLinearMap ∘ₗ H.subtype := by
    apply e.toBasis.ext
    intro i
    change (U : E →L[ℂ] E) (e i : E) = R (e i : E)
    rw [hu, hR0, hzero, mul_zero, add_zero]
  have hJH : (U : E →L[ℂ] E).toLinearMap ∘ₗ K.reflection.toLinearMap ∘ₗ H.subtype =
      R.toLinearMap ∘ₗ K.reflection.toLinearMap ∘ₗ H.subtype := by
    apply e.toBasis.ext
    intro i
    change (U : E →L[ℂ] E) (K.reflection (e i)) = R (K.reflection (e i))
    rw [hw, hR1, hzero, mul_zero, add_zero]
  have hfix := optimizer_and_canonical_fix_gradient_kernel_of_isLocalMinOn_acute_transports_complex
    p hp hp1 hp2 K L U hmap hmin hacute D
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := d.surjective x
  rw [hd, map_add, map_add, map_add, map_add]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (LinearMap.congr_fun hH y.fst.fst)
      (LinearMap.congr_fun hJH y.fst.snd))
    ((hfix y.snd y.snd.property).1.trans (hfix y.snd y.snd.property).2.symm)

/-- Every feasible transporter is minimizing exactly when it equals
canonical rotation, provided all angles obey the closed critical bound. -/
theorem isMinOn_transports_iff_eq_canonicalRotation_of_angles_le_critical_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hcrit : ∀ i : Fin (Module.finrank ℂ K),
      K.principalAngles L i ≤ criticalAngle p.toReal)
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    IsMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E) ↔ (U : E →L[ℂ] E) = nonacuteDirectRotation K L D := by
  constructor
  · intro hmin
    exact eq_canonicalRotation_of_isLocalMinOn_angles_le_critical_complex
      p hp hp1 hp2 K L U hmap hmin.isLocalMinOn hcrit D
  · intro heq
    obtain ⟨V, hV, hVmin⟩ := exists_schatten_transport_minimizer p hp
      K.starProjection L.starProjection U
      ((map_eq_iff_conjugate_starProjection_complex K L U).mp hmap)
    have hVeq := eq_canonicalRotation_of_isLocalMinOn_angles_le_critical_complex
      p hp hp1 hp2 K L V ((map_eq_iff_conjugate_starProjection_complex K L V).mpr hV)
      hVmin.isLocalMinOn hcrit D
    rw [heq.trans hVeq.symm]
    exact hVmin

/-- The closed critical-angle regime has exactly one global minimizer
among all ambient complex unitary transports. -/
theorem existsUnique_schatten_minimizer_of_angles_le_critical_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (hcrit : ∀ i : Fin (Module.finrank ℂ K),
      K.principalAngles L i ≤ criticalAngle p.toReal) :
    ∃! U : unitary (E →L[ℂ] E),
      K.map (Unitary.linearIsometryEquiv U).toLinearMap = L ∧
      IsMinOn
        (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
        {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
        (U : E →L[ℂ] E) := by
  obtain ⟨W, hWmap, _⟩ := exists_unitary_attaining_schatten_principalAngles_complex
    p hp K L hKL
  let W' := Unitary.linearIsometryEquiv.symm W
  have hW'map : K.map (Unitary.linearIsometryEquiv W').toLinearMap = L := by
    simpa only [W', MulEquiv.apply_symm_apply] using hWmap
  obtain ⟨U, hU, hmin⟩ := exists_schatten_transport_minimizer p hp
    K.starProjection L.starProjection W'
    ((map_eq_iff_conjugate_starProjection_complex K L W').mp hW'map)
  have hmap := (map_eq_iff_conjugate_starProjection_complex K L U).mpr hU
  let D := finiteCrossedDefectEquiv K L hKL
  have hUeq := eq_canonicalRotation_of_isLocalMinOn_angles_le_critical_complex
    p hp hp1 hp2 K L U hmap hmin.isLocalMinOn hcrit D
  refine ⟨U, ⟨hmap, hmin⟩, ?_⟩
  intro V hV
  apply Subtype.ext
  exact (eq_canonicalRotation_of_isLocalMinOn_angles_le_critical_complex
    p hp hp1 hp2 K L V hV.1 hV.2.isLocalMinOn hcrit D).trans hUeq.symm

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
