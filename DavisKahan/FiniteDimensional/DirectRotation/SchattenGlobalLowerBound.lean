/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenSpectralDecomposition
import DavisKahan.FiniteDimensional.DirectRotation.SchattenTransportExistence
import ForTauCeti.Analysis.InnerProductSpace.Projection.PairedPhaseTrace

/-!
# The unrestricted complex Schatten transport lower bound

The spectral decomposition of a local minimum consists of scalar-optimal
reflection pairs and a self-adjoint kernel restriction. The paired phase
trace identity identifies their means with the actual principal angles.
The kernel reflection bound then gives the principal-angle lower bound.
Compact attainment transfers it to every admissible unitary transport.
No block structure is assumed of the competing transporter.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
private theorem ker_invariant_of_commute_square
    (G P : E →L[ℂ] E) (hG : IsSelfAdjoint G) (hP : Commute P (G * G)) :
    ∀ x ∈ G.toLinearMap.ker, P x ∈ G.toLinearMap.ker := by
  intro x hx
  change G x = 0 at hx
  change G (P x) = 0
  have h := congrArg (fun T : E →L[ℂ] E => T x) hP.eq
  change P (G (G x)) = G (G (P x)) at h
  rw [hx, map_zero, map_zero] at h
  have hi := hG.isSymmetric (P x) (G (P x))
  change inner ℂ (G (P x)) (G (P x)) = inner ℂ (P x) (G (G (P x))) at hi
  rw [← h, inner_zero_right] at hi
  exact inner_self_eq_zero.mp hi

/-- The subspace and projection formulations of a complex unitary
transport agree. -/
theorem map_eq_iff_conjugate_starProjection
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E)) :
    K.map (Unitary.linearIsometryEquiv U).toLinearMap = L ↔
      (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = L.starProjection := by
  let u := Unitary.linearIsometryEquiv U
  have hs : star (U : E →L[ℂ] E) = (u.symm : E →L[ℂ] E) := u.adjoint_eq_symm
  have hp : (K.map u.toLinearMap).starProjection =
      (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) := by
    ext x
    rw [Submodule.starProjection_map_apply, hs]
    rfl
  constructor
  · intro h
    exact hp.symm.trans (congrArg (fun S : Submodule ℂ E => S.starProjection) h)
  · intro h
    have heq := hp.trans h
    rw [← Submodule.range_starProjection (K.map u.toLinearMap),
      ← Submodule.range_starProjection L, heq]

set_option maxHeartbeats 800000 in
-- Combining the spectral normal form with two angle traces requires the
-- larger elaboration allowance already used by the normal-form theorem.
/-- Every local constrained minimum dominates the exact scalar cost sum
of the original source and target principal angles. -/
theorem sum_phaseMinimum_le_of_isLocalMinOn_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i)) ≤
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - (U : E →L[ℂ] E).toLinearMap) ^ p.toReal := by
  classical
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
  let Z := G.toLinearMap.ker
  have ht := (map_eq_iff_conjugate_starProjection K L U).mp hmap
  obtain ⟨n, e, alpha, beta, V, W, R, d, hV, hW, hR, _, hd, _, hVe, hWe,
      hmean, hcost⟩ := schatten_transport_spectral_decomposition_of_isLocalMinOn
        p hp hp1 hp2 K L.starProjection U ht hmin
  have hG : IsSelfAdjoint G := isSelfAdjoint_schattenUnitaryGradient _ _
  obtain ⟨hPK, hPL⟩ := gradient_square_reduces_projections_of_isLocalMinOn_transports
    p hp hp1 K L.starProjection U ht hmin
  have hK : ∀ x ∈ Z, K.starProjection x ∈ Z :=
    ker_invariant_of_commute_square G K.starProjection hG hPK
  have hL : ∀ x ∈ Z, L.starProjection x ∈ Z :=
    ker_invariant_of_commute_square G L.starProjection hG hPL
  have hu (i) : (Unitary.linearIsometryEquiv U) (e i : E) =
      Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E) := by
    change (U : E →L[ℂ] E) (e i : E) = _
    rw [← hV, hVe]
    rfl
  have hw (i) : (Unitary.linearIsometryEquiv U) (K.reflection (e i)) =
      Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i) := by
    change (U : E →L[ℂ] E) (K.reflection (e i)) = _
    rw [← hW, hWe, Submodule.coe_smul, map_smul]
  have hangles := Submodule.sum_principalAngles_eq_paired_phases_add_comap
    K L H Z (Unitary.linearIsometryEquiv U) hmap e alpha beta hu hw
    (fun i => ⟨(hmean i).1.le, (hmean i).2.le⟩) d hd hK hL
    (phaseMinimum p.toReal) (phaseMinimum_zero_angle p.toReal hp1.le)
  obtain ⟨R', hR', _, _, hbound⟩ := gradient_kernel_principalAngle_lower_bound p hp K L U hmap
  have heq : R' = R := by
    ext z
    exact (hR' z).trans (hR z).symm
  rw [heq] at hbound
  rw [hangles, hcost]
  exact add_le_add le_rfl hbound

/-- The exact scalar principal-angle sum is a lower bound for every
complex unitary transport, without a restriction to principal planes. -/
theorem sum_phaseMinimum_le_schatten_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L) :
    (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i)) ≤
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - (U : E →L[ℂ] E).toLinearMap) ^ p.toReal := by
  have ht := (map_eq_iff_conjugate_starProjection K L U).mp hmap
  obtain ⟨V, hV, hmin⟩ := exists_schatten_transport_minimizer p hp K.starProjection L.starProjection U ht
  have hmapV := (map_eq_iff_conjugate_starProjection K L V).mpr hV
  exact (sum_phaseMinimum_le_of_isLocalMinOn_transports p hp hp1 hp2 K L V hmapV
    hmin.isLocalMinOn).trans (hmin ⟨U.property, ht⟩)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
