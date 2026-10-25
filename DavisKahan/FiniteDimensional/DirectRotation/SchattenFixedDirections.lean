/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimizerAngles
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenLocalGlobal
public import ForTauCeti.Analysis.InnerProductSpace.SchattenTransportRestriction

/-!
# Every Schatten optimizer fixes the zero-angle space

Angle preservation makes the kernel of the projection difference reducing
for every optimizer. Its two restricted projections coincide. The inherited
local transport minimum is therefore global with value zero, forcing the
restricted transporter to be identity. This includes common source vectors
and common orthogonal ambient directions, even for a nonacute pair.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every local minimizing transporter fixes every vector on which the
source and target projections agree. Zero and right angles elsewhere
and all angle multiplicities are unrestricted. -/
theorem apply_eq_self_of_projections_eq_of_isLocalMinOn_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (x : E) (hx : K.starProjection x = L.starProjection x) :
    (U : E →L[ℂ] E) x = x := by
  let S := K.sinAngleOperator L
  let N := S.toLinearMap.ker
  let T := Unitary.linearIsometryEquiv U
  have hPQ (z : N) : K.starProjection (z : E) = L.starProjection z := by
    have h := K.norm_sinAngleOperator_apply L (z : E)
    have hz : K.sinAngleOperator L (z : E) = 0 := z.property
    rw [hz, norm_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)
  have hPN : ∀ z ∈ N, K.starProjection z ∈ N := by
    intro z hz
    have h := congrArg (fun A : E →L[ℂ] E => A z)
      (K.commute_starProjection_sinAngleOperator L).eq
    change K.starProjection (S z) = S (K.starProjection z) at h
    change S (K.starProjection z) = 0
    rw [← h, show S z = 0 from hz, map_zero]
  have hTN : ∀ z ∈ N, T z ∈ N := by
    intro z hz
    have h := congrArg (fun A : E →L[ℂ] E => A z)
      (commute_sinAngleOperator_of_isLocalMinOn_transports_complex
        p hp hp1 hp2 K L U hmap hmin).eq
    change (U : E →L[ℂ] E) (S z) = S ((U : E →L[ℂ] E) z) at h
    change S ((U : E →L[ℂ] E) z) = 0
    rw [← h, show S z = 0 from hz, map_zero]
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  have hmin' : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W =
        (T : E →L[ℂ] E) * K.starProjection * star (T : E →L[ℂ] E)}
      (T : E →L[ℂ] E) := by
    simpa only [T, Unitary.coe_linearIsometryEquiv_apply, ht] using hmin
  obtain ⟨V, hV, hlocal⟩ := exists_isLocalMinOn_restriction_of_invariant p hp T
    K.starProjection (isSelfAdjoint_starProjection K) N hTN hPN hmin'
  let P₀ : N →L[ℂ] N := (K.starProjection.toLinearMap.restrict hPN).toContinuousLinearMap
  let K₀ := K.comap N.subtype
  have hP₀ (z : N) : (P₀ z : E) = K.starProjection (z : E) := rfl
  have hUP (z : E) : T (K.starProjection z) = L.starProjection (T z) := by
    have h := congrArg (fun A : E →L[ℂ] E => A (T z)) ht
    have hleft : star (U : E →L[ℂ] E) ((U : E →L[ℂ] E) z) = z :=
      congrArg (fun A : E →L[ℂ] E => A z) (Unitary.star_mul_self_of_mem U.property)
    change (U : E →L[ℂ] E) (K.starProjection
      (star (U : E →L[ℂ] E) ((U : E →L[ℂ] E) z))) =
        L.starProjection ((U : E →L[ℂ] E) z) at h
    rw [hleft] at h
    exact h
  have hVP : Commute (V : N →L[ℂ] N) P₀ := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    change (V (P₀ z) : E) = (P₀ (V z) : E)
    calc
      _ = T (P₀ z : E) := hV (P₀ z)
      _ = T (K.starProjection (z : E)) := congrArg T (hP₀ z)
      _ = L.starProjection (T z) := hUP z
      _ = L.starProjection (V z : E) := congrArg L.starProjection (hV z).symm
      _ = K.starProjection (V z : E) := (hPQ (V z)).symm
      _ = _ := (hP₀ (V z)).symm
  have hP₀eq : P₀ = K₀.starProjection := by
    ext z
    exact (Submodule.starProjection_comap_subtype_apply_of_invariant K N hPN z).symm
  have hVtrans := (commute_unitary_iff_star_right_conjugate
    (Unitary.linearIsometryEquiv.symm V).property).mp hVP
  change (V : N →L[ℂ] N) * P₀ * star (V : N →L[ℂ] N) = P₀ at hVtrans
  change IsLocalMinOn _ {W | W ∈ unitary (N →L[ℂ] N) ∧
    W * P₀ * star W = (V : N →L[ℂ] N) * P₀ * star (V : N →L[ℂ] N)}
      (V : N →L[ℂ] N) at hlocal
  rw [hVtrans, hP₀eq] at hlocal
  rw [hP₀eq] at hVtrans
  let Vunit := Unitary.linearIsometryEquiv.symm V
  have hVmap := (map_eq_iff_conjugate_starProjection_complex K₀ K₀ Vunit).mpr hVtrans
  have hcost := schatten_transport_cost_eq_sum_of_isLocalMinOn_complex
    p hp hp1 hp2 K₀ K₀ Vunit hVmap hlocal
  have hVlin : (V : N →L[ℂ] N).toLinearMap = V.toLinearMap := by ext z; rfl
  have hcost0 : UnitarilyInvariantSeminorm.schatten ℂ N N p
      (LinearMap.id - V.toLinearMap) ^ p.toReal = 0 := by
    rw [K₀.principalAngles_self] at hcost
    simpa only [Vunit, Unitary.coe_symm_linearIsometryEquiv_apply, hVlin,
      Finsupp.zero_apply, phaseMinimum_zero_angle p.toReal hp1.le,
      Finset.sum_const_zero] using hcost
  have hnorm := (Real.rpow_eq_zero (apply_nonneg _ _) (by linarith : p.toReal ≠ 0)).mp hcost0
  have hdisp := (UnitarilyInvariantSeminorm.schatten_apply_eq_zero_iff p).mp hnorm
  have hI := sub_eq_zero.mp hdisp
  have hxN : x ∈ N := by
    change K.sinAngleOperator L x = 0
    apply norm_eq_zero.mp
    rw [K.norm_sinAngleOperator_apply L x, hx, sub_self, norm_zero]
  let z : N := ⟨x, hxN⟩
  have hVz : V z = z := (congrArg (fun A : N →ₗ[ℂ] N => A z) hI).symm
  exact (hV z).symm.trans (congrArg (fun y : N => (y : E)) hVz)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
