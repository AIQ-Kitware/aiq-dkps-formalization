/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6, GPT-6.1 Sol
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealNuclearMatching

/-!
# Exact nearest real orthogonal operator commuting with a projection

Transport the image of the prescribed subspace back to itself. Right
orthogonal invariance preserves the literal Schatten distance, so the
unrestricted real matching formula gives the nearest orthogonal member
of the projection commutant, including attainment and all competitors.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem map_self_iff_commute_projection (K : Submodule ℝ E) (V : E ≃ₗᵢ[ℝ] E) :
    K.map V.toLinearMap = K ↔ Commute (V : E →L[ℝ] E) K.starProjection := by
  have hiff : Commute (V : E →L[ℝ] E) K.starProjection ↔
      ∀ x, V (K.starProjection x) = K.starProjection (V x) := by
    constructor
    · intro h x
      exact congrArg (fun T : E →L[ℝ] E => T x) h.eq
    · intro h
      exact ContinuousLinearMap.ext h
  rw [hiff]
  constructor
  · intro hmap x
    have h := Submodule.starProjection_map_apply V K (V x)
    simpa only [hmap, V.symm_apply_apply] using h.symm
  · intro h
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      apply K.starProjection_eq_self_iff.mp
      change K.starProjection (V x) = V x
      rw [← h, K.starProjection_eq_self_iff.mpr hx]
    · intro y hy
      have hpre : V.symm y ∈ K := by
        apply K.starProjection_eq_self_iff.mp
        apply V.injective
        rw [h, V.apply_symm_apply, K.starProjection_eq_self_iff.mpr hy]
      exact ⟨V.symm y, hpre, V.apply_symm_apply y⟩

private theorem schatten_distance_eq_correction_displacement
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A V : E ≃ₗᵢ[ℝ] E) :
    UnitarilyInvariantSeminorm.schatten ℝ E E p (A.toLinearMap - V.toLinearMap) =
      UnitarilyInvariantSeminorm.schatten ℝ E E p
        (LinearMap.id - (A.symm.trans V).toLinearMap) := by
  have hfac : A.toLinearMap - V.toLinearMap =
      (LinearMap.id - (A.symm.trans V).toLinearMap) ∘ₗ A.toLinearMap := by
    ext x
    change A x - V x = A x - V (A.symm (A x))
    rw [A.symm_apply_apply]
  rw [hfac]
  exact (UnitarilyInvariantSeminorm.schatten ℝ E E p).map_comp_linearIsometryEquiv A _

/-- Exact nearest real orthogonal operator in a prescribed projection's
commutant. The literal Schatten distance to the input has the matching
value for the actual image-to-source principal angles, and is minimal
against every orthogonal commuting competitor. -/
theorem exists_nearest_real_schatten_commuting_orthogonal
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℝ E) (A : E ≃ₗᵢ[ℝ] E) :
    let L := K.map A.toLinearMap
    ∃ V : E ≃ₗᵢ[ℝ] E, Commute (V : E →L[ℝ] E) K.starProjection ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
          (A.toLinearMap - V.toLinearMap) ^ p.toReal =
        realPositiveSchattenMatchingMinimum p.toReal
          (fun j : {j : Fin (Module.finrank ℝ L) // 0 < L.principalAngles K j} =>
            L.principalAngles K j.val) ∧
      ∀ W : E ≃ₗᵢ[ℝ] E, Commute (W : E →L[ℝ] E) K.starProjection →
        UnitarilyInvariantSeminorm.schatten ℝ E E p (A.toLinearMap - V.toLinearMap) ≤
          UnitarilyInvariantSeminorm.schatten ℝ E E p (A.toLinearMap - W.toLinearMap) := by
  let L := K.map A.toLinearMap
  obtain ⟨T, hT, hcost, hmin⟩ := exists_minimizing_real_schatten_transport_matching
    p hp hp1 hp2 L K (A.toLinearEquiv.finrank_map_eq K)
  let V := A.trans T
  have hmapV : K.map V.toLinearMap = K := by
    change K.map (T.toLinearMap ∘ₗ A.toLinearMap) = K
    rw [Submodule.map_comp]
    exact hT
  have heq : A.symm.trans V = T := by ext x; simp [V]
  have hdist : UnitarilyInvariantSeminorm.schatten ℝ E E p
      (A.toLinearMap - V.toLinearMap) =
      UnitarilyInvariantSeminorm.schatten ℝ E E p (LinearMap.id - T.toLinearMap) := by
    rw [schatten_distance_eq_correction_displacement, heq]
  refine ⟨V, (map_self_iff_commute_projection K V).mp hmapV, ?_, ?_⟩
  · rw [hdist]
    exact hcost
  · intro W hW
    have hmapW := (map_self_iff_commute_projection K W).mpr hW
    have hmapS : L.map (A.symm.trans W).toLinearMap = K := by
      change (K.map A.toLinearMap).map (A.symm.trans W).toLinearMap = K
      rw [← Submodule.map_comp]
      have hlin : (A.symm.trans W).toLinearMap ∘ₗ A.toLinearMap = W.toLinearMap := by
        ext x
        exact congrArg W (A.symm_apply_apply x)
      rw [hlin, hmapW]
    have hbound := hmin (A.symm.trans W) hmapS
    rw [← hdist, ← schatten_distance_eq_correction_displacement p A W] at hbound
    exact (Real.rpow_le_rpow_iff (apply_nonneg _ _) (apply_nonneg _ _)
      (zero_lt_one.trans hp1)).mp hbound

/-- The exact nuclear analogue of nearest real orthogonal correction to a
projection commutant. The minimum is the closed nuclear matching value
of the actual image-to-source pair, with an attainer and full ambient
comparison. No differentiability of the nuclear norm is assumed. -/
theorem exists_nearest_real_nuclear_commuting_orthogonal
    (K : Submodule ℝ E) (A : E ≃ₗᵢ[ℝ] E) :
    let L := K.map A.toLinearMap
    ∃ V : E ≃ₗᵢ[ℝ] E, Commute (V : E →L[ℝ] E) K.starProjection ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E 1 (A.toLinearMap - V.toLinearMap) =
        realNuclearMatchingMinimum
          (fun j : {j : Fin (Module.finrank ℝ L) // 0 < L.principalAngles K j} =>
            L.principalAngles K j.val) ∧
      ∀ W : E ≃ₗᵢ[ℝ] E, Commute (W : E →L[ℝ] E) K.starProjection →
        UnitarilyInvariantSeminorm.schatten ℝ E E 1 (A.toLinearMap - V.toLinearMap) ≤
          UnitarilyInvariantSeminorm.schatten ℝ E E 1 (A.toLinearMap - W.toLinearMap) := by
  let L := K.map A.toLinearMap
  obtain ⟨T, hT, hcost, hmin⟩ := exists_minimizing_real_nuclear_transport_matching
    L K (A.toLinearEquiv.finrank_map_eq K)
  let V := A.trans T
  have hmapV : K.map V.toLinearMap = K := by
    change K.map (T.toLinearMap ∘ₗ A.toLinearMap) = K
    rw [Submodule.map_comp]
    exact hT
  have heq : A.symm.trans V = T := by ext x; simp [V]
  have hdist : UnitarilyInvariantSeminorm.schatten ℝ E E 1
      (A.toLinearMap - V.toLinearMap) =
      UnitarilyInvariantSeminorm.schatten ℝ E E 1 (LinearMap.id - T.toLinearMap) := by
    rw [schatten_distance_eq_correction_displacement, heq]
  refine ⟨V, (map_self_iff_commute_projection K V).mp hmapV, ?_, ?_⟩
  · rw [hdist]
    exact hcost
  · intro W hW
    have hmapW := (map_self_iff_commute_projection K W).mpr hW
    have hmapS : L.map (A.symm.trans W).toLinearMap = K := by
      change (K.map A.toLinearMap).map (A.symm.trans W).toLinearMap = K
      rw [← Submodule.map_comp]
      have hlin : (A.symm.trans W).toLinearMap ∘ₗ A.toLinearMap = W.toLinearMap := by
        ext x
        exact congrArg W (A.symm_apply_apply x)
      rw [hlin, hmapW]
    have hbound := hmin (A.symm.trans W) hmapS
    rw [← hdist, ← schatten_distance_eq_correction_displacement 1 A W] at hbound
    exact hbound

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
