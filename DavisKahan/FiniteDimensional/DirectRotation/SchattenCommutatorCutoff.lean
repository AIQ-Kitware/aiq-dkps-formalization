/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenSignedOptimizers
import ForTauCeti.Analysis.InnerProductSpace.Projection.GapThreshold

/-!
# Sharp projection-gap and commutator tests for Schatten uniqueness

The exact uniqueness cutoff is `2 * sqrt (p-1) / p` in projection-gap
coordinates. For a unitary image, the gap is the commutator norm with the
source projection. These tests require only one operator norm, including
the critical equality case, rather than the entire angle list.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal

/-- The critical sine has a rational square-root expression. -/
theorem sin_criticalAngle (p : ℝ) (hp1 : 1 < p) :
    Real.sin (criticalAngle p) = 2 * Real.sqrt (p - 1) / p := by
  have hp0 : 0 < p := by linarith
  rw [criticalAngle, Real.sin_arccos,
    show 1 - ((2 - p) / p) ^ 2 = (2 / p) ^ 2 * (p - 1) by
      field_simp
      ring,
    Real.sqrt_mul (sq_nonneg (2 / p)), Real.sqrt_sq (div_nonneg (by norm_num) hp0.le)]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The projection-gap test is necessary and sufficient for global
canonical optimality, including critical equality and dimension zero. -/
theorem schatten_canonical_minimal_iff_projectionGap_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    (∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - (nonacuteDirectRotation K L
            (finiteCrossedDefectEquiv K L hKL)).toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - T.toLinearMap) ^ p.toReal) ↔
      K.projectionGap L ≤ 2 * Real.sqrt (p.toReal - 1) / p.toReal := by
  rw [nonacuteDirectRotation_schatten_minimal_iff_complex p hp hp1 hp2 K L hKL,
    Submodule.finite_principalAngles_le_iff_directedProjectionGap_le K L _
      ⟨(criticalAngle_mem p.toReal hp1 hp2).1.le, (criticalAngle_mem p.toReal hp1 hp2).2.le⟩,
    K.projectionGap_eq_directedProjectionGap_of_finrank_eq L hKL,
    sin_criticalAngle p.toReal hp1]

/-- A single projection-gap norm characterizes uniqueness among all
ambient unitary transports, with arbitrary principal-angle multiplicities. -/
theorem schatten_transport_unique_minimizer_iff_projectionGap_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    (∃! U : unitary (E →L[ℂ] E),
      K.map (Unitary.linearIsometryEquiv U).toLinearMap = L ∧
      IsMinOn
        (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
        {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
        (U : E →L[ℂ] E)) ↔
      K.projectionGap L ≤ 2 * Real.sqrt (p.toReal - 1) / p.toReal := by
  rw [schatten_transport_unique_minimizer_iff_complex p hp hp1 hp2 K L hKL,
    Submodule.finite_principalAngles_le_iff_directedProjectionGap_le K L _
      ⟨(criticalAngle_mem p.toReal hp1 hp2).1.le, (criticalAngle_mem p.toReal hp1 hp2).2.le⟩,
    K.projectionGap_eq_directedProjectionGap_of_finrank_eq L hKL,
    sin_criticalAngle p.toReal hp1]

/-- For a prescribed unitary image, the sharp commutator cutoff
characterizes uniqueness of the optimal transporter. -/
theorem schatten_transport_unique_minimizer_iff_commutator_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) (A : E ≃ₗᵢ[ℂ] E) :
    (∃! U : unitary (E →L[ℂ] E),
      K.map (Unitary.linearIsometryEquiv U).toLinearMap = K.map A.toLinearMap ∧
      IsMinOn
        (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
        {W | W ∈ unitary (E →L[ℂ] E) ∧
          W * K.starProjection * star W = (K.map A.toLinearMap).starProjection}
        (U : E →L[ℂ] E)) ↔
      ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
        2 * Real.sqrt (p.toReal - 1) / p.toReal := by
  rw [schatten_transport_unique_minimizer_iff_projectionGap_complex p hp hp1 hp2
    K (K.map A.toLinearMap) (A.toLinearEquiv.finrank_map_eq K).symm,
    Submodule.projectionGap_unitary_image_eq_commutator]

/-- The nearest subspace-preserving unitary is unique exactly below and
at the sharp commutator cutoff. The comparison includes every ambient
unitary preserving the prescribed subspace. -/
theorem schatten_correction_unique_minimizer_iff_commutator_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) (A : E ≃ₗᵢ[ℂ] E) :
    (∃! C : E ≃ₗᵢ[ℂ] E, K.map C.toLinearMap = K ∧
      ∀ D : E ≃ₗᵢ[ℂ] E, K.map D.toLinearMap = K →
        UnitarilyInvariantSeminorm.schatten ℂ E E p
            (A.toLinearMap - C.toLinearMap) ^ p.toReal ≤
          UnitarilyInvariantSeminorm.schatten ℂ E E p
            (A.toLinearMap - D.toLinearMap) ^ p.toReal) ↔
      ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
        2 * Real.sqrt (p.toReal - 1) / p.toReal := by
  let L := K.map A.toLinearMap
  let e : (E ≃ₗᵢ[ℂ] E) ≃ (E ≃ₗᵢ[ℂ] E) :=
    { toFun := fun C => A.symm.trans C
      invFun := fun T => A.trans T
      left_inv := by intro C; ext x; simp
      right_inv := by intro T; ext x; simp }
  have hmap (C : E ≃ₗᵢ[ℂ] E) : L.map (e C).toLinearMap = K.map C.toLinearMap := by
    change (K.map A.toLinearMap).map (A.symm.trans C).toLinearMap = _
    rw [← Submodule.map_comp]
    congr 1
    ext x
    exact congrArg C (A.symm_apply_apply x)
  have hcost (C : E ≃ₗᵢ[ℂ] E) :
      UnitarilyInvariantSeminorm.schatten ℂ E E p
          (A.toLinearMap - C.toLinearMap) ^ p.toReal =
        UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - (e C).toLinearMap) ^ p.toReal := by
    have hfac : A.toLinearMap - C.toLinearMap =
        (LinearMap.id - (e C).toLinearMap) ∘ₗ A.toLinearMap := by
      ext x
      change A x - C x = A x - C (A.symm (A x))
      rw [A.symm_apply_apply]
    rw [hfac]
    exact congrArg (fun t : ℝ => t ^ p.toReal)
      ((UnitarilyInvariantSeminorm.schatten ℂ E E p).map_comp_linearIsometryEquiv A _)
  let CorrMin (C : E ≃ₗᵢ[ℂ] E) : Prop := K.map C.toLinearMap = K ∧
    ∀ D : E ≃ₗᵢ[ℂ] E, K.map D.toLinearMap = K →
      UnitarilyInvariantSeminorm.schatten ℂ E E p (A.toLinearMap - C.toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p (A.toLinearMap - D.toLinearMap) ^ p.toReal
  let TransMin (T : E ≃ₗᵢ[ℂ] E) : Prop := L.map T.toLinearMap = K ∧
    ∀ V : E ≃ₗᵢ[ℂ] E, L.map V.toLinearMap = K →
      UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - T.toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - V.toLinearMap) ^ p.toReal
  have hpred (C) : CorrMin C ↔ TransMin (e C) := by
    constructor
    · rintro ⟨hC, hmin⟩
      refine ⟨(hmap C).trans hC, ?_⟩
      intro V hV
      obtain ⟨D, rfl⟩ := e.surjective V
      have hh := hmin D ((hmap D).symm.trans hV)
      simpa only [hcost] using hh
    · rintro ⟨hC, hmin⟩
      refine ⟨(hmap C).symm.trans hC, ?_⟩
      intro D hD
      rw [hcost, hcost]
      exact hmin (e D) ((hmap D).trans hD)
  have heq := e.existsUnique_congr hpred
  change (∃! C, CorrMin C) ↔ _
  rw [heq]
  change (∃! T : E ≃ₗᵢ[ℂ] E, L.map T.toLinearMap = K ∧
    ∀ V : E ≃ₗᵢ[ℂ] E, L.map V.toLinearMap = K →
      UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - T.toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - V.toLinearMap) ^ p.toReal) ↔ _
  rw [schatten_transport_unique_minimizer_linearIsometryEquiv_iff_complex p hp hp1 hp2
    L K (A.toLinearEquiv.finrank_map_eq K)]
  rw [Submodule.finite_principalAngles_le_iff_directedProjectionGap_le L K _
      ⟨(criticalAngle_mem p.toReal hp1 hp2).1.le, (criticalAngle_mem p.toReal hp1 hp2).2.le⟩,
    ← L.projectionGap_eq_directedProjectionGap_of_finrank_eq K (A.toLinearEquiv.finrank_map_eq K),
    Submodule.projectionGap_comm, Submodule.projectionGap_unitary_image_eq_commutator,
    sin_criticalAngle p.toReal hp1]

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
