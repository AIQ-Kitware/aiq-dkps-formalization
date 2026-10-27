/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenLocalFixed
public import DavisKahan.Geometry.Polar.CanonicalCutoffTail
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenCanonicalUniqueness
public import ForTauCeti.Analysis.InnerProductSpace.Projection.GapThreshold

/-!
# Closed-threshold uniqueness in arbitrary Hilbert dimension

Every finite-cost local optimizer is canonical when the projection gap
is at most the critical sine. Compact sine cutoffs inherit finite
optimality; finite canonical uniqueness applies on each. Kernel and
spectral completeness retain arbitrary fixed ambient directions.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Below and at the critical sine, every finite-cost local optimizer
is the canonical polar rotation. Infinite rank, angle multiplicities,
zero angles and arbitrary fixed ambient directions are included. -/
theorem eq_canonicalPolarFactor_of_schatten_isLocalMinOn_of_gap_le_critical_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U)
    (hgap : K.projectionGap L ≤ Real.sin (criticalAngle p.toReal)) :
    (U : E →L[ℂ] E) = spectraCanonicalPolarFactor K L := by
  have hcrit := criticalAngle_mem p.toReal hp1 hp2
  have hs1 : Real.sin (criticalAngle p.toReal) < 1 :=
    (Real.strictMonoOn_sin ⟨by linarith [hcrit.1, Real.pi_pos], hcrit.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hcrit.2).trans_eq Real.sin_pi_div_two
  have hacute : IsUniformlyAcute K L := hgap.trans_lt hs1
  have hz := halmosSourceDefect_eq_bot_of_isUniformlyAcute K L hacute
  have hz' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K L hacute
  let J := LinearIsometryEquiv.ofEq _ _ (hz.trans hz'.symm)
  let R := nonacuteDirectRotation K L J
  have hRpolar : R = spectraCanonicalPolarFactor K L :=
    nonacuteDirectRotation_eq_canonicalPolarFactor_of_acute K L J hz hz'
  have hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[ℂ] E) :=
    OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le _
      (ne_top_of_le_ne_top hfinite
        ((OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge_projection_sub_le_unitary_displacement
          K L U hmap))
  let S := K.sinAngleOperator L
  have hSc : IsCompactOperator S := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hseq : S.singularValue = (K.starProjection - L.starProjection).singularValue := by
      funext n
      dsimp only [S]
      rw [Submodule.sinAngleOperator_def, ContinuousLinearMap.singularValue_modulus]
    rw [hseq]
    exact hD.tendsto_singularValue
  have hUS := commute_sinAngleOperator_of_schatten_isLocalMinOn_complex p hp hp1 hp2 K L U hmap hfinite hmin
  rw [← hRpolar]
  apply eq_of_eq_on_ker_and_positive_eigenSpans hSc
    (K.isPositive_sinAngleOperator L).isSelfAdjoint
    (K.isPositive_sinAngleOperator L).re_inner_nonneg_left
  · intro x hx
    have hPQ : K.starProjection x = L.starProjection x := by
      have h := K.norm_sinAngleOperator_apply L x
      rw [show S x = 0 from hx, norm_zero] at h
      exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)
    exact (apply_eq_self_of_projections_eq_of_schatten_isLocalMinOn_complex p hp hp1 hp2
      K L U hmap hfinite hmin x hPQ).trans
        (nonacuteDirectRotation_apply_eq_self_of_projections_eq K L J x hPQ).symm
  · intro ε hε x hx
    let M := eigenSpan S (Set.Ioi ε)
    obtain ⟨hM, hK, hL, _⟩ := finite_sine_spectral_cutoff K L hD ε hε
    let : FiniteDimensional ℂ M := hM
    have hUM : ∀ y ∈ M, U y ∈ M := eigenSpan_invariant_of_commute S _ hUS _
    obtain ⟨V, hV, hlocal, _, hVmin⟩ := exists_schatten_locally_minimizing_finite_restriction
      p.toReal hp1.le K L M U hmap hfinite hmin hK hUM
    have hRred := sine_spectral_cutoff_isReducing_nonacuteDirectRotation K L J hD ε hε
    let R' := Unitary.linearIsometryEquiv
      (⟨R, nonacuteDirectRotation_mem_unitary K L J⟩ : unitary (E →L[ℂ] E))
    obtain ⟨W, hW, _⟩ := R'.exists_restriction_of_reducing M hRred
    let K₀ := K.comap M.subtype
    let L₀ := L.comap M.subtype
    have hdim : Module.finrank ℂ K₀ = Module.finrank ℂ L₀ := by
      have h := V.toLinearEquiv.finrank_map_eq K₀
      rw [hlocal] at h
      exact h.symm
    let J₀ := finiteCrossedDefectEquiv K₀ L₀ hdim
    have hgap₀ : K₀.projectionGap L₀ ≤ Real.sin (criticalAngle p.toReal) :=
      (K.projectionGap_comap_subtype_le_of_invariant L M
        hK.mem_invtSubmodule hL.mem_invtSubmodule).trans hgap
    have hacute₀ : IsUniformlyAcute K₀ L₀ := hgap₀.trans_lt hs1
    have hz₀ := halmosSourceDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute₀
    have hz₀' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute₀
    have hVglobal := schatten_isMin_of_isLocalMinOn_finite_complex
      p hp hp1 hp2 K₀ L₀ V hlocal hVmin
    have hmin' : IsMinOn
        (fun T : M →L[ℂ] M => UnitarilyInvariantSeminorm.schatten ℂ M M p
          (LinearMap.id - T.toLinearMap) ^ p.toReal)
        {T | T ∈ unitary (M →L[ℂ] M) ∧ T * K₀.starProjection * star T = L₀.starProjection}
        (V : M →L[ℂ] M) := by
      intro T hT
      let T' := Unitary.linearIsometryEquiv (⟨T, hT.1⟩ : unitary (M →L[ℂ] M))
      have h := ENNReal.rpow_le_rpow (hVglobal T'
        ((map_eq_iff_conjugate_starProjection_complex K₀ L₀ ⟨T, hT.1⟩).mpr hT.2))
          (zero_lt_one.trans hp1).le
      rw [OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp,
        OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    have hVcanon := eq_canonicalRotation_of_isLocalMinOn_angles_le_critical_complex
      p hp hp1 hp2 K₀ L₀ (Unitary.linearIsometryEquiv.symm V) hlocal hmin'.isLocalMinOn
      ((K₀.finite_principalAngles_le_iff_directedProjectionGap_le L₀
        (criticalAngle p.toReal) ⟨hcrit.1.le, hcrit.2.le⟩).mpr
          ((K₀.directedProjectionGap_le_projectionGap L₀).trans hgap₀)) J₀
    have hWcanon := nonacuteDirectRotation_restriction_eq_canonicalPolarFactor_of_acute
      K L M J W hW hK.mem_invtSubmodule hz₀ hz₀'
    have hVW : (V : M →L[ℂ] M) = (W : M →L[ℂ] M) :=
      hVcanon.trans ((nonacuteDirectRotation_eq_canonicalPolarFactor_of_acute K₀ L₀ J₀ hz₀ hz₀').trans
        hWcanon.symm)
    calc
      U x = (V ⟨x, hx⟩ : E) := (hV ⟨x, hx⟩).symm
      _ = (W ⟨x, hx⟩ : E) := congrArg Subtype.val
        (congrArg (fun T : M →L[ℂ] M => T ⟨x, hx⟩) hVW)
      _ = R x := hW _

/-- Global canonical rigidity follows from closed-threshold local rigidity. -/
theorem eq_canonicalPolarFactor_of_schatten_minimal_of_gap_le_critical
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E)))
    (hgap : K.projectionGap L ≤ Real.sin (criticalAngle p.toReal)) :
    (U : E →L[ℂ] E) = spectraCanonicalPolarFactor K L := by
  exact eq_canonicalPolarFactor_of_schatten_isLocalMinOn_of_gap_le_critical_complex p hp hp1 hp2 K L U hmap hfinite
    (show IsMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U
      from fun T hT => hmin T hT).isLocalMinOn hgap

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
