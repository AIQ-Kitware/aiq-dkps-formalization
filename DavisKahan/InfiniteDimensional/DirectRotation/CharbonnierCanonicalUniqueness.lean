/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierOptimizerAngles
public import DavisKahan.Geometry.Polar.CanonicalCutoffTail
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedQuarticStability
public import ForTauCeti.Analysis.InnerProductSpace.Projection.GapThreshold

/-!
# Closed-threshold uniqueness in arbitrary Hilbert dimension

Every finite-cost global optimizer is canonical when the projection gap
is at most the critical sine. Compact sine cutoffs inherit finite
optimality; finite canonical uniqueness applies on each. Kernel and
spectral completeness retain arbitrary fixed ambient directions.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Below and at the critical sine, every finite-cost global optimizer
is the canonical polar rotation. Infinite rank, angle multiplicities,
zero angles and arbitrary fixed ambient directions are included. -/
theorem eq_canonicalPolarFactor_of_charbonnier_minimal_of_gap_le_critical
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
    (hgap : K.projectionGap L ≤ Real.sin (smoothedCriticalAngle tau)) :
    (U : E →L[ℂ] E) = spectraCanonicalPolarFactor K L := by
  have hcrit := smoothedCriticalAngle_mem tau hτ
  have hs1 : Real.sin (smoothedCriticalAngle tau) < 1 :=
    (Real.strictMonoOn_sin ⟨by linarith [hcrit.1, Real.pi_pos], hcrit.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hcrit.2).trans_eq Real.sin_pi_div_two
  have hacute : IsUniformlyAcute K L := hgap.trans_lt hs1
  have hz := halmosSourceDefect_eq_bot_of_isUniformlyAcute K L hacute
  have hz' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K L hacute
  let J := LinearIsometryEquiv.ofEq _ _ (hz.trans hz'.symm)
  let R := nonacuteDirectRotation K L J
  have hRpolar : R = spectraCanonicalPolarFactor K L :=
    nonacuteDirectRotation_eq_canonicalPolarFactor_of_acute K L J hz hz'
  have hSp := (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hfinite
  have hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[ℂ] E) :=
    OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2 (by norm_num) _
      (ne_top_of_le_ne_top hSp
        ((OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge_projection_sub_le_unitary_displacement
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
  have hUS := commute_sinAngleOperator_of_charbonnier_minimal tau hτ K L U hmap hfinite hmin
  rw [← hRpolar]
  apply eq_of_eq_on_ker_and_positive_eigenSpans hSc
    (K.isPositive_sinAngleOperator L).isSelfAdjoint
    (K.isPositive_sinAngleOperator L).re_inner_nonneg_left
  · intro x hx
    have hPQ : K.starProjection x = L.starProjection x := by
      have h := K.norm_sinAngleOperator_apply L x
      rw [show S x = 0 from hx, norm_zero] at h
      exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)
    exact (apply_eq_self_of_projections_eq_of_charbonnier_minimal_of_commute tau hτ
      K L U hmap hfinite hmin hUS x hPQ).trans
        (nonacuteDirectRotation_apply_eq_self_of_projections_eq K L J x hPQ).symm
  · intro ε hε x hx
    let M := eigenSpan S (Set.Ioi ε)
    obtain ⟨hM, hK, hL, _⟩ := finite_sine_spectral_cutoff K L hD ε hε
    let : FiniteDimensional ℂ M := hM
    have hUM : ∀ y ∈ M, U y ∈ M := eigenSpan_invariant_of_commute S _ hUS _
    obtain ⟨V, hV, hlocal, hVmin⟩ := exists_charbonnier_minimizing_finite_restriction
      tau hτ K L M U hmap hfinite hmin hK hUM
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
    have hgap₀ : K₀.projectionGap L₀ ≤ Real.sin (smoothedCriticalAngle tau) :=
      (K.projectionGap_comap_subtype_le_of_invariant L M
        hK.mem_invtSubmodule hL.mem_invtSubmodule).trans hgap
    have hacute₀ : IsUniformlyAcute K₀ L₀ := hgap₀.trans_lt hs1
    have hz₀ := halmosSourceDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute₀
    have hz₀' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute₀
    have hcost (T : M ≃ₗᵢ[ℂ] M) :
        (1 - (T : M →L[ℂ] M)).charbonnierCost tau =
          ENNReal.ofReal (smoothedDisplacementCost tau T.toLinearMap) := by
      rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
      rfl
    have hmax := (K₀.finite_principalAngles_le_iff_directedProjectionGap_le L₀
      (smoothedCriticalAngle tau) ⟨hcrit.1.le, hcrit.2.le⟩).mpr
        ((K₀.directedProjectionGap_le_projectionGap L₀).trans hgap₀)
    let R₀ := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K₀ L₀ J₀,
        nonacuteDirectRotation_mem_unitary K₀ L₀ J₀⟩ : unitary (M →L[ℂ] M))
    have huniq := smoothed_canonical_unique_minimizer tau hτ K₀ L₀ hdim hmax
    have hle := hVmin R₀ huniq.1
    rw [hcost, hcost] at hle
    have hVeq : V = R₀ := (huniq.2 V hlocal).2
      ((ENNReal.ofReal_le_ofReal_iff (by
        unfold smoothedDisplacementCost
        apply Finset.sum_nonneg
        intro i _
        exact sub_nonneg.mpr (Real.le_sqrt_of_sq_le
          (by nlinarith [sq_nonneg ((LinearMap.id - R₀.toLinearMap).singularValues i)])))).mp hle)
    have hVcanon : (V : M →L[ℂ] M) = nonacuteDirectRotation K₀ L₀ J₀ := by
      rw [hVeq]
      rfl
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

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
