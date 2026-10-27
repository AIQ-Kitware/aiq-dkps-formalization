/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierStationarity
public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierMinimizerRestriction
public import ForTauCeti.Analysis.InnerProductSpace.Projection.AnticommutingModulus
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedNonacuteClassification

/-!
# Finite spectral sectors of every Hilbert-space Charbonnier optimizer

Constrained stationarity makes the gradient modulus commute with the
source projection. Its positive spectral cutoffs are finite and reduce
the source, target and actual minimizing unitary. Their actual unitary
restrictions are unrestricted finite-dimensional global minimizers.
No block or canonical-tail assumption is supplied about the optimizer.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Actual finite spectral classification sectors for every
optimizer.** Every positive gradient-modulus cutoff reduces both
projections and the minimizing unitary, carries its actual forward and
inverse restrictions, and inherits unrestricted finite optimality.
Only the gradient, rather than displacement, is bounded on its tail. -/
theorem exists_charbonnier_minimizing_restriction_on_gradient_cutoff
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
    (ε : ℝ) (hε : 0 < ε) :
    let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
    let M := eigenSpan G.modulus (Set.Ioi ε)
    ∃ hM : FiniteDimensional ℂ M,
      let _ : FiniteDimensional ℂ M := hM
      M.IsReducing K.starProjection.toLinearMap ∧
      M.IsReducing L.starProjection.toLinearMap ∧ M.IsReducing U.toLinearMap ∧
      ‖G ∘L Mᗮ.subtypeL‖ ≤ ε ∧
      ∃ V : M ≃ₗᵢ[ℂ] M,
        (∀ x : M, (V x : E) = U x) ∧ (∀ x : M, (V.symm x : E) = U.symm x) ∧
        (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
        ∀ W : M ≃ₗᵢ[ℂ] M,
          (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
          smoothedDisplacementCost tau V.toLinearMap ≤
            smoothedDisplacementCost tau W.toLinearMap := by
  dsimp only
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  let A := G.modulus
  let M := eigenSpan A (Set.Ioi ε)
  let : IsStarNormal (U : E →L[ℂ] E) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm U).property
  have hG : IsSelfAdjoint G := isSelfAdjoint_smoothedUnitaryGradient _ _
  have hSp := (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hfinite
  have hUcompact : IsCompactOperator (((U : E →L[ℂ] E) - 1) : E →L[ℂ] E) := by
    rw [← neg_sub 1 (U : E →L[ℂ] E)]
    exact (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2 (by norm_num)
      (1 - (U : E →L[ℂ] E)) hSp).neg
  have hGc : IsCompactOperator G := isCompactOperator_smoothedUnitaryGradient tau hτ U hUcompact
  have hAc : IsCompactOperator A := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hseq : A.singularValue = G.singularValue :=
      funext (fun n => ContinuousLinearMap.singularValue_modulus G n)
    rw [hseq]
    exact hGc.tendsto_singularValue
  have hAs : IsSelfAdjoint A := G.isSelfAdjoint_modulus
  have hM : FiniteDimensional ℂ M :=
    finiteDimensional_eigenSpan hAc hAs hε (fun _ hs => hs.le)
  let : FiniteDimensional ℂ M := hM
  have hPA : Commute K.starProjection A :=
    K.commute_starProjection_modulus_of_reflection_conjugate_eq_neg G hG
      (gradient_reflection_conjugate_eq_neg_of_charbonnier_minimal tau hτ K L U hmap hfinite hmin)
  have hK : M.IsReducing K.starProjection.toLinearMap := by
    apply (K.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule M).mpr
    exact eigenSpan_invariant_of_commute A K.starProjection hPA _
  have hUG : Commute (U : E →L[ℂ] E) G := (commute_smoothedUnitaryGradient tau _).symm
  have hUA : Commute (U : E →L[ℂ] E) A := by
    apply ContinuousLinearMap.commute_modulus_of_commute
    change Commute (U : E →L[ℂ] E) (star G * G)
    rw [hG.star_eq]
    exact hUG.mul_right hUG
  have hUM : ∀ x ∈ M, U x ∈ M := eigenSpan_invariant_of_commute A _ hUA _
  obtain ⟨_, _, _, hUred⟩ := U.exists_restriction_of_finite_invariant M hUM
  obtain ⟨V, hV, hlocal, hVmin⟩ := exists_charbonnier_minimizing_finite_restriction tau hτ
    K L M U hmap hfinite hmin hK hUM
  have hL : M.IsReducing L.starProjection.toLinearMap := by
    apply (L.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule M).mpr
    intro x hx
    change L.starProjection x ∈ M
    have h := K.starProjection_map_mem_of_isometry_restriction M U V hV
      hK.mem_invtSubmodule x hx
    simpa only [hmap] using h
  refine ⟨hM, hK, hL, hUred, ?_, V, hV, ?_, hlocal, ?_⟩
  · have htail : ‖A ∘L Mᗮ.subtypeL‖ ≤ ε :=
      norm_comp_orthogonal_eigenSpan_le hAc hAs G.isPositive_modulus.re_inner_nonneg_left
        hε.le (fun _ hs => hs)
    apply ContinuousLinearMap.opNorm_le_bound _ hε.le
    intro x
    change ‖G (x : E)‖ ≤ ε * ‖x‖
    calc
      _ = ‖A (x : E)‖ := (G.norm_modulus_apply (x : E)).symm
      _ ≤ ‖A ∘L Mᗮ.subtypeL‖ * ‖x‖ := (A ∘L Mᗮ.subtypeL).le_opNorm x
      _ ≤ _ := mul_le_mul_of_nonneg_right htail (norm_nonneg x)
  · intro x
    apply U.injective
    rw [← hV, V.apply_symm_apply, U.apply_symm_apply]
  · intro W hW
    have hcost (X : M ≃ₗᵢ[ℂ] M) : (1 - (X : M →L[ℂ] M)).charbonnierCost tau =
        ENNReal.ofReal (smoothedDisplacementCost tau X.toLinearMap) := by
      rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
      rfl
    have hnonneg : 0 ≤ smoothedDisplacementCost tau W.toLinearMap := by
      unfold smoothedDisplacementCost
      apply Finset.sum_nonneg
      intro i _
      exact sub_nonneg.mpr (Real.le_sqrt_of_sq_le
        (by nlinarith [sq_nonneg ((LinearMap.id - W.toLinearMap).singularValues i)]))
    have h := hVmin W hW
    rw [hcost, hcost] at h
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp h

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
