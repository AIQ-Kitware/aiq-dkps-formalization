/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierSubcriticalTail
public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierFeasibility
public import DavisKahan.Geometry.Polar.DirectRotationIdeal
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReplaceFiniteTransport
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReducingSpectralTrace

/-!
# Exact unrestricted Charbonnier attainment in Hilbert space

Optimize a finite active sine sector and retain the canonical rotation on
the infinite subcritical tail. Hilbert--Schmidt projection difference and
balanced crossed defects suffice. The cost is the literal extended
Charbonnier trace, compared against every ambient complex transporter.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance attainmentComapSubtypeProjection
    (K N : Submodule ℂ E) [K.HasOrthogonalProjection] [CompleteSpace N] :
    (K.comap N.subtype).HasOrthogonalProjection :=
  K.hasOrthogonalProjection_comap_subtype_of_complete N

/-- **Exact global smoothed attainment by finite correction.** Every
positive subcritical cutoff gives a global ambient minimizer, agreeing
with the completed direct rotation on the whole complementary tail.
The update rank is bounded by the actual finite cutoff dimension. -/
theorem exists_charbonnier_minimizer_by_finite_correction
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (smoothedCriticalAngle tau)) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let R := nonacuteDirectRotation K L J
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (∀ x ∈ Mᗮ, U x = R x) ∧
      (R.toLinearMap - U.toLinearMap).rank ≤ Module.finrank ℂ M ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞ ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau =
        ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
          (1 - (T : E →L[ℂ] E)).charbonnierCost tau := by
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2
    (by norm_num) (K.starProjection - L.starProjection) hD
  obtain ⟨hM, hK, hL, _⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  have hRM : ∀ x ∈ M, R x ∈ M :=
    (sine_spectral_cutoff_isReducing_nonacuteDirectRotation K L J hcompact c hc).mem_invtSubmodule
  have hRmap : K.map R.toLinearMap = L :=
    (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L J)
  obtain ⟨V, hV, _, _⟩ := R.exists_restriction_of_finite_invariant M hRM
  let K₀ := K.comap M.subtype
  let L₀ := L.comap M.subtype
  have hVmap := K.map_comap_subtype_of_isometry_restriction L M R V hRmap hV
  have hdim := V.toLinearEquiv.finrank_map_eq K₀
  rw [hVmap] at hdim
  obtain ⟨W, hWmap, hWcost, _⟩ :=
    exists_unitary_minimizing_smoothed_transport_principalAngles tau hτ K₀ L₀ hdim.symm
  obtain ⟨U, hUmap, hUM, hUtail, hRank⟩ :=
    K.exists_transport_replacing_finite_block L M hK R hRmap hRM W hWmap
  have hfull := ContinuousLinearMap.charbonnierCost_unitary_displacement_eq_block_add_tail
    tau hτ M U R W hUM hUtail
  have hhead : (1 - (W : M →L[ℂ] M)).charbonnierCost tau =
      ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
        (Real.arcsin ((K₀.sinThetaMap L₀).singularValue j : ℝ))) := by
    rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
    change ENNReal.ofReal (smoothedDisplacementCost tau W.toLinearMap) = _
    have hnonneg (i : Fin (Module.finrank ℂ K₀)) :
        0 ≤ smoothedPhaseMinimum tau (K₀.principalAngles L₀ i) :=
      smoothedPhaseMinimum_nonneg tau _ hτ
        ⟨K₀.principalAngles_nonneg L₀ i, K₀.principalAngles_le_pi_div_two L₀ i⟩
    rw [hWcost, ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i),
      OperatorIdealFamily.tsum_singularValue_penalty_eq_sum _
        (fun s => ENNReal.ofReal (smoothedPhaseMinimum tau (Real.arcsin (s : ℝ))))
        (by simp only [NNReal.coe_zero, Real.arcsin_zero,
          smoothedPhaseMinimum_zero_angle tau hτ, ENNReal.ofReal_zero])]
    simp_rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]
    exact Submodule.sum_principalAngles_eq_sum_singularValues_arcsin K₀ L₀
      (fun t => ENNReal.ofReal (smoothedPhaseMinimum tau t))
      (by rw [smoothedPhaseMinimum_zero_angle tau hτ, ENNReal.ofReal_zero])
  have htail : (Mᗮ.orthogonalProjectionOnto ∘L (1 - (R : E →L[ℂ] E)) ∘L
        Mᗮ.subtypeL).charbonnierCost tau =
      ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
        (Real.arcsin (((K.comap Mᗮ.subtype).sinThetaMap
          (L.comap Mᗮ.subtype)).singularValue j : ℝ))) :=
    charbonnier_canonical_cutoff_tail_eq_minimum_sum tau hτ K L J hcompact c hc hc1 hcrit
  have hcost : (1 - (U : E →L[ℂ] E)).charbonnierCost tau =
      ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
        (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) := by
    rw [hfull, hhead, htail,
      Submodule.tsum_sine_penalty_eq_add_of_isReducing K L M hcompact hK hL
        (fun s => ENNReal.ofReal (smoothedPhaseMinimum tau (Real.arcsin (s : ℝ))))
        (by simp only [NNReal.coe_zero, Real.arcsin_zero,
          smoothedPhaseMinimum_zero_angle tau hτ, ENNReal.ofReal_zero])]
  have hRfinite : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (1 - (R : E →L[ℂ] E)) ≠ ∞ :=
    (gauge_nonacuteDirectRotation_ne_top_iff_projection_sub
      (OperatorIdealFamily.schatten ℂ 2 (by norm_num)) K L J).mpr hD
  have hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞ := by
    apply (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mpr
    exact ContinuousLinearMap.gauge_schatten_displacement_ne_top_of_finite_restriction_and_ideal_tail
      2 (by norm_num) M U (R : E →L[ℂ] E) W (fun x => (hUM x).symm) hUtail hRfinite
  refine ⟨U, hUmap, hUtail, hRank, hfinite, hcost, ?_⟩
  intro T hT
  rw [hcost]
  exact sine_smoothedPhaseMinimum_sum_le_transport tau hτ K L T hT

/-- **Unrestricted infinite-rank Charbonnier attainment.** Native
Hilbert--Schmidt projection difference and balanced crossed defects
give a finite-cost attainer with the exact principal-angle minimum.
No separability, prescribed blocks or finite-rank reference is assumed. -/
theorem exists_unitary_minimizing_charbonnier_transport_of_projection_sub_ne_top
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (hbalance : Module.finrank ℂ (halmosSourceDefect K L) =
      Module.finrank ℂ (halmosTargetDefect K L)) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞ ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau =
        ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
          (1 - (T : E →L[ℂ] E)).charbonnierCost tau := by
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2
    (by norm_num) (K.starProjection - L.starProjection) hD
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq
    K L hcompact hbalance
  let c := Real.sin (smoothedCriticalAngle tau) / 2
  have hangle := smoothedCriticalAngle_mem tau hτ
  have hsin : 0 < Real.sin (smoothedCriticalAngle tau) :=
    Real.sin_pos_of_pos_of_lt_pi hangle.1 (by linarith [hangle.2, Real.pi_pos])
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : c < 1 := by dsimp only [c]; linarith [Real.sin_le_one (smoothedCriticalAngle tau)]
  have hcrit : c ≤ Real.sin (smoothedCriticalAngle tau) := by dsimp only [c]; linarith
  obtain ⟨U, hmap, _, _, hfinite, hcost, hmin⟩ :=
    exists_charbonnier_minimizer_by_finite_correction tau hτ K L J hD c hc hc1 hcrit
  exact ⟨U, hmap, hfinite, hcost, hmin⟩

/-- A globally optimal finite update obeys the native Hilbert--Schmidt
rank budget at the exact smoothed critical cutoff. -/
theorem exists_charbonnier_minimizer_with_critical_rank_budget
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞) :
    ∃ U : E ≃ₗᵢ[ℂ] E, ∃ n : ℕ,
      K.map U.toLinearMap = L ∧
      ((nonacuteDirectRotation K L J).toLinearMap - U.toLinearMap).rank ≤ n ∧
      (n : ℝ≥0∞) * ENNReal.ofReal (Real.sin (smoothedCriticalAngle tau)) ^ (2 : ℝ) ≤
        (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
          (K.starProjection - L.starProjection) ^ (2 : ℝ) ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞ ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau =
        ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
          (1 - (T : E →L[ℂ] E)).charbonnierCost tau := by
  let c := Real.sin (smoothedCriticalAngle tau)
  have hangle := smoothedCriticalAngle_mem tau hτ
  have hc : 0 < c := Real.sin_pos_of_pos_of_lt_pi hangle.1
    (by linarith [hangle.2, Real.pi_pos])
  have hc1 : c < 1 := by
    have h := Real.strictMonoOn_sin
      ⟨by linarith [hangle.1, Real.pi_pos], hangle.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hangle.2
    simpa only [Real.sin_pi_div_two] using h
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) (K.starProjection - L.starProjection) hD
  obtain ⟨U, hmap, _, hRank, hfinite, hcost, hmin⟩ :=
    exists_charbonnier_minimizer_by_finite_correction tau hτ K L J hD c hc hc1 le_rfl
  exact ⟨U, Module.finrank ℂ (eigenSpan (K.sinAngleOperator L) (Set.Ioi c)),
    hmap, hRank, finrank_sine_spectral_cutoff_mul_rpow_le_schatten_projection_sub
      2 (by norm_num) K L hcompact c hc, hfinite, hcost, hmin⟩

/-- Finite-cost global smoothed attainment is equivalent to its exact
feasibility conditions. Both necessity and sufficiency hold for the
full ambient complex transport problem. -/
theorem charbonnier_finite_minimum_iff_projection_sub_and_defect_balance
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞ ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
          (1 - (T : E →L[ℂ] E)).charbonnierCost tau) ↔
    (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞ ∧
      Module.finrank ℂ (halmosSourceDefect K L) =
        Module.finrank ℂ (halmosTargetDefect K L) := by
  constructor
  · rintro ⟨U, hmap, hfinite, _⟩
    exact (charbonnier_transport_iff_schatten_two_and_defect_balance tau hτ K L).mp
      ⟨U, hmap, hfinite⟩
  · rintro ⟨hD, hbalance⟩
    obtain ⟨U, hmap, hfinite, _, hmin⟩ :=
      exists_unitary_minimizing_charbonnier_transport_of_projection_sub_ne_top tau hτ
        K L hD hbalance
    exact ⟨U, hmap, hfinite, hmin⟩

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
