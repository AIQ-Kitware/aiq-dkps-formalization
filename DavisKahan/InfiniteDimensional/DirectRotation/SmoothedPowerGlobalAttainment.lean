/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SmoothedPowerCanonicalTrace
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenNuclearEndpoint
public import DavisKahan.Geometry.Polar.CanonicalCutoffTail
public import ForTauCeti.Analysis.OperatorIdeal.SmoothedPowerFiniteCorrection
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReplaceFiniteTransport
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReducingSpectralTrace

/-!
# Exact common-family transport attainment in arbitrary Hilbert dimension

The same finite active-sector correction and canonical tail solve every
regular member of the closed family. The sole nuclear corner uses the
already proved signed-root construction. Native ideal domains and defect
balance remain explicit; costs are extended spectral sums and all ambient
complex unitary competitors are retained.

The finite-cutoff assembly adapts `CharbonnierGlobalAttainment` using the
common C1/C2 results and generic spectral block trace. Classical ingredients
include compact spectral theory, restricted-unitary feasibility and the
relative index; exact primary-source comparisons are in the provenance note.
Priority of this family-wide transport extension remains unresolved.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPowerTransport

open FiniteDimensional.SmoothedPowerTransport
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance attainmentComapSubtypeProjection
    (K N : Submodule ℂ E) [K.HasOrthogonalProjection] [CompleteSpace N] :
    (K.comap N.subtype).HasOrthogonalProjection :=
  K.hasOrthogonalProjection_comap_subtype_of_complete N

/-- The complete complementary canonical tail has exactly the intrinsic
minimum of the actual restricted pair below a positive canonical cutoff. -/
theorem canonical_cutoff_tail_eq_minimum_sum (p tau a : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hcrit : smoothedPowerCriticalCosine p tau ≤ Real.cos a)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[ℂ] E))
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) (hcut : c ≤ Real.sin a) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    (Mᗮ.orthogonalProjectionOnto ∘L (1 - nonacuteDirectRotation K L J) ∘L
      Mᗮ.subtypeL).smoothedPowerCost p tau =
      ∑' j, ENNReal.ofReal (phaseMinimum p tau
        (Real.arcsin (((K.comap Mᗮ.subtype).sinThetaMap
          (L.comap Mᗮ.subtype)).singularValue j : ℝ))) := by
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  obtain ⟨hM, hK, hL, _⟩ := finite_sine_spectral_cutoff K L hD c hc
  let : FiniteDimensional ℂ M := hM
  let K₀ := K.comap Mᗮ.subtype
  let L₀ := L.comap Mᗮ.subtype
  obtain ⟨V, hV, _, hcanonical, hgap⟩ :=
    exists_canonical_tail_of_finite_sine_cutoff K L J hD c hc hc1
  have hacute : IsUniformlyAcute K₀ L₀ := hgap.trans_lt hc1
  have hz := halmosSourceDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute
  have hz' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute
  let J₀ := LinearIsometryEquiv.ofEq _ _ (hz.trans hz'.symm)
  have hVe : (V : Mᗮ →L[ℂ] Mᗮ) = nonacuteDirectRotation K₀ L₀ J₀ :=
    hcanonical.trans (nonacuteDirectRotation_eq_canonicalPolarFactor_of_acute K₀ L₀ J₀ hz hz').symm
  have hD₀ : IsCompactOperator ((K₀.starProjection - L₀.starProjection) : Mᗮ →L[ℂ] Mᗮ) := by
    rw [K.projection_sub_comap_subtype_eq_compression_of_invariant L Mᗮ
      hK.orthogonal_mem_invtSubmodule hL.orthogonal_mem_invtSubmodule]
    exact (hD.comp_clm Mᗮ.subtypeL).clm_comp Mᗮ.orthogonalProjectionOnto
  have hdisp : Mᗮ.orthogonalProjectionOnto ∘L
      (1 - nonacuteDirectRotation K L J) ∘L Mᗮ.subtypeL = 1 - (V : Mᗮ →L[ℂ] Mᗮ) := by
    apply ContinuousLinearMap.ext
    intro x
    change Mᗮ.orthogonalProjectionOnto ((x : E) - nonacuteDirectRotation K L J x) = x - V x
    rw [map_sub, ← hV, Mᗮ.orthogonalProjectionOnto_mem_subspace_eq_self,
      Mᗮ.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [hdisp, hVe]
  exact nonacuteDirectRotation_eq_minimum_sum_of_subcritical p tau a hp hp2 htau ha hcrit
    K₀ L₀ J₀ hD₀ (hgap.trans hcut)

/-- **A common finite-correction attainment theorem.** Finite projection
penalty and an actual defect equivalence suffice on every member admitting
a positive canonical cutoff. The nuclear corner has no such cutoff. -/
theorem exists_minimizer_by_finite_correction (p tau a : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hcrit : smoothedPowerCriticalCosine p tau ≤ Real.cos a)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (K.starProjection - L.starProjection).smoothedPowerCost p tau ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) (hcut : c ≤ Real.sin a) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let R := nonacuteDirectRotation K L J
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (∀ x ∈ Mᗮ, U x = R x) ∧
      (R.toLinearMap - U.toLinearMap).rank ≤ Module.finrank ℂ M ∧
      (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau ≠ ∞ ∧
      (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau =
        ∑' j, ENNReal.ofReal (phaseMinimum p tau
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau ≤
          (1 - (T : E →L[ℂ] E)).smoothedPowerCost p tau := by
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  have hcompact := ContinuousLinearMap.isCompactOperator_of_smoothedPowerCost_ne_top
    p tau hp hp2 htau (K.starProjection - L.starProjection) hD
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
    exists_unitary_minimizing_transport_principalAngles_of_nonneg p tau hp hp2 htau K₀ L₀ hdim.symm
  obtain ⟨U, hUmap, hUM, hUtail, hRank⟩ :=
    K.exists_transport_replacing_finite_block L M hK R hRmap hRM W hWmap
  have hRfinite : (1 - (R : E →L[ℂ] E)).smoothedPowerCost p tau ≠ ∞ :=
    (nonacuteDirectRotation_cost_ne_top_iff_projection_sub p tau hp hp2 htau K L J).mpr hD
  have hfinite := ContinuousLinearMap.smoothedPowerCost_displacement_ne_top_of_finite_restriction_and_tail
    p tau hp hp2 htau M U (R : E →L[ℂ] E) W (fun x => (hUM x).symm) hUtail hRfinite
  have hUc := ContinuousLinearMap.isCompactOperator_of_smoothedPowerCost_ne_top
    p tau hp hp2 htau (1 - (U : E →L[ℂ] E)) hfinite
  have hfull := ContinuousLinearMap.tsum_unitary_displacement_penalty_eq_block_add_tail
    M U R W hUM hUtail hUc
    (fun s => ENNReal.ofReal ((tau ^ 2 + (s : ℝ) ^ 2) ^ (p / 2) - tau ^ p))
    (by rw [NNReal.coe_zero, smoothedPower_scalar_zero p tau htau, ENNReal.ofReal_zero])
  change (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau =
    (1 - (W : M →L[ℂ] M)).smoothedPowerCost p tau +
      (Mᗮ.orthogonalProjectionOnto ∘L (1 - (R : E →L[ℂ] E)) ∘L Mᗮ.subtypeL).smoothedPowerCost p tau at hfull
  have hhead : (1 - (W : M →L[ℂ] M)).smoothedPowerCost p tau =
      ∑' j, ENNReal.ofReal (phaseMinimum p tau
        (Real.arcsin ((K₀.sinThetaMap L₀).singularValue j : ℝ))) := by
    rw [smoothedPowerCost_displacement_eq_ofReal p tau (by linarith) htau, hWcost,
      ENNReal.ofReal_sum_of_nonneg (fun (i : Fin (Module.finrank ℂ K₀)) _ =>
        phaseMinimum_nonneg p tau _ (by linarith) htau (K₀.principalAngles_nonneg L₀ i)),
      OperatorIdealFamily.tsum_singularValue_penalty_eq_sum _
        (fun s => ENNReal.ofReal (phaseMinimum p tau (Real.arcsin (s : ℝ))))
        (by simp only [NNReal.coe_zero, Real.arcsin_zero, phaseMinimum_zero p tau htau, ENNReal.ofReal_zero])]
    simp_rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]
    exact Submodule.sum_principalAngles_eq_sum_singularValues_arcsin K₀ L₀
      (fun t => ENNReal.ofReal (phaseMinimum p tau t))
      (by rw [phaseMinimum_zero p tau htau, ENNReal.ofReal_zero])
  have htail : (Mᗮ.orthogonalProjectionOnto ∘L (1 - (R : E →L[ℂ] E)) ∘L
        Mᗮ.subtypeL).smoothedPowerCost p tau =
      ∑' j, ENNReal.ofReal (phaseMinimum p tau
        (Real.arcsin (((K.comap Mᗮ.subtype).sinThetaMap
          (L.comap Mᗮ.subtype)).singularValue j : ℝ))) :=
    canonical_cutoff_tail_eq_minimum_sum p tau a hp hp2 htau ha hcrit K L J hcompact c hc hc1 hcut
  have hcost : (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau =
      ∑' j, ENNReal.ofReal (phaseMinimum p tau
        (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) := by
    rw [hfull, hhead, htail,
      Submodule.tsum_sine_penalty_eq_add_of_isReducing K L M hcompact hK hL
        (fun s => ENNReal.ofReal (phaseMinimum p tau (Real.arcsin (s : ℝ))))
        (by simp only [NNReal.coe_zero, Real.arcsin_zero,
          phaseMinimum_zero p tau htau, ENNReal.ofReal_zero])]
  refine ⟨U, hUmap, hUtail, hRank, hfinite, hcost, ?_⟩
  intro T hT
  rw [hcost]
  exact angle_minimum_sum_le_transport p tau hp hp2 htau K L T hT

/-- All regular family members admit a positive acute canonical cutoff.
The nuclear corner is exactly the excluded parameter pair. -/
theorem exists_positive_canonical_cutoff (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau) (hregular : 0 < tau ∨ 1 < p) :
    ∃ a ∈ Set.Ioo 0 (Real.pi / 2), smoothedPowerCriticalCosine p tau ≤ Real.cos a := by
  have hC : smoothedPowerCriticalCosine p tau ∈ Set.Ico 0 1 := by
    by_cases hz : tau = 0
    · subst tau
      have hp1 : 1 < p := hregular.resolve_left (lt_irrefl 0)
      rw [smoothedPowerCriticalCosine_zero p hp]
      exact ⟨div_nonneg (by linarith) (by linarith),
        (div_lt_one (by linarith : 0 < p)).mpr (by linarith)⟩
    · exact smoothedPowerCriticalCosine_mem p tau hp hp2 (lt_of_le_of_ne htau (Ne.symm hz))
  let t := Real.arccos (smoothedPowerCriticalCosine p tau)
  have ht0 : 0 < t := Real.arccos_pos.mpr hC.2
  have htπ : t ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr hC.1
  refine ⟨t / 2, ⟨by linarith, by linarith [Real.pi_pos]⟩, ?_⟩
  have hcos := Real.antitoneOn_cos
    (show t / 2 ∈ Set.Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos])
    (show t ∈ Set.Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos]) (by linarith : t / 2 ≤ t)
  rw [show Real.cos t = smoothedPowerCriticalCosine p tau from
    Real.cos_arccos (by linarith [hC.1]) hC.2.le] at hcos
  exact hcos

/-- The common regular-family attainer is obtained by one finite-sector
correction, over arbitrary complex Hilbert dimension and rank. -/
theorem exists_unitary_minimizing_transport_regular (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau) (hregular : 0 < tau ∨ 1 < p)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : (K.starProjection - L.starProjection).smoothedPowerCost p tau ≠ ∞)
    (hbalance : Module.finrank ℂ (halmosSourceDefect K L) =
      Module.finrank ℂ (halmosTargetDefect K L)) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau ≠ ∞ ∧
      (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau =
        ∑' j, ENNReal.ofReal (phaseMinimum p tau
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau ≤
          (1 - (T : E →L[ℂ] E)).smoothedPowerCost p tau := by
  have hcompact := ContinuousLinearMap.isCompactOperator_of_smoothedPowerCost_ne_top
    p tau hp hp2 htau (K.starProjection - L.starProjection) hD
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq K L hcompact hbalance
  obtain ⟨a, ha, hcrit⟩ := exists_positive_canonical_cutoff p tau hp hp2 htau hregular
  let c := Real.sin a / 2
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2, Real.pi_pos])
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : c < 1 := by dsimp only [c]; linarith [Real.sin_le_one a]
  have hcut : c ≤ Real.sin a := by dsimp only [c]; linarith
  obtain ⟨U, hmap, _, _, hfinite, hcost, hmin⟩ :=
    exists_minimizer_by_finite_correction p tau a hp hp2 htau ha hcrit K L J hD c hc hc1 hcut
  exact ⟨U, hmap, hfinite, hcost, hmin⟩

/-- **Exact finite-cost attainment for the full closed family.** Finite
projection penalty and balanced crossed defects give the intrinsic angle
minimum against every ambient complex unitary. The nuclear corner reuses
its signed-root construction, not a nonexistent finite active cutoff. -/
theorem exists_unitary_minimizing_transport_of_projection_cost_ne_top (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : (K.starProjection - L.starProjection).smoothedPowerCost p tau ≠ ∞)
    (hbalance : Module.finrank ℂ (halmosSourceDefect K L) =
      Module.finrank ℂ (halmosTargetDefect K L)) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau ≠ ∞ ∧
      (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau =
        ∑' j, ENNReal.ofReal (phaseMinimum p tau
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau ≤
          (1 - (T : E →L[ℂ] E)).smoothedPowerCost p tau := by
  by_cases hregular : 0 < tau ∨ 1 < p
  · exact exists_unitary_minimizing_transport_regular p tau hp hp2 htau hregular K L hD hbalance
  have ht0 : tau = 0 := le_antisymm (not_lt.mp (fun h => hregular (Or.inl h))) htau
  have hp1 : p = 1 := le_antisymm (not_lt.mp (fun h => hregular (Or.inr h))) hp
  subst tau
  subst p
  have hDn : (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞ := by
    simpa only [ContinuousLinearMap.smoothedPowerCost_zero_smoothing 1 (by norm_num),
      ENNReal.rpow_one] using hD
  obtain ⟨U, hmap, hfinite, hvalue, _⟩ :=
    SchattenPhaseTransition.exists_unitary_minimizing_nuclear_transport_eq_phaseMinimum_sum_complex
      K L hDn hbalance
  have hcost : (1 - (U : E →L[ℂ] E)).smoothedPowerCost 1 0 =
      ∑' j, ENNReal.ofReal (phaseMinimum 1 0
        (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) := by
    rw [ContinuousLinearMap.smoothedPowerCost_zero_smoothing 1 (by norm_num), ENNReal.rpow_one, hvalue]
    apply tsum_congr
    intro j
    apply congrArg ENNReal.ofReal
    exact (phaseMinimum_zero_smoothing_eq 1 _ (by norm_num)
      ⟨Real.arcsin_nonneg.mpr (NNReal.coe_nonneg _), Real.arcsin_le_pi_div_two _⟩).symm
  refine ⟨U, hmap, ?_, hcost, ?_⟩
  · simpa only [ContinuousLinearMap.smoothedPowerCost_zero_smoothing 1 (by norm_num),
      ENNReal.rpow_one] using hfinite
  · intro T hT
    rw [hcost]
    exact angle_minimum_sum_le_transport 1 0 (by norm_num) (by norm_num) (by norm_num) K L T hT

/-- Finite-cost global attainment is equivalent to the common ideal and
index conditions. This distinguishes genuine finite optimization from an
extended-cost fiber on which every feasible unitary has infinite cost. -/
theorem finite_minimum_iff_projection_cost_and_defect_balance (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau ≠ ∞ ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau ≤
          (1 - (T : E →L[ℂ] E)).smoothedPowerCost p tau) ↔
      (K.starProjection - L.starProjection).smoothedPowerCost p tau ≠ ∞ ∧
      Module.finrank ℂ (halmosSourceDefect K L) =
        Module.finrank ℂ (halmosTargetDefect K L) := by
  constructor
  · rintro ⟨U, hmap, hfinite, _⟩
    exact (transport_iff_projection_cost_and_defect_balance p tau hp hp2 htau K L).mp
      ⟨U, hmap, hfinite⟩
  · rintro ⟨hD, hbalance⟩
    obtain ⟨U, hmap, hfinite, _, hmin⟩ :=
      exists_unitary_minimizing_transport_of_projection_cost_ne_top p tau hp hp2 htau K L hD hbalance
    exact ⟨U, hmap, hfinite, hmin⟩

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPowerTransport
