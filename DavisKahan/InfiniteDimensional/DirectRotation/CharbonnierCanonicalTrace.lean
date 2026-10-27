/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierGlobalLowerBound
public import DavisKahan.Geometry.Polar.CanonicalApproximation
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCanonicalOptimality
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedBalancedPhases
public import ForTauCeti.Analysis.InnerProductSpace.Projection.GapThreshold
public import ForTauCeti.Analysis.OperatorIdeal.CharbonnierLimit

/-!
# Exact canonical smoothed costs on infinite subcritical pairs

Finite canonical restrictions and lower semicontinuity transfer the exact
smoothed minimum to compact uniformly subcritical projection pairs.
The objective is the literal extended Charbonnier trace.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition Filter
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem subcritical_scalar_formula (tau theta : ℝ) (hτ : 0 < tau)
    (hθ0 : 0 ≤ theta) (hθ : theta ≤ smoothedCriticalAngle tau) :
    smoothedPhaseMinimum tau theta =
      2 * (Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta) - tau) := by
  rw [smoothedPhaseMinimum_eq_canonical_of_le_critical tau theta hτ hθ0 hθ,
    Complex.norm_sub_one_sq_eq_of_norm_eq_one (Complex.norm_exp_ofReal_mul_I theta),
    Complex.exp_ofReal_mul_I_re]
  congr 3
  ring

private theorem subcritical_scalar_mono (tau x y : ℝ) (hτ : 0 < tau)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ smoothedCriticalAngle tau) :
    smoothedPhaseMinimum tau x ≤ smoothedPhaseMinimum tau y := by
  rw [subcritical_scalar_formula tau x hτ hx (hxy.trans hy),
    subcritical_scalar_formula tau y hτ (hx.trans hxy) hy]
  have hcrit := smoothedCriticalAngle_mem tau hτ
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hx (by linarith [hcrit.2]) hxy
  have hsqrt := Real.sqrt_le_sqrt (show tau ^ 2 + 2 - 2 * Real.cos x ≤
    tau ^ 2 + 2 - 2 * Real.cos y by linarith)
  linarith

/-- An actual finite restriction of a subcritical canonical rotation
attains the exact smoothed angle sum of the restricted projection pair. -/
theorem charbonnier_canonical_restriction_eq_minimum_sum
    (tau : ℝ) (hτ : 0 < tau)
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional ℂ M]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hacute : IsUniformlyAcute K L)
    (hcut : K.projectionGap L ≤ Real.sin (smoothedCriticalAngle tau))
    (V : M ≃ₗᵢ[ℂ] M)
    (hV : ∀ x : M, (V x : E) = nonacuteDirectRotation K L J x)
    (hK : ∀ x ∈ M, K.starProjection x ∈ M)
    (hL : ∀ x ∈ M, L.starProjection x ∈ M) :
    (1 - (V : M →L[ℂ] M)).charbonnierCost tau =
      ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
        (Real.arcsin (((K.comap M.subtype).sinThetaMap
          (L.comap M.subtype)).singularValue j : ℝ))) := by
  let K₀ := K.comap M.subtype
  let L₀ := L.comap M.subtype
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  have hmap : K.map R.toLinearMap = L :=
    (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L J)
  have hlocal : K₀.map V.toLinearMap = L₀ :=
    K.map_comap_subtype_of_isometry_restriction L M R V hmap hV
  have hdim : Module.finrank ℂ K₀ = Module.finrank ℂ L₀ := by
    have h := V.toLinearEquiv.finrank_map_eq K₀
    rw [hlocal] at h
    exact h.symm
  have hacute₀ : IsUniformlyAcute K₀ L₀ :=
    (K.projectionGap_comap_subtype_le_of_invariant L M hK hL).trans_lt hacute
  have hz := halmosSourceDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute₀
  have hz' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute₀
  have hcanonical : (V : M →L[ℂ] M) =
      nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hdim) := by
    calc
      _ = spectraCanonicalPolarFactor K₀ L₀ :=
        nonacuteDirectRotation_restriction_eq_canonicalPolarFactor_of_acute
          K L M J V hV hK hz hz'
      _ = _ := (nonacuteDirectRotation_eq_canonicalPolarFactor_of_acute K₀ L₀
        (finiteCrossedDefectEquiv K₀ L₀ hdim) hz hz').symm
  have hmax : ∀ i : Fin (Module.finrank ℂ K₀),
      K₀.principalAngles L₀ i ≤ smoothedCriticalAngle tau := by
    apply (Submodule.finite_principalAngles_le_iff_directedProjectionGap_le K₀ L₀ _
      (smoothedCriticalAngle_mem_Icc tau)).mpr
    exact (K₀.directedProjectionGap_le_projectionGap L₀).trans
      ((K.projectionGap_comap_subtype_le_of_invariant L M hK hL).trans hcut)
  obtain ⟨W, hWmap, hWcost, hmin⟩ :=
    exists_unitary_minimizing_smoothed_transport_principalAngles tau hτ K₀ L₀ hdim
  have hVmin := (smoothed_canonical_isMin_iff tau hτ K₀ L₀ hdim).mpr hmax
  have hlin : V.toLinearMap =
      (nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hdim)).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap hcanonical
  change ∀ T : M ≃ₗᵢ[ℂ] M, K₀.map T.toLinearMap = L₀ →
    smoothedDisplacementCost tau
      (nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hdim)).toLinearMap ≤
        smoothedDisplacementCost tau T.toLinearMap at hVmin
  rw [← hlin] at hVmin
  have hcost : smoothedDisplacementCost tau V.toLinearMap =
      ∑ i : Fin (Module.finrank ℂ K₀), smoothedPhaseMinimum tau (K₀.principalAngles L₀ i) :=
    le_antisymm ((hVmin W hWmap).trans_eq hWcost) (hmin V hlocal)
  rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
  change ENNReal.ofReal (smoothedDisplacementCost tau V.toLinearMap) = _
  have hnonneg (i : Fin (Module.finrank ℂ K₀)) :
      0 ≤ smoothedPhaseMinimum tau (K₀.principalAngles L₀ i) :=
    smoothedPhaseMinimum_nonneg tau _ hτ
      ⟨K₀.principalAngles_nonneg L₀ i, K₀.principalAngles_le_pi_div_two L₀ i⟩
  rw [hcost, ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i),
    OperatorIdealFamily.tsum_singularValue_penalty_eq_sum _
      (fun s => ENNReal.ofReal (smoothedPhaseMinimum tau (Real.arcsin (s : ℝ))))
      (by simp only [NNReal.coe_zero, Real.arcsin_zero,
        smoothedPhaseMinimum_zero_angle tau hτ, ENNReal.ofReal_zero])]
  simp_rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]
  exact Submodule.sum_principalAngles_eq_sum_singularValues_arcsin K₀ L₀
    (fun t => ENNReal.ofReal (smoothedPhaseMinimum tau t))
    (by rw [smoothedPhaseMinimum_zero_angle tau hτ, ENNReal.ofReal_zero])

/-- A canonical finite truncation has exactly the minimum smoothed
angle sum of its actual truncated target pair. -/
theorem charbonnier_canonical_truncation_eq_minimum_sum
    (tau : ℝ) (hτ : 0 < tau)
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional ℂ M]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hacute : IsUniformlyAcute K L)
    (hcut : K.projectionGap L ≤ Real.sin (smoothedCriticalAngle tau))
    (hRM : ∀ x ∈ M, nonacuteDirectRotation K L J x ∈ M)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hL : M.IsReducing L.starProjection.toLinearMap)
    (V : E ≃ₗᵢ[ℂ] E)
    (hV : ∀ x ∈ M, V x = nonacuteDirectRotation K L J x)
    (hfix : ∀ x ∈ Mᗮ, V x = x) :
    (1 - (V : E →L[ℂ] E)).charbonnierCost tau =
      ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
        (Real.arcsin ((K.sinThetaMap (K.map V.toLinearMap)).singularValue j : ℝ))) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  obtain ⟨W, hW, _, _⟩ := R.exists_restriction_of_finite_invariant M hRM
  have hdisp : 1 - (V : E →L[ℂ] E) = M.subtypeL ∘L
      (1 - (W : M →L[ℂ] M)) ∘L M.orthogonalProjectionOnto := by
    apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
    constructor
    · intro x
      change (x : E) - V x = (x : E) - (W x : E)
      rw [hW, hV x x.property]
      rfl
    · intro x hx
      change x - V x = 0
      rw [hfix x hx, sub_self]
  have hmap : K.map R.toLinearMap = L :=
    (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L J)
  have hsin := K.sinThetaMap_map_truncation_eq_comp_starProjection L M R V
    hmap hRM hK hL hV hfix
  have hsinext : (K.sinThetaMap L) ∘L M.starProjection = M.subtypeL ∘L
      ((K.comap M.subtype).sinThetaMap (L.comap M.subtype)) ∘L
        M.orthogonalProjectionOnto := by
    apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
    constructor
    · intro x
      change K.sinThetaMap L (M.starProjection (x : E)) = _
      rw [M.starProjection_eq_self_iff.mpr x.property]
      exact (K.sinThetaMap_comap_subtype_apply_of_invariant L M
        hK.mem_invtSubmodule hL.mem_invtSubmodule x).symm
    · intro x hx
      change K.sinThetaMap L (M.starProjection x) = 0
      rw [M.starProjection_apply_eq_zero_iff.mpr hx, map_zero]
  rw [hdisp, ContinuousLinearMap.charbonnierCost_orthogonal_extension, hsin, hsinext]
  simp_rw [ContinuousLinearMap.singularValue_orthogonal_extension]
  exact charbonnier_canonical_restriction_eq_minimum_sum tau hτ K L M J hacute hcut W hW
    hK.mem_invtSubmodule hL.mem_invtSubmodule

set_option maxHeartbeats 600000 in
/-- **Exact infinite-rank smoothed canonical minimum.** Compact
projection difference and the closed smoothed gap threshold suffice;
no ideal membership, separability or finite-rank assumption is imposed.
The equality includes divergent extended costs. -/
theorem charbonnier_nonacuteDirectRotation_eq_minimum_sum_of_subcritical
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[ℂ] E))
    (hcut : K.projectionGap L ≤ Real.sin (smoothedCriticalAngle tau)) :
    (1 - nonacuteDirectRotation K L J).charbonnierCost tau =
      ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
        (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) := by
  have hc := smoothedCriticalAngle_mem tau hτ
  have hsin1 : Real.sin (smoothedCriticalAngle tau) < 1 := by
    have h := Real.strictMonoOn_sin
      ⟨by linarith [hc.1, Real.pi_pos], hc.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hc.2
    simpa only [Real.sin_pi_div_two] using h
  have hacute : IsUniformlyAcute K L := hcut.trans_lt hsin1
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  choose V M hM hnorm hK hL hRM hV hfix hcost using fun n : ℕ =>
    exists_finite_canonical_approximation K L J hD (1 / ((n : ℝ) + 1)) (by positivity)
  have hlim : Tendsto (fun n => (V n : E →L[ℂ] E)) atTop (𝓝 (R : E →L[ℂ] E)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hnorm
      (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)))
  let S (A : E →L[ℂ] E) := (1 - A * K.starProjection * star A) * K.starProjection
  have hsin (W : E ≃ₗᵢ[ℂ] E) : K.sinThetaMap (K.map W.toLinearMap) = S (W : E →L[ℂ] E) := by
    have hproj := (K.map_eq_iff_conjugate_starProjection (K.map W.toLinearMap) W).mp rfl
    rw [Submodule.sinThetaMap_def, Submodule.starProjection_orthogonal, ← hproj]
    rfl
  have hmap : K.map R.toLinearMap = L :=
    (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L J)
  let f (s : ℝ≥0) := ENNReal.ofReal (smoothedPhaseMinimum tau (Real.arcsin (s : ℝ)))
  have hangle (j : ℕ) : Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ) ≤
      smoothedCriticalAngle tau := by
    have hs : ((K.sinThetaMap L).singularValue j : ℝ) ≤ Real.sin (smoothedCriticalAngle tau) :=
      (show ((K.sinThetaMap L).singularValue j : ℝ) ≤ ‖K.sinThetaMap L‖ from by
        exact_mod_cast (K.sinThetaMap L).singularValue_le_nnnorm j).trans
        ((K.norm_sinThetaMap L).trans_le ((K.directedProjectionGap_le_projectionGap L).trans hcut))
    calc
      _ ≤ Real.arcsin (Real.sin (smoothedCriticalAngle tau)) := Real.arcsin_le_arcsin hs
      _ = _ := Real.arcsin_sin (by linarith [hc.1, Real.pi_pos]) hc.2.le
  have heq (n : ℕ) : (1 - (V n : E →L[ℂ] E)).charbonnierCost tau =
      ∑' j, f ((S (V n)).singularValue j) := by
    let : FiniteDimensional ℂ (M n) := hM n
    rw [← hsin]
    exact charbonnier_canonical_truncation_eq_minimum_sum tau hτ K L (M n) J hacute hcut
      (hRM n) (hK n) (hL n) (V n) (hV n) (hfix n)
  have hdom (n : ℕ) : (∑' j, f ((S (V n)).singularValue j)) ≤
      ∑' j, f ((K.sinThetaMap L).singularValue j) := by
    let : FiniteDimensional ℂ (M n) := hM n
    rw [← hsin, K.sinThetaMap_map_truncation_eq_comp_starProjection L (M n) R (V n) hmap
      (hRM n) (hK n) (hL n) (hV n) (hfix n)]
    apply ENNReal.tsum_le_tsum
    intro j
    apply ENNReal.ofReal_le_ofReal
    apply subcritical_scalar_mono tau _ _ hτ (Real.arcsin_nonneg.mpr (NNReal.coe_nonneg _))
      (Real.arcsin_le_arcsin ?_) (hangle j)
    have hs : ((K.sinThetaMap L) ∘L (M n).starProjection).singularValue j ≤
        (K.sinThetaMap L).singularValue j := by
      calc
        _ ≤ (K.sinThetaMap L).singularValue j * ‖(M n).starProjection‖₊ :=
          ContinuousLinearMap.singularValue_comp_le_right _ _ j
        _ ≤ (K.sinThetaMap L).singularValue j * 1 := by
          gcongr
          exact_mod_cast (M n).starProjection_norm_le
        _ = _ := mul_one _
    exact_mod_cast hs
  apply le_antisymm
  · have hlsc : LowerSemicontinuous
        (fun A : E →L[ℂ] E => A.charbonnierCost tau) :=
      (ContinuousLinearMap.lowerSemicontinuous_charbonnierCost
        (𝕜 := ℂ) (E := E) (F := E)).comp
          (show Continuous (fun A : E →L[ℂ] E => (tau, A)) from
            continuous_const.prodMk continuous_id)
    exact (hlsc.isClosed_preimage (∑' j, f ((K.sinThetaMap L).singularValue j))).mem_of_tendsto
      (((continuous_const.sub continuous_id).tendsto _).comp hlim)
      (Eventually.of_forall (fun n => (heq n).trans_le (hdom n)))
  · exact sine_smoothedPhaseMinimum_sum_le_transport tau hτ K L R hmap

/-- The canonical rotation globally minimizes the smoothed objective
throughout the closed canonical gap regime, among all ambient unitary
transporters. Infinite extended costs are permitted. -/
theorem charbonnier_nonacuteDirectRotation_minimal_of_subcritical
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[ℂ] E))
    (hcut : K.projectionGap L ≤ Real.sin (smoothedCriticalAngle tau))
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    (1 - nonacuteDirectRotation K L J).charbonnierCost tau ≤
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau := by
  rw [charbonnier_nonacuteDirectRotation_eq_minimum_sum_of_subcritical tau hτ K L J hD hcut]
  exact sine_smoothedPhaseMinimum_sum_le_transport tau hτ K L U hmap

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
