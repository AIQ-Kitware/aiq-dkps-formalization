/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SmoothedPowerGlobalLowerBound
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerCanonicalCriterion
public import DavisKahan.Geometry.Polar.CanonicalApproximation
public import ForTauCeti.Analysis.InnerProductSpace.Projection.GapThreshold

/-!
# Canonical tails for the common spectral penalty family

Finite canonical restrictions, exact spectral sums and operator-norm lower
semicontinuity pass the finite canonical formula to compact subcritical
pairs. The proof adapts the classical approximation/geometry assembly in
`CharbonnierCanonicalTrace`, using the common family minimum and its angle
monotonicity rather than a penalty-specific closed formula.
Historical priority of the resulting family transport extension is unresolved.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPowerTransport

open FiniteDimensional.SmoothedPowerTransport Filter
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- An actual finite restriction of canonical rotation realizes the
intrinsic family minimum whenever all its angles are subcritical. -/
theorem canonical_restriction_eq_minimum_sum (p tau a : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (ha : a ∈ Set.Icc 0 (Real.pi / 2)) (hcrit : smoothedPowerCriticalCosine p tau ≤ Real.cos a)
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional ℂ M]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hacute : IsUniformlyAcute K L) (hcut : K.projectionGap L ≤ Real.sin a)
    (V : M ≃ₗᵢ[ℂ] M) (hV : ∀ x : M, (V x : E) = nonacuteDirectRotation K L J x)
    (hK : ∀ x ∈ M, K.starProjection x ∈ M) (hL : ∀ x ∈ M, L.starProjection x ∈ M) :
    (1 - (V : M →L[ℂ] M)).smoothedPowerCost p tau =
      ∑' j, ENNReal.ofReal (phaseMinimum p tau
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
  have hlocal := K.map_comap_subtype_of_isometry_restriction L M R V hmap hV
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
        nonacuteDirectRotation_restriction_eq_canonicalPolarFactor_of_acute K L M J V hV hK hz hz'
      _ = _ := (nonacuteDirectRotation_eq_canonicalPolarFactor_of_acute K₀ L₀
        (finiteCrossedDefectEquiv K₀ L₀ hdim) hz hz').symm
  have hmax : ∀ i : Fin (Module.finrank ℂ K₀), K₀.principalAngles L₀ i ≤ a := by
    apply (Submodule.finite_principalAngles_le_iff_directedProjectionGap_le K₀ L₀ a ha).mpr
    exact (K₀.directedProjectionGap_le_projectionGap L₀).trans
      ((K.projectionGap_comap_subtype_le_of_invariant L M hK hL).trans hcut)
  have hvalue : displacementCost p tau (V : M →L[ℂ] M) =
      ∑ i : Fin (Module.finrank ℂ K₀), phaseMinimum p tau (K₀.principalAngles L₀ i) := by
    rw [hcanonical, nonacuteDirectRotation_displacementCost_eq_sum p tau htau K₀ L₀ hdim]
    apply Finset.sum_congr rfl
    intro i _
    apply ((phaseMinimum_eq_canonical_iff p tau _ hp hp2 htau
      ⟨K₀.principalAngles_nonneg L₀ i, K₀.principalAngles_le_pi_div_two L₀ i⟩).mpr ?_).symm
    exact hcrit.trans (Real.antitoneOn_cos
      ⟨K₀.principalAngles_nonneg L₀ i, by linarith [K₀.principalAngles_le_pi_div_two L₀ i, Real.pi_pos]⟩
      ⟨ha.1, by linarith [ha.2, Real.pi_pos]⟩ (hmax i))
  rw [smoothedPowerCost_displacement_eq_ofReal p tau (by linarith) htau, hvalue,
    ENNReal.ofReal_sum_of_nonneg (fun (i : Fin (Module.finrank ℂ K₀)) _ =>
      phaseMinimum_nonneg p tau _ (by linarith) htau
      (K₀.principalAngles_nonneg L₀ i)),
    OperatorIdealFamily.tsum_singularValue_penalty_eq_sum _
      (fun s => ENNReal.ofReal (phaseMinimum p tau (Real.arcsin (s : ℝ))))
      (by simp only [NNReal.coe_zero, Real.arcsin_zero,
        phaseMinimum_zero p tau htau, ENNReal.ofReal_zero])]
  simp_rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]
  exact Submodule.sum_principalAngles_eq_sum_singularValues_arcsin K₀ L₀
    (fun t => ENNReal.ofReal (phaseMinimum p tau t))
    (by rw [phaseMinimum_zero p tau htau, ENNReal.ofReal_zero])

/-- Canonical finite truncations have the exact minimum sum of their
actual moving target pairs. No fixed-target approximation is asserted. -/
theorem canonical_truncation_eq_minimum_sum (p tau a : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (ha : a ∈ Set.Icc 0 (Real.pi / 2)) (hcrit : smoothedPowerCriticalCosine p tau ≤ Real.cos a)
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional ℂ M]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hacute : IsUniformlyAcute K L) (hcut : K.projectionGap L ≤ Real.sin a)
    (hRM : ∀ x ∈ M, nonacuteDirectRotation K L J x ∈ M)
    (hK : M.IsReducing K.starProjection.toLinearMap) (hL : M.IsReducing L.starProjection.toLinearMap)
    (V : E ≃ₗᵢ[ℂ] E) (hV : ∀ x ∈ M, V x = nonacuteDirectRotation K L J x)
    (hfix : ∀ x ∈ Mᗮ, V x = x) :
    (1 - (V : E →L[ℂ] E)).smoothedPowerCost p tau =
      ∑' j, ENNReal.ofReal (phaseMinimum p tau
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
      ((K.comap M.subtype).sinThetaMap (L.comap M.subtype)) ∘L M.orthogonalProjectionOnto := by
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
  rw [hdisp, ContinuousLinearMap.smoothedPowerCost_orthogonal_extension, hsin, hsinext]
  simp_rw [ContinuousLinearMap.singularValue_orthogonal_extension]
  exact canonical_restriction_eq_minimum_sum p tau a hp hp2 htau ha hcrit K L M J
    hacute hcut W hW hK.mem_invtSubmodule hL.mem_invtSubmodule

set_option maxHeartbeats 600000 in
-- Canonical approximation carries dependent finite subspaces and two spectral sums.
/-- **Exact canonical family minimum on compact subcritical pairs.**
No finite-cost or rank assumption is imposed; divergent costs are included.
The positive acute cutoff is arbitrary within the canonical regime. -/
theorem nonacuteDirectRotation_eq_minimum_sum_of_subcritical (p tau a : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hcrit : smoothedPowerCriticalCosine p tau ≤ Real.cos a)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[ℂ] E))
    (hcut : K.projectionGap L ≤ Real.sin a) :
    (1 - nonacuteDirectRotation K L J).smoothedPowerCost p tau =
      ∑' j, ENNReal.ofReal (phaseMinimum p tau
        (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) := by
  have hsin1 : Real.sin a < 1 := by
    have h := Real.strictMonoOn_sin
      ⟨by linarith [ha.1, Real.pi_pos], ha.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ ha.2
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
  let f (s : ℝ≥0) := ENNReal.ofReal (phaseMinimum p tau (Real.arcsin (s : ℝ)))
  have heq (n : ℕ) : (1 - (V n : E →L[ℂ] E)).smoothedPowerCost p tau =
      ∑' j, f ((S (V n)).singularValue j) := by
    let : FiniteDimensional ℂ (M n) := hM n
    rw [← hsin]
    exact canonical_truncation_eq_minimum_sum p tau a hp hp2 htau ⟨ha.1.le, ha.2.le⟩ hcrit
      K L (M n) J hacute hcut (hRM n) (hK n) (hL n) (V n) (hV n) (hfix n)
  have hdom (n : ℕ) : (∑' j, f ((S (V n)).singularValue j)) ≤
      ∑' j, f ((K.sinThetaMap L).singularValue j) := by
    let : FiniteDimensional ℂ (M n) := hM n
    rw [← hsin, K.sinThetaMap_map_truncation_eq_comp_starProjection L (M n) R (V n) hmap
      (hRM n) (hK n) (hL n) (hV n) (hfix n)]
    apply ENNReal.tsum_le_tsum
    intro j
    apply ENNReal.ofReal_le_ofReal
    apply monotoneOn_phaseMinimum_angle p tau (by linarith) htau
      ⟨Real.arcsin_nonneg.mpr (NNReal.coe_nonneg _), Real.arcsin_le_pi_div_two _⟩
      ⟨Real.arcsin_nonneg.mpr (NNReal.coe_nonneg _), Real.arcsin_le_pi_div_two _⟩
    apply Real.arcsin_le_arcsin
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
  · have hlsc := ContinuousLinearMap.lowerSemicontinuous_smoothedPowerCost
      (𝕜 := ℂ) (E := E) (F := E) p tau (by linarith)
    exact (hlsc.isClosed_preimage (∑' j, f ((K.sinThetaMap L).singularValue j))).mem_of_tendsto
      (((continuous_const.sub continuous_id).tendsto _).comp hlim)
      (Eventually.of_forall (fun n => (heq n).trans_le (hdom n)))
  · exact angle_minimum_sum_le_transport p tau hp hp2 htau K L R hmap

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPowerTransport
