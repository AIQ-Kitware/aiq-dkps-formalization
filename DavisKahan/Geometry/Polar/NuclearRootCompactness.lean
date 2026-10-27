/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearRootMetric
public import ForTauCeti.Analysis.InnerProductSpace.CompactModulusFiber
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Topology

/-!
# Norm compactness of the complete nuclear optimizer family

Compact projection difference makes the independent signed-root set
compact. Finite native nuclear projection difference and balanced
crossed defects then make the entire ambient complex optimizer family
compact in the accepted operator norm topology. No separability or
finite-rank assumption is needed.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The independent signed-root set is closed in operator norm. -/
theorem isClosed_nuclearSignedSineParameters
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    IsClosed (nuclearSignedSineParameters K L D) := by
  let S := K.sinAngleOperator L
  let G := (nuclearTransportDual K L D : E →L[𝕜] E) * Proposition35.section3CosAngleOperator K L
  have hcomm : IsClosed {A : E →L[𝕜] E | Commute A G} := by
    change IsClosed {A : E →L[𝕜] E | A * G = G * A}
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hconj : Continuous (fun A : E →L[𝕜] E => K.reflection.conjStarAlgEquiv A) := by
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply]
    fun_prop
  have hodd : IsClosed {A : E →L[𝕜] E | K.reflection.conjStarAlgEquiv A = -A} :=
    isClosed_eq hconj continuous_neg
  have heq : nuclearSignedSineParameters K L D =
      {A : E →L[𝕜] E | IsSelfAdjoint A ∧ A.modulus = S} ∩
        ({A | Commute A G} ∩ {A | K.reflection.conjStarAlgEquiv A = -A}) := by
    ext A
    simp only [mem_nuclearSignedSineParameters, Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc, S, G]
  rw [heq]
  exact (TauCeti.isClosed_setOf_isSelfAdjoint_modulus_eq S
    (K.isPositive_sinAngleOperator L)).inter (hcomm.inter hodd)

/-- Compact projection difference makes all independent nuclear
signed roots norm compact over either field. The real set may be empty;
no real attainment or parity assertion is hidden in this statement. -/
theorem isCompact_nuclearSignedSineParameters
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection)) :
    IsCompact (nuclearSignedSineParameters K L D) := by
  let S := K.sinAngleOperator L
  have hScompact : IsCompactOperator S := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hsing : S.singularValue = (K.starProjection - L.starProjection).singularValue := by
      funext n
      rw [show S = (K.starProjection - L.starProjection).modulus from K.sinAngleOperator_def L,
        ContinuousLinearMap.singularValue_modulus]
    rw [hsing]
    exact hcompact.tendsto_singularValue
  apply (TauCeti.isCompact_setOf_isSelfAdjoint_modulus_eq S
    (K.isPositive_sinAngleOperator L) hScompact).of_isClosed_subset
      (isClosed_nuclearSignedSineParameters K L D)
  intro A hA
  have hp := (mem_nuclearSignedSineParameters K L D A).mp hA
  exact ⟨hp.1, hp.2.1⟩

section Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The full nuclear optimizer coefficients form a norm-compact set.**
The ambient space may be nonseparable, with infinite-rank projection
perturbation and infinite-dimensional common fixed directions. -/
theorem isCompact_nuclear_optimizer_coefficients_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞) :
    IsCompact ((fun T : F ≃ₗᵢ[ℂ] F => (T : F →L[ℂ] F)) '' nuclearTransportOptimizers K L) := by
  have hcompact := ContinuousLinearMap.isCompactOperator_of_nuclearENorm_ne_top hΔ
  have hroots := isCompact_nuclearSignedSineParameters K L D hcompact
  let : CompactSpace (nuclearSignedSineParameters K L D) := isCompact_iff_compactSpace.mp hroots
  let e := nuclearSignedSineEquivOptimizers_complex K L D hΔ
  let f (A : nuclearSignedSineParameters K L D) : F →L[ℂ] F := (e A).val
  have hf : Continuous f := (nuclearSignedSineEquivOptimizers_isometry_complex K L D hΔ).continuous
  have hrange : IsCompact (Set.range f) := isCompact_range hf
  have heq : Set.range f =
      (fun T : F ≃ₗᵢ[ℂ] F => (T : F →L[ℂ] F)) '' nuclearTransportOptimizers K L := by
    ext A
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨(e B).val, (e B).property, rfl⟩
    · rintro ⟨T, hT, rfl⟩
      refine ⟨e.symm ⟨T, hT⟩, ?_⟩
      change ((e (e.symm ⟨T, hT⟩)).val : F →L[ℂ] F) = (T : F →L[ℂ] F)
      rw [e.apply_symm_apply]
  rwa [heq] at hrange

/-- **The complete complex nuclear optimizer family is norm compact.**
This uses the accepted operator norm topology on actual unitary maps,
not the strong topology or an unspecified topology on a parameter set. -/
theorem isCompact_nuclearTransportOptimizers_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞) :
    IsCompact (nuclearTransportOptimizers K L) := by
  apply LinearIsometryEquiv.isEmbedding_toContinuousLinearMap.isCompact_iff.mpr
  exact isCompact_nuclear_optimizer_coefficients_complex K L D hΔ

/-- Balanced crossed defects give a nonempty ambient nuclear optimizer
set over the complex field. This statement includes infinite costs. -/
theorem nuclearTransportOptimizers_nonempty_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    (nuclearTransportOptimizers K L).Nonempty := by
  refine ⟨nuclearPhaseRotation_complex K L D, (mem_nuclearTransportOptimizers K L _).mpr
    ⟨nuclearPhaseRotation_map_complex K L D, ?_⟩⟩
  intro U hU
  have h := nuclearPhaseRotation_isMin_complex K L D U hU
  simpa only [OperatorIdealFamily.gauge_schatten, one_div_one, ENNReal.rpow_one,
    ContinuousLinearMap.nuclearENorm_def] using h

/-- **Attainment of a secondary objective while preserving the exact
nuclear optimum.** Every lower semicontinuous extended nonnegative
objective has a minimizer on the full ambient optimizer family. -/
theorem exists_secondary_minimizer_nuclear_transport_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (f : (F ≃ₗᵢ[ℂ] F) → ℝ≥0∞)
    (hf : LowerSemicontinuousOn f (nuclearTransportOptimizers K L)) :
    ∃ T ∈ nuclearTransportOptimizers K L,
      ∀ U ∈ nuclearTransportOptimizers K L, f T ≤ f U := by
  obtain ⟨T, hT, hmin⟩ := hf.exists_isMinOn (nuclearTransportOptimizers_nonempty_complex K L D)
    (isCompact_nuclearTransportOptimizers_complex K L D hΔ)
  exact ⟨T, hT, hmin⟩

/-- **Reference alignment within the exact nuclear-optimal family.**
For every Schatten exponent q at least one and every bounded reference
B, a nuclear optimizer minimizing its Schatten distance to B exists.
No performance, uniqueness or statistical assertion is implied. -/
theorem exists_nearest_reference_nuclear_optimizer_schatten_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (q : ℝ) (hq : 1 ≤ q) (B : F →L[ℂ] F) :
    ∃ T ∈ nuclearTransportOptimizers K L, ∀ U ∈ nuclearTransportOptimizers K L,
      (OperatorIdealFamily.schatten ℂ q hq).gauge ((T : F →L[ℂ] F) - B) ≤
        (OperatorIdealFamily.schatten ℂ q hq).gauge ((U : F →L[ℂ] F) - B) := by
  have hc : Continuous (fun T : F ≃ₗᵢ[ℂ] F => (T : F →L[ℂ] F) - B) :=
    LinearIsometryEquiv.isEmbedding_toContinuousLinearMap.continuous.sub continuous_const
  have hl : LowerSemicontinuous (fun T : F ≃ₗᵢ[ℂ] F =>
      (OperatorIdealFamily.schatten ℂ q hq).gauge ((T : F →L[ℂ] F) - B)) :=
    (OperatorIdealFamily.lowerSemicontinuous_gauge_schatten q hq).comp hc
  exact exists_secondary_minimizer_nuclear_transport_complex K L D hΔ _ (hl.lowerSemicontinuousOn _)

/-- A reference differing from identity by a Schatten-q operator
admits a finite-distance best match within the exact nuclear-optimal
family. This is a nonvacuous secondary optimization theorem. -/
theorem exists_finite_nearest_reference_nuclear_optimizer_schatten_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (q : ℝ) (hq : 1 ≤ q) (B : F →L[ℂ] F)
    (hB : (OperatorIdealFamily.schatten ℂ q hq).gauge (1 - B) ≠ ∞) :
    ∃ T ∈ nuclearTransportOptimizers K L,
      (OperatorIdealFamily.schatten ℂ q hq).gauge ((T : F →L[ℂ] F) - B) ≠ ∞ ∧
        ∀ U ∈ nuclearTransportOptimizers K L,
          (OperatorIdealFamily.schatten ℂ q hq).gauge ((T : F →L[ℂ] F) - B) ≤
            (OperatorIdealFamily.schatten ℂ q hq).gauge ((U : F →L[ℂ] F) - B) := by
  obtain ⟨T, hT, hmin⟩ := exists_nearest_reference_nuclear_optimizer_schatten_complex K L D hΔ q hq B
  refine ⟨T, hT, ?_, hmin⟩
  have hp := (mem_nuclearTransportOptimizers K L T).mp hT
  have hfinite := ((nuclear_isMin_iff_certificate_complex K L D hΔ T hp.1).mp hp.2).1
  have hPhi1 : (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
      (1 - (T : F →L[ℂ] F)) ≠ ∞ := by
    simpa only [OperatorIdealFamily.gauge_schatten, one_div_one, ENNReal.rpow_one,
      ContinuousLinearMap.nuclearENorm_def] using hfinite
  let Φ := OperatorIdealFamily.schatten ℂ q hq
  have hPhiq : Φ.gauge (1 - (T : F →L[ℂ] F)) ≠ ∞ :=
    ne_top_of_le_ne_top hPhi1
      (OperatorIdealFamily.gauge_schatten_le_of_le (by norm_num : (1 : ℝ) ≤ 1) hq hq _)
  have hneg : Φ.gauge ((T : F →L[ℂ] F) - 1) ≠ ∞ := by
    rw [← neg_sub 1 (T : F →L[ℂ] F), Φ.gauge_neg]
    exact hPhiq
  have hsub : (T : F →L[ℂ] F) - B = ((T : F →L[ℂ] F) - 1) + (1 - B) := by abel
  change Φ.gauge ((T : F →L[ℂ] F) - B) ≠ ∞
  rw [hsub]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hneg, hB⟩) (Φ.gauge_add_le _ _)

end Complex

end TauCeti.DavisKahan
