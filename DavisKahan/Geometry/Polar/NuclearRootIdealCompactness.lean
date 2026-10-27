/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearRootCompactness
public import DavisKahan.Geometry.Polar.NuclearRootProfile
public import ForTauCeti.Analysis.InnerProductSpace.CompactModulusIdeal

/-!
# Compactness of nuclear optimizers in ideal norms

The signed-root set is compact in every Schatten norm containing the
projection difference. For trace-class projection difference the full
complex optimizer displacement set is compact in every Schatten-q norm,
including the nuclear norm itself. All carriers are the accepted Tau
Ceti ideal carriers.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The independent signed-root family is compact in the native Schatten
norm whenever the projection difference belongs to that ideal. This
statement also applies over the reals, where the root set may be empty. -/
theorem isCompact_nuclearSignedSineParameters_schatten
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (q : ℝ) (hq : 1 ≤ q)
    (hΔ : (OperatorIdealFamily.schatten 𝕜 q hq).gauge
      (K.starProjection - L.starProjection) ≠ ∞) :
    IsCompact {A : ((OperatorIdealFamily.schatten 𝕜 q hq).operatorGauge E E).Carrier |
      A.toContinuousLinearMap ∈ nuclearSignedSineParameters K L D} := by
  let Φ := OperatorIdealFamily.schatten 𝕜 q hq
  have hS : Φ.gauge (K.sinAngleOperator L) ≠ ∞ := by
    have heq := (SymmetricOperatorIdealFamily.schatten 𝕜 q hq).gauge_modulus_eq
      (K.starProjection - L.starProjection)
    change (SymmetricOperatorIdealFamily.schatten 𝕜 q hq).toOperatorIdealFamily.gauge _ =
      (SymmetricOperatorIdealFamily.schatten 𝕜 q hq).toOperatorIdealFamily.gauge _ at heq
    rw [SymmetricOperatorIdealFamily.schatten_toOperatorIdealFamily] at heq
    rwa [Submodule.sinAngleOperator_def, heq]
  apply (TauCeti.isCompact_setOf_isSelfAdjoint_modulus_eq_schatten q hq
    (K.sinAngleOperator L) (K.isPositive_sinAngleOperator L) hS).of_isClosed_subset
  · convert (isClosed_nuclearSignedSineParameters K L D).preimage
      (OperatorGauge.Carrier.toContinuousLinearMapL (Φ.operatorGauge E E)).continuous using 1
    ext A
    simp only [Set.mem_preimage, Set.mem_ofPred_eq,
      OperatorGauge.Carrier.toContinuousLinearMapL_apply]
  · intro A hA
    have hp := (mem_nuclearSignedSineParameters K L D A.toContinuousLinearMap).mp hA
    exact ⟨hp.1, hp.2.1⟩

section Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Ideal-norm compactness of every nuclear optimizer.** The displacement
operators of the full ambient optimizer family form a compact subset of
the native Schatten-q carrier for every q at least one. In particular
this proves compactness in nuclear distance, without finite rank or
separability assumptions. -/
theorem isCompact_nuclear_optimizer_displacements_schatten_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (q : ℝ) (hq : 1 ≤ q) :
    IsCompact {B : ((OperatorIdealFamily.schatten ℂ q hq).operatorGauge F F).Carrier |
      ∃ T ∈ nuclearTransportOptimizers K L,
        B.toContinuousLinearMap = 1 - (T : F →L[ℂ] F)} := by
  let Φ := OperatorIdealFamily.schatten ℂ q hq
  have hΔone : (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞ := by
    simpa only [OperatorIdealFamily.gauge_schatten, one_div_one, ENNReal.rpow_one,
      ContinuousLinearMap.nuclearENorm_def] using hΔ
  have hΔq : Φ.gauge (K.starProjection - L.starProjection) ≠ ∞ :=
    ne_top_of_le_ne_top hΔone
      (OperatorIdealFamily.gauge_schatten_le_of_le (by norm_num : (1 : ℝ) ≤ 1) hq hq _)
  let X := {A : (Φ.operatorGauge F F).Carrier |
    A.toContinuousLinearMap ∈ nuclearSignedSineParameters K L D}
  let : CompactSpace X := isCompact_iff_compactSpace.mp
    (isCompact_nuclearSignedSineParameters_schatten K L D q hq hΔq)
  let root (A : X) : nuclearSignedSineParameters K L D :=
    ⟨A.val.toContinuousLinearMap, A.property⟩
  let e := nuclearSignedSineEquivOptimizers_complex K L D hΔ
  let t (A : X) : F ≃ₗᵢ[ℂ] F := (e (root A)).val
  have ht (A : X) : t A ∈ nuclearTransportOptimizers K L := (e (root A)).property
  have hfinite (A : X) : Φ.gauge (1 - (t A : F →L[ℂ] F)) ≠ ∞ := by
    rw [nuclear_optimizer_schatten_profile_complex q hq K L D hΔ ⟨t A, ht A⟩]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by have h := (div_le_one (by linarith : 0 < q)).mpr hq; linarith)
      (by norm_num)) hΔq
  let f : X → (Φ.operatorGauge F F).Carrier := fun A =>
    ⟨1 - (t A : F →L[ℂ] F), by
      simpa only [OperatorGauge.mem_finiteSubmodule, OperatorIdealFamily.operatorGauge_apply]
        using lt_top_iff_ne_top.mpr (hfinite A)⟩
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro A B
    simp only [Subtype.dist_eq, dist_eq_norm]
    rw [OperatorGauge.Carrier.norm_def, OperatorGauge.Carrier.toContinuousLinearMap_sub,
      OperatorIdealFamily.operatorGauge_apply]
    change (Φ.gauge ((1 - (t A : F →L[ℂ] F)) -
      (1 - (t B : F →L[ℂ] F)))).toReal = ‖A.val - B.val‖
    rw [show (1 - (t A : F →L[ℂ] F)) - (1 - (t B : F →L[ℂ] F)) =
      (t B : F →L[ℂ] F) - (t A : F →L[ℂ] F) from by abel]
    have hA := (mem_nuclearSignedSineParameters K L D _).mp A.property
    have hB := (mem_nuclearSignedSineParameters K L D _).mp B.property
    have heq := nuclearSignedSineTransport_gauge_sub
      (SymmetricOperatorIdealFamily.schatten ℂ q hq) K L D
      B.val.toContinuousLinearMap A.val.toContinuousLinearMap
      hB.1 hB.2.1 hB.2.2.1 hA.1 hA.2.1 hA.2.2.1
    change (SymmetricOperatorIdealFamily.schatten ℂ q hq).toOperatorIdealFamily.gauge _ =
      (SymmetricOperatorIdealFamily.schatten ℂ q hq).toOperatorIdealFamily.gauge _ at heq
    rw [SymmetricOperatorIdealFamily.schatten_toOperatorIdealFamily] at heq
    change Φ.gauge ((t B : F →L[ℂ] F) - (t A : F →L[ℂ] F)) =
      Φ.gauge (B.val.toContinuousLinearMap - A.val.toContinuousLinearMap) at heq
    rw [heq, ← OperatorIdealFamily.operatorGauge_apply,
      ← OperatorGauge.Carrier.toContinuousLinearMap_sub,
      ← OperatorGauge.Carrier.norm_def, norm_sub_rev]
  have hrange : Set.range f = {B : (Φ.operatorGauge F F).Carrier |
      ∃ T ∈ nuclearTransportOptimizers K L,
        B.toContinuousLinearMap = 1 - (T : F →L[ℂ] F)} := by
    ext B
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨t A, ht A, rfl⟩
    · rintro ⟨T, hT, hB⟩
      let A := e.symm ⟨T, hT⟩
      have hAfinite : Φ.gauge A.val ≠ ∞ := by
        have heq := nuclearSignedSineParameters_gauge
          (SymmetricOperatorIdealFamily.schatten ℂ q hq) K L D A
        change (SymmetricOperatorIdealFamily.schatten ℂ q hq).toOperatorIdealFamily.gauge _ =
          (SymmetricOperatorIdealFamily.schatten ℂ q hq).toOperatorIdealFamily.gauge _ at heq
        rw [SymmetricOperatorIdealFamily.schatten_toOperatorIdealFamily] at heq
        change Φ.gauge A.val = Φ.gauge (K.starProjection - L.starProjection) at heq
        rwa [heq]
      let a : X := ⟨⟨A.val, by simpa only [OperatorGauge.mem_finiteSubmodule,
        OperatorIdealFamily.operatorGauge_apply] using lt_top_iff_ne_top.mpr hAfinite⟩, A.property⟩
      refine ⟨a, OperatorGauge.Carrier.ext ?_⟩
      change 1 - ((e A).val : F →L[ℂ] F) = B.toContinuousLinearMap
      rw [e.apply_symm_apply, hB]
  rw [← hrange]
  exact isCompact_range hf.continuous

end Complex

end TauCeti.DavisKahan
