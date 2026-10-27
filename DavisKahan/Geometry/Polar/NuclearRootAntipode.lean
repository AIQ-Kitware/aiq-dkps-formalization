/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearRootMetric
public import ForTauCeti.Analysis.OperatorIdeal.Family.Modulus

/-!
# Antipodal geometry of all complex nuclear minimizers

Root negation induces an involution of the entire optimizer family.
It attains the universal sharp pairwise gauge bound for every symmetric
operator ideal simultaneously, including infinite gauge values.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The independent parameter set is closed under negation. -/
theorem neg_mem_nuclearSignedSineParameters
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : A ∈ nuclearSignedSineParameters K L D) :
    -A ∈ nuclearSignedSineParameters K L D := by
  obtain ⟨hself, hmod, hcomm, hodd⟩ := (mem_nuclearSignedSineParameters K L D A).mp hA
  apply (mem_nuclearSignedSineParameters K L D (-A)).mpr
  refine ⟨hself.neg, by rw [ContinuousLinearMap.modulus_neg, hmod], hcomm.neg_left, ?_⟩
  rw [map_neg, hodd, neg_neg]

/-- Root negation as an actual equivalence of the independent parameters. -/
@[expose]
def nuclearSignedSineNegEquiv
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    nuclearSignedSineParameters K L D ≃ nuclearSignedSineParameters K L D where
  toFun A := ⟨-A.val, neg_mem_nuclearSignedSineParameters K L D A.val A.property⟩
  invFun A := ⟨-A.val, neg_mem_nuclearSignedSineParameters K L D A.val A.property⟩
  left_inv A := by apply Subtype.ext; exact neg_neg A.val
  right_inv A := by apply Subtype.ext; exact neg_neg A.val

/-- Every root has the same gauge as the projection difference, for
every symmetric ideal family. No finite-gauge hypothesis is required. -/
theorem nuclearSignedSineParameters_gauge
    (Φ : SymmetricOperatorIdealFamily 𝕜)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : nuclearSignedSineParameters K L D) :
    Φ.gauge A.val = Φ.gauge (K.starProjection - L.starProjection) := by
  have hmod := ((mem_nuclearSignedSineParameters K L D A.val).mp A.property).2.1
  calc
    _ = Φ.gauge A.val.modulus := (Φ.gauge_modulus_eq A.val).symm
    _ = Φ.gauge (K.sinAngleOperator L) := congrArg Φ.gauge hmod
    _ = _ := by rw [Submodule.sinAngleOperator_def]; exact Φ.gauge_modulus_eq _

/-- The universal sharp upper bound on parameter differences in every
symmetric ideal gauge, allowing infinite values. -/
theorem nuclearSignedSineParameters_gauge_sub_le
    (Φ : SymmetricOperatorIdealFamily 𝕜)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A B : nuclearSignedSineParameters K L D) :
    Φ.gauge (A.val - B.val) ≤ 2 * Φ.gauge (K.starProjection - L.starProjection) := by
  rw [sub_eq_add_neg]
  calc
    _ ≤ Φ.gauge A.val + Φ.gauge (-B.val) := Φ.gauge_add_le _ _
    _ = _ := by
      rw [Φ.toOperatorIdealFamily.gauge_neg, nuclearSignedSineParameters_gauge Φ K L D A,
        nuclearSignedSineParameters_gauge Φ K L D B, two_mul]

/-- Root negation attains the sharp pairwise gauge bound simultaneously
for every symmetric ideal family. -/
theorem nuclearSignedSineParameters_gauge_antipode
    (Φ : SymmetricOperatorIdealFamily 𝕜)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : nuclearSignedSineParameters K L D) :
    Φ.gauge (A.val - (nuclearSignedSineNegEquiv K L D A).val) =
      2 * Φ.gauge (K.starProjection - L.starProjection) := by
  change Φ.gauge (A.val - -A.val) = _
  rw [sub_neg_eq_add, ← two_smul 𝕜 A.val, Φ.gauge_smul]
  have htwo : ‖(2 : 𝕜)‖ₑ = (2 : ℝ≥0∞) := by rw [← ofReal_norm, RCLike.norm_ofNat]; norm_num
  rw [htwo, nuclearSignedSineParameters_gauge Φ K L D A]

section Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The antipode of the full optimizer family, induced by exact
signed-root negation. Its coefficient formula identifies its intrinsic
center independently of the auxiliary crossed-defect completion. -/
@[expose]
def nuclearOptimizerAntipode_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞) :
    nuclearTransportOptimizers K L ≃ nuclearTransportOptimizers K L :=
  (nuclearSignedSineEquivOptimizers_complex K L D hΔ).symm.trans
    ((nuclearSignedSineNegEquiv K L D).trans (nuclearSignedSineEquivOptimizers_complex K L D hΔ))

/-- The optimizer antipode negates its exact extracted root. -/
@[simp]
theorem nuclearOptimizerAntipode_extract_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L) :
    ((nuclearSignedSineEquivOptimizers_complex K L D hΔ).symm
      (nuclearOptimizerAntipode_complex K L D hΔ T)).val =
        -((nuclearSignedSineEquivOptimizers_complex K L D hΔ).symm T).val := by
  let e := nuclearSignedSineEquivOptimizers_complex K L D hΔ
  change (e.symm (e (nuclearSignedSineNegEquiv K L D (e.symm T)))).val = _
  rw [e.symm_apply_apply]
  rfl

/-- The antipode is an involution on all ambient nuclear minimizers. -/
theorem nuclearOptimizerAntipode_involutive_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞) :
    Function.Involutive (nuclearOptimizerAntipode_complex K L D hΔ) := by
  intro T
  apply (nuclearSignedSineEquivOptimizers_complex K L D hΔ).symm.injective
  apply Subtype.ext
  rw [nuclearOptimizerAntipode_extract_complex, nuclearOptimizerAntipode_extract_complex, neg_neg]

/-- Every pair of global optimizers satisfies the sharp gauge bound. -/
theorem nuclear_optimizers_gauge_sub_le_complex
    (Φ : SymmetricOperatorIdealFamily ℂ)
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T U : nuclearTransportOptimizers K L) :
    Φ.gauge ((T.val : F →L[ℂ] F) - (U.val : F →L[ℂ] F)) ≤
      2 * Φ.gauge (K.starProjection - L.starProjection) := by
  let e := nuclearSignedSineEquivOptimizers_complex K L D hΔ
  let A := e.symm T
  let B := e.symm U
  have hpA := (mem_nuclearSignedSineParameters K L D A.val).mp A.property
  have hpB := (mem_nuclearSignedSineParameters K L D B.val).mp B.property
  have hm := nuclearSignedSineTransport_gauge_sub Φ K L D A.val B.val
    hpA.1 hpA.2.1 hpA.2.2.1 hpB.1 hpB.2.1 hpB.2.2.1
  change Φ.gauge (((e A).val : F →L[ℂ] F) - ((e B).val : F →L[ℂ] F)) = Φ.gauge (A.val - B.val) at hm
  have hAT : e A = T := e.apply_symm_apply T
  have hBU : e B = U := e.apply_symm_apply U
  rw [hAT, hBU] at hm
  rw [hm]
  exact nuclearSignedSineParameters_gauge_sub_le Φ K L D A B

/-- Every optimizer has a partner attaining the universal maximum
separation in every symmetric ideal gauge simultaneously. -/
theorem nuclearOptimizerAntipode_gauge_complex
    (Φ : SymmetricOperatorIdealFamily ℂ)
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L) :
    Φ.gauge ((T.val : F →L[ℂ] F) - ((nuclearOptimizerAntipode_complex K L D hΔ T).val : F →L[ℂ] F)) =
      2 * Φ.gauge (K.starProjection - L.starProjection) := by
  let e := nuclearSignedSineEquivOptimizers_complex K L D hΔ
  let A := e.symm T
  let B := nuclearSignedSineNegEquiv K L D A
  have hpA := (mem_nuclearSignedSineParameters K L D A.val).mp A.property
  have hpB := (mem_nuclearSignedSineParameters K L D B.val).mp B.property
  have hm := nuclearSignedSineTransport_gauge_sub Φ K L D A.val B.val
    hpA.1 hpA.2.1 hpA.2.2.1 hpB.1 hpB.2.1 hpB.2.2.1
  change Φ.gauge (((e A).val : F →L[ℂ] F) - ((e B).val : F →L[ℂ] F)) = Φ.gauge (A.val - B.val) at hm
  have hAT : e A = T := e.apply_symm_apply T
  have hBU : e B = nuclearOptimizerAntipode_complex K L D hΔ T := rfl
  rw [hAT, hBU] at hm
  exact hm.trans (nuclearSignedSineParameters_gauge_antipode Φ K L D A)

/-- The operator-norm separation of every optimizer from its antipode
is exactly twice the projection gap. -/
theorem nuclearOptimizerAntipode_norm_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L) :
    ‖(T.val : F →L[ℂ] F) - ((nuclearOptimizerAntipode_complex K L D hΔ T).val : F →L[ℂ] F)‖ =
      2 * ‖K.starProjection - L.starProjection‖ := by
  have h := nuclearOptimizerAntipode_gauge_complex (SymmetricOperatorIdealFamily.opNorm ℂ) K L D hΔ T
  change (SymmetricOperatorIdealFamily.opNorm ℂ).toOperatorIdealFamily.gauge _ =
    2 * (SymmetricOperatorIdealFamily.opNorm ℂ).toOperatorIdealFamily.gauge _ at h
  rw [SymmetricOperatorIdealFamily.opNorm_toOperatorIdealFamily] at h
  simp only [OperatorIdealFamily.gauge_opNorm] at h
  simpa using congrArg ENNReal.toReal h

/-- No pair of optimizers can exceed the separation attained by the
antipode in operator norm. -/
theorem nuclear_optimizers_norm_sub_le_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T U : nuclearTransportOptimizers K L) :
    ‖(T.val : F →L[ℂ] F) - (U.val : F →L[ℂ] F)‖ ≤ 2 * ‖K.starProjection - L.starProjection‖ := by
  have h := nuclear_optimizers_gauge_sub_le_complex (SymmetricOperatorIdealFamily.opNorm ℂ) K L D hΔ T U
  change (SymmetricOperatorIdealFamily.opNorm ℂ).toOperatorIdealFamily.gauge _ ≤
    2 * (SymmetricOperatorIdealFamily.opNorm ℂ).toOperatorIdealFamily.gauge _ at h
  rw [SymmetricOperatorIdealFamily.opNorm_toOperatorIdealFamily] at h
  simp only [OperatorIdealFamily.gauge_opNorm] at h
  have hfinite : (2 : ℝ≥0∞) * ‖K.starProjection - L.starProjection‖ₑ ≠ ∞ := by finiteness
  simpa using ENNReal.toReal_mono hfinite h

/-- **Intrinsic center of the complete nuclear optimizer family.**
Every optimizer and its antipode have the canonical intertwiner as
midpoint. The center is independent of the crossed-defect completion. -/
theorem nuclearOptimizerAntipode_sum_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L) :
    (T.val : F →L[ℂ] F) + ((nuclearOptimizerAntipode_complex K L D hΔ T).val : F →L[ℂ] F) =
      spectraCanonicalIntertwiner K L + spectraCanonicalIntertwiner K L := by
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let V := nuclearTransportDual K L D
  let U := nuclearOptimizerAntipode_complex K L D hΔ T
  have hroot := nuclearOptimizerAntipode_extract_complex K L D hΔ T
  rw [nuclearSignedSineEquivOptimizers_symm_apply_complex,
    nuclearSignedSineEquivOptimizers_symm_apply_complex] at hroot
  have hVm : (V : F →L[ℂ] F) ∈ unitary (F →L[ℂ] F) := (Unitary.linearIsometryEquiv.symm V).property
  have h := congrArg (fun A : F →L[ℂ] F => (V : F →L[ℂ] F) * A) hroot
  change (V : F →L[ℂ] F) * (star (V : F →L[ℂ] F) * ((U.val.symm : F →L[ℂ] F) * R - C)) =
    (V : F →L[ℂ] F) * -(star (V : F →L[ℂ] F) * ((T.val.symm : F →L[ℂ] F) * R - C)) at h
  rw [mul_neg, ← mul_assoc, ← mul_assoc, Unitary.mul_star_self_of_mem hVm, one_mul, one_mul] at h
  have hC : IsSelfAdjoint C := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hs := congrArg star h
  simp only [star_sub, star_mul, star_neg, hC.star_eq,
    LinearIsometryEquiv.star_eq_symm, LinearIsometryEquiv.symm_symm] at hs
  rw [neg_sub] at hs
  have hsum : star R * (U.val : F →L[ℂ] F) + star R * (T.val : F →L[ℂ] F) = C + C :=
    sub_eq_sub_iff_add_eq_add.mp hs
  have hsum' : star R * ((T.val : F →L[ℂ] F) + (U.val : F →L[ℂ] F)) = C + C := by
    rw [mul_add, add_comm]
    exact hsum
  have hr := congrArg (fun A : F →L[ℂ] F => R * A) hsum'
  have hRm : R ∈ unitary (F →L[ℂ] F) := nonacuteDirectRotation_mem_unitary K L D
  have hcenter : R * C = spectraCanonicalIntertwiner K L :=
    nonacuteDirectRotation_mul_cosine_eq_canonicalIntertwiner K L D
  rw [← mul_assoc, Unitary.mul_star_self_of_mem hRm, one_mul, mul_add, hcenter] at hr
  exact hr

/-- The antipodal optimizer has an intrinsic affine coefficient formula. -/
theorem nuclearOptimizerAntipode_coefficient_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L) :
    ((nuclearOptimizerAntipode_complex K L D hΔ T).val : F →L[ℂ] F) =
      spectraCanonicalIntertwiner K L + spectraCanonicalIntertwiner K L - (T.val : F →L[ℂ] F) := by
  rw [← nuclearOptimizerAntipode_sum_complex K L D hΔ T]
  abel

/-- Every nuclear optimizer lies on the same sphere about the
canonical intertwiner in every symmetric ideal gauge simultaneously.
The formula includes infinite values and has no dimension restriction. -/
theorem nuclear_optimizers_gauge_radius_complex
    (Φ : SymmetricOperatorIdealFamily ℂ)
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L) :
    Φ.gauge ((T.val : F →L[ℂ] F) - spectraCanonicalIntertwiner K L) =
      Φ.gauge (K.starProjection - L.starProjection) := by
  have hhalf : (T.val : F →L[ℂ] F) - spectraCanonicalIntertwiner K L =
      (1 / 2 : ℂ) • ((T.val : F →L[ℂ] F) -
        ((nuclearOptimizerAntipode_complex K L D hΔ T).val : F →L[ℂ] F)) := by
    rw [nuclearOptimizerAntipode_coefficient_complex]
    module
  rw [hhalf, Φ.gauge_smul, nuclearOptimizerAntipode_gauge_complex Φ K L D hΔ T]
  have hnorm : ‖(1 / 2 : ℂ)‖ₑ = (2 : ℝ≥0∞)⁻¹ := by
    rw [← ofReal_norm]
    simp only [norm_div, norm_one, RCLike.norm_ofNat]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hnorm, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]

/-- The antipode itself is independent of every auxiliary choice of
isometric identification of the right-angle crossed defects. -/
theorem nuclearOptimizerAntipode_independent_defect_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D D' : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L) :
    nuclearOptimizerAntipode_complex K L D hΔ T = nuclearOptimizerAntipode_complex K L D' hΔ T := by
  apply Subtype.ext
  ext x
  have h := (nuclearOptimizerAntipode_coefficient_complex K L D hΔ T).trans
    (nuclearOptimizerAntipode_coefficient_complex K L D' hΔ T).symm
  exact congrArg (fun A : F →L[ℂ] F => A x) h

end Complex

end TauCeti.DavisKahan
