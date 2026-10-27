/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.PairedPhase
public import ForTauCeti.Analysis.InnerProductSpace.Polar.Symmetry

/-!
# The nuclear transport dual on the entire Hilbert space

Complete the accepted polar factor of R-C by identity on its kernel.
It is unitary over either field, including infinite-dimensional fixed
sectors and right-angle defects. Its dual displacement is the intrinsic
sine plus a fixed-direction defect and a source-reflection-odd term.
The identity is algebraic and imposes no trace-class assumption.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The kernel of the skew part of completed direct rotation is the
full projection-difference kernel, over either field in arbitrary dimension. -/
theorem ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker =
      (K.starProjection - L.starProjection).ker := by
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  have hmod : B.modulus = (K.starProjection - L.starProjection).modulus :=
    Proposition35.modulus_nonacuteDirectRotation_sub_cosine K L D
  rw [← B.ker_modulus, hmod, ContinuousLinearMap.ker_modulus]

/-- Source reflection negates the entire skew part of completed
rotation by conjugation, without any compactness or acuteness hypothesis. -/
theorem reflection_conj_nonacuteDirectRotation_sub_cosine
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    K.reflection.conjStarAlgEquiv
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L) =
        -(nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L) := by
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  apply ContinuousLinearMap.ext
  intro x
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change K.reflection (B (K.reflection.symm x)) = -(B x)
  have h : B (K.reflection (K.reflection.symm x)) =
      -K.reflection (B (K.reflection.symm x)) :=
    nonacuteDirectRotation_skew_reflection K L D (K.reflection.symm x)
  rw [K.reflection.apply_symm_apply] at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

/-- The source-reflection-odd accepted polar phase of completed rotation. -/
theorem reflection_conj_polarFactor_nonacuteDirectRotation_sub_cosine
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    K.reflection.conjStarAlgEquiv
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).polarFactor =
        -(nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).polarFactor := by
  rw [ContinuousLinearMap.conjStarAlgEquiv_polarFactor,
    reflection_conj_nonacuteDirectRotation_sub_cosine,
    ContinuousLinearMap.polarFactor_neg]

/-- The actual full-space nuclear dual: polar quarter turn on the
moving sector and identity on all common fixed directions. -/
@[expose]
def nuclearTransportDual
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) : E ≃ₗᵢ[𝕜] E :=
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  Unitary.linearIsometryEquiv
    (⟨B.polarFactor + B.ker.starProjection,
      ContinuousLinearMap.polarFactor_add_ker_starProjection_mem_unitary_of_adjoint_eq_neg B
        (Proposition35.star_nonacuteDirectRotation_sub_cosine K L D)⟩ : unitary (E →L[𝕜] E))

/-- The cosine fixes the full kernel of the canonical skew part. -/
theorem cosine_apply_eq_self_of_mem_nonacute_skew_ker
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (x : E) (hx : x ∈
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker) :
    Proposition35.section3CosAngleOperator K L x = x := by
  have hproj := hx
  rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub] at hproj
  change K.starProjection x - L.starProjection x = 0 at hproj
  have hR := nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D x
    (sub_eq_zero.mp hproj)
  change nonacuteDirectRotation K L D x - Proposition35.section3CosAngleOperator K L x = 0 at hx
  exact (sub_eq_zero.mp hx).symm.trans hR

/-- **Exact nuclear dual displacement identity.** Its second term is
the fixed-sector defect, and its last term is reflection odd whenever
Z commutes with the source projection. No trace or summability is
assumed by this operator identity. -/
theorem nuclearTransportDual_adjoint_mul_displacement
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) (Z : E →L[𝕜] E) :
    let R := nonacuteDirectRotation K L D
    let C := Proposition35.section3CosAngleOperator K L
    let B := R - C
    let Q := B.ker.starProjection
    star (nuclearTransportDual K L D : E →L[𝕜] E) * (R - Z) =
      K.sinAngleOperator L + Q * (1 - Z) + star B.polarFactor * (C - Z) := by
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let B := R - C
  let Q := B.ker.starProjection
  let F := B.polarFactor
  have hC : IsSelfAdjoint C := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hQ : IsSelfAdjoint Q := isSelfAdjoint_starProjection B.ker
  have hCQ : C * Q = Q := by
    apply ContinuousLinearMap.ext
    intro x
    exact cosine_apply_eq_self_of_mem_nonacute_skew_ker K L D _ (B.ker.starProjection_apply_mem x)
  have hQC : Q * C = Q := by
    have h := congrArg star hCQ
    simpa only [star_mul, hC.star_eq, hQ.star_eq] using h
  have hBQ : B * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    exact B.ker.starProjection_apply_mem x
  have hQB : Q * B = 0 := by
    have hskew : star B = -B := Proposition35.star_nonacuteDirectRotation_sub_cosine K L D
    have h := congrArg star hBQ
    rw [star_mul, hQ.star_eq, hskew,
      mul_neg, star_zero] at h
    exact neg_eq_zero.mp h
  have hFB : star F * B = K.sinAngleOperator L := by
    have h := B.adjoint_polarFactor_comp
    change star F * B = B.modulus at h
    exact h.trans ((Proposition35.modulus_nonacuteDirectRotation_sub_cosine K L D).trans
      (by rw [Proposition35.section3SinAngleOperator, Submodule.sinAngleOperator_def]))
  have hdecomp : R - Z = B + (C - Z) := by dsimp only [B]; abel
  have hdefect : Q * (C - Z) = Q * (1 - Z) := by rw [mul_sub, mul_sub, hQC, mul_one]
  change star (F + Q) * (R - Z) = K.sinAngleOperator L + Q * (1 - Z) + star F * (C - Z)
  rw [star_add, hQ.star_eq, hdecomp, add_mul, mul_add, mul_add, hFB, hQB, zero_add, hdefect]
  abel

end TauCeti.DavisKahan
