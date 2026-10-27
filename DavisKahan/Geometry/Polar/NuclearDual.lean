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

/-- Completed direct rotation fixes the full skew-kernel projection. -/
theorem nonacuteDirectRotation_mul_skew_ker_projection
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
    nonacuteDirectRotation K L D * B.ker.starProjection = B.ker.starProjection := by
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  let Q := B.ker.starProjection
  ext x
  apply nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D
  have hx := B.ker.starProjection_apply_mem x
  change Q x ∈ B.ker at hx
  rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub] at hx
  exact sub_eq_zero.mp hx

/-- The real part of the completed nuclear dual is precisely the
full common-sector projection. -/
theorem nuclearTransportDual_add_star
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
    (nuclearTransportDual K L D : E →L[𝕜] E) +
      star (nuclearTransportDual K L D : E →L[𝕜] E) =
        B.ker.starProjection + B.ker.starProjection := by
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  have hF : star B.polarFactor = -B.polarFactor :=
    ContinuousLinearMap.adjoint_polarFactor_eq_neg_of_adjoint_eq_neg B
      (Proposition35.star_nonacuteDirectRotation_sub_cosine K L D)
  change (B.polarFactor + B.ker.starProjection) + star (B.polarFactor + B.ker.starProjection) = _
  rw [star_add, hF, (isSelfAdjoint_starProjection B.ker).star_eq]
  abel

/-- The completed nuclear dual removes the entire canonical skew
phase, giving the intrinsic positive sine. -/
theorem nuclearTransportDual_adjoint_mul_skew
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L) =
        K.sinAngleOperator L := by
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  let F := B.polarFactor
  let Q := B.ker.starProjection
  have hQ : IsSelfAdjoint Q := isSelfAdjoint_starProjection B.ker
  have hBQ : B * Q = 0 := by ext x; exact B.ker.starProjection_apply_mem x
  have hQB : Q * B = 0 := by
    have hB : star B = -B := Proposition35.star_nonacuteDirectRotation_sub_cosine K L D
    have h := congrArg star hBQ
    rw [star_mul, hQ.star_eq, hB, mul_neg, star_zero] at h
    exact neg_eq_zero.mp h
  have hFB : star F * B = K.sinAngleOperator L := by
    have h := B.adjoint_polarFactor_comp
    change star F * B = B.modulus at h
    exact h.trans ((Proposition35.modulus_nonacuteDirectRotation_sub_cosine K L D).trans
      (by rw [Proposition35.section3SinAngleOperator, Submodule.sinAngleOperator_def]))
  change star (F + Q) * B = _
  rw [star_add, hQ.star_eq, add_mul, hFB, hQB, add_zero]

/-- The actual nuclear dual commutes with completed direct rotation,
including on fixed directions and arbitrary right-angle completions. -/
theorem nonacuteDirectRotation_comm_nuclearTransportDual
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    Commute (nonacuteDirectRotation K L D) (nuclearTransportDual K L D : E →L[𝕜] E) := by
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let B := R - C
  let Q := B.ker.starProjection
  let R' := Unitary.linearIsometryEquiv
    (⟨R, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[𝕜] E))
  have hRC : Commute R C := Proposition35.nonacuteDirectRotation_comm_cosine K L D
  have hRB : Commute R B := (Commute.refl R).sub_right hRC
  have hRF : Commute R B.polarFactor := ContinuousLinearMap.commute_unitary_polarFactor B R' hRB
  have hRQ : R * Q = Q := nonacuteDirectRotation_mul_skew_ker_projection K L D
  have hQR : Q * R = Q := by
    have h := congrArg star hRQ
    rw [star_mul, (isSelfAdjoint_starProjection B.ker).star_eq] at h
    have h' := congrArg (fun A : E →L[𝕜] E => A * R) h
    rw [mul_assoc, Unitary.star_mul_self_of_mem (nonacuteDirectRotation_mem_unitary K L D), mul_one] at h'
    exact h'.symm
  have hRQcomm : Commute R Q := by change R * Q = Q * R; rw [hRQ, hQR]
  change Commute R (B.polarFactor + Q)
  exact hRF.add_right hRQcomm

/-- The cosine fixes the entire common-sector projection. -/
theorem cosine_mul_skew_ker_projection
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
    Proposition35.section3CosAngleOperator K L * B.ker.starProjection = B.ker.starProjection := by
  ext x
  exact cosine_apply_eq_self_of_mem_nonacute_skew_ker K L D _
    ((nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker.starProjection_apply_mem x)

/-- The actual dual fixes the entire common-sector projection. -/
theorem nuclearTransportDual_mul_skew_ker_projection
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
    (nuclearTransportDual K L D : E →L[𝕜] E) * B.ker.starProjection = B.ker.starProjection := by
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  have hFQ : B.polarFactor * B.ker.starProjection = 0 := by
    ext x
    exact B.polarFactor_apply_of_mem_ker (B.ker.starProjection_apply_mem x)
  change (B.polarFactor + B.ker.starProjection) * B.ker.starProjection = _
  rw [add_mul, hFQ, (isStarProjection_starProjection (U := B.ker)).isIdempotentElem.eq, zero_add]

/-- The nuclear dual preserves the intrinsic cosine, including its
zero and unit eigenspaces. -/
theorem nuclearTransportDual_comm_cosine
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    Commute (nuclearTransportDual K L D : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L) := by
  let R := nonacuteDirectRotation K L D
  let V := nuclearTransportDual K L D
  let C := Proposition35.section3CosAngleOperator K L
  have hVm : (V : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := (Unitary.linearIsometryEquiv.symm V).property
  have hVR : Commute (V : E →L[𝕜] E) R := (nonacuteDirectRotation_comm_nuclearTransportDual K L D).symm
  have hc := (commute_unitary_iff_star_right_conjugate hVm).mp hVR
  have hcs := congrArg star hc
  simp only [star_mul, star_star] at hcs
  have hVRs : Commute (V : E →L[𝕜] E) (star R) :=
    (commute_unitary_iff_star_right_conjugate hVm).mpr (by simpa only [mul_assoc] using hcs)
  have h := (hVR.add_right hVRs).eq
  have hsum : R + star R = C + C := nonacuteDirectRotation_add_star_eq_two_cosine K L D
  rw [hsum] at h
  change (V : E →L[𝕜] E) * C = C * (V : E →L[𝕜] E)
  apply smul_right_injective (E →L[𝕜] E) (by norm_num : (2 : 𝕜) ≠ 0)
  simpa only [two_smul, mul_add, add_mul] using h

/-- Reflection reverses the moving part of the dual and retains the
full common-sector projection. -/
theorem reflection_conj_nuclearTransportDual
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
    K.reflection.conjStarAlgEquiv (nuclearTransportDual K L D : E →L[𝕜] E) =
      -(nuclearTransportDual K L D : E →L[𝕜] E) + B.ker.starProjection + B.ker.starProjection := by
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  let F := B.polarFactor
  let Q := B.ker.starProjection
  have hF : K.reflection.conjStarAlgEquiv F = -F :=
    reflection_conj_polarFactor_nonacuteDirectRotation_sub_cosine K L D
  have hQformula : Q = 1 - star F * F := by
    have h := B.adjoint_polarFactor_comp_polarFactor
    change star F * F = B.kerᗮ.starProjection at h
    rw [Submodule.starProjection_orthogonal'] at h
    rw [h]
    abel
  have hQ : K.reflection.conjStarAlgEquiv Q = Q := by
    rw [hQformula, map_sub, map_one, map_mul, map_star, hF, star_neg, neg_mul, mul_neg, neg_neg]
  change K.reflection.conjStarAlgEquiv (F + Q) = -(F + Q) + Q + Q
  rw [map_add, hF, hQ]
  abel

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
