/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.Geometry.Angle.Proposition35Nonacute
import ForTauCeti.Analysis.InnerProductSpace.Projection.CompressionRealPart
import TauCeti.Analysis.InnerProductSpace.Projection.Block

/-!
# The diagonal compressions of the canonical nonacute rotation

Each diagonal compression equals the corresponding compression of `cos Θ`.
Its Gram operator already equals the square of that positive real part,
forcing its skew part to vanish. Consequently reflection in the source
subspace reverses the entire skew part of the nonacute rotation.
-/

noncomputable section

namespace TauCeti.DavisKahan

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

private theorem compression_eq_of_transport_gram
    (P Q R C : H →L[𝕜] H) (hP : IsStarProjection P)
    (hunit : R ∈ unitary (H →L[𝕜] H)) (hC : IsSelfAdjoint C)
    (hskew : star (R - C) = -(R - C)) (hCP : Commute C P) (hRC : Commute R C)
    (htrans : R * P = Q * R) (hsq : (C * C) * P = P * Q * P) :
    P * R * P = C * P := by
  apply compression_eq_of_gram_eq_real_sq P R C hP hC hskew hCP hRC
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hRPR : R * P * star R = Q := by
    rw [htrans, mul_assoc, Unitary.mul_star_self_of_mem hunit, mul_one]
  calc
    _ = (P * R) * (P * P) * star R * P := by
      rw [star_mul, star_mul, hP.isSelfAdjoint.star_eq]
      noncomm_ring
    _ = P * (R * P * star R) * P := by rw [hPP]; noncomm_ring
    _ = P * Q * P := by rw [hRPR]
    _ = (C * C) * P := hsq.symm
    _ = (C * P) * (C * P) := by
      calc
        _ = (C * C) * (P * P) := by rw [hPP]
        _ = C * (C * P) * P := by noncomm_ring
        _ = C * (P * C) * P := by rw [hCP.eq]
        _ = _ := by noncomm_ring

/-- The completed nonacute rotation intertwines the source and target
reflections, as it intertwines their orthogonal projections. -/
theorem nonacuteDirectRotation_reflection_intertwines
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) (x : H) :
    nonacuteDirectRotation U V D (U.reflection x) =
      V.reflection (nonacuteDirectRotation U V D x) := by
  rw [Submodule.reflection_apply, Submodule.reflection_apply, map_sub, map_nsmul]
  rw [show nonacuteDirectRotation U V D (U.starProjection x) =
      V.starProjection (nonacuteDirectRotation U V D x) from
    DFunLike.congr_fun (nonacuteDirectRotation_intertwines U V D) x]

/-- The two diagonal compressions of the completed nonacute rotation are
the corresponding positive cosine compressions. -/
theorem nonacuteDirectRotation_compressions_eq_cosine
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    let R := nonacuteDirectRotation U V D
    let C := Proposition35.section3CosAngleOperator U V
    U.starProjection * R * U.starProjection = C * U.starProjection ∧
      Uᗮ.starProjection * R * Uᗮ.starProjection = C * Uᗮ.starProjection := by
  let R := nonacuteDirectRotation U V D
  let C := Proposition35.section3CosAngleOperator U V
  let P := U.starProjection
  let Q := V.starProjection
  let Pc := Uᗮ.starProjection
  let Qc := Vᗮ.starProjection
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hPc : IsStarProjection Pc := isStarProjection_starProjection
  have hCP : Commute C P := by
    exact Commute.cfc_real (Proposition35.section3AngleOperator_comm_projection U V) Real.cos
  have hCPc : Commute C Pc := by
    change Commute C Uᗮ.starProjection
    rw [Submodule.starProjection_orthogonal' U]
    exact (Commute.one_right C).sub_right hCP
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg U V)).isSelfAdjoint
  have hRunit := nonacuteDirectRotation_mem_unitary U V D
  have hRC := Proposition35.nonacuteDirectRotation_comm_cosine U V D
  have hskew := Proposition35.star_nonacuteDirectRotation_sub_cosine U V D
  have htrans : R * P = Q * R := nonacuteDirectRotation_intertwines U V D
  have htransc : R * Pc = Qc * R := by
    dsimp only [Pc, Qc]
    rw [Submodule.starProjection_orthogonal' U, Submodule.starProjection_orthogonal' V,
      mul_sub, sub_mul, mul_one, one_mul]
    rw [htrans]
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hPcPc : Pc * Pc = Pc := hPc.isIdempotentElem.eq
  have hPcP : Pc * P = 0 := by
    dsimp only [Pc]
    rw [Submodule.starProjection_orthogonal' U]
    change (1 - P) * P = 0
    rw [sub_mul, one_mul, hPP, sub_self]
  have hPPc : P * Pc = 0 := by
    dsimp only [Pc]
    rw [Submodule.starProjection_orthogonal' U]
    change P * (1 - P) = 0
    rw [mul_sub, mul_one, hPP, sub_self]
  have hCsq : C * C = P * Q * P + Pc * Qc * Pc :=
    Proposition35.section3CosAngleOperator_mul_self_eq_halmosCosineSq U V
  have hsqP : (C * C) * P = P * Q * P := by
    rw [hCsq]
    calc
      _ = (P * Q) * (P * P) + (Pc * Qc) * (Pc * P) := by noncomm_ring
      _ = _ := by rw [hPP, hPcP, mul_zero, add_zero]
  have hsqPc : (C * C) * Pc = Pc * Qc * Pc := by
    rw [hCsq]
    calc
      _ = (P * Q) * (P * Pc) + (Pc * Qc) * (Pc * Pc) := by noncomm_ring
      _ = _ := by rw [hPPc, hPcPc, mul_zero, zero_add]
  exact ⟨compression_eq_of_transport_gram P Q R C hP hRunit hC hskew hCP hRC htrans hsqP,
    compression_eq_of_transport_gram Pc Qc R C hPc hRunit hC hskew hCPc hRC htransc hsqPc⟩

/-- Reflection in the source reverses the skew part of the completed
nonacute rotation, including on the right-angle defect spaces. -/
theorem nonacuteDirectRotation_skew_reflection
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) (x : H) :
    let K := nonacuteDirectRotation U V D - Proposition35.section3CosAngleOperator U V
    K (U.reflection x) = -U.reflection (K x) := by
  let K := nonacuteDirectRotation U V D - Proposition35.section3CosAngleOperator U V
  obtain ⟨hU, hUc⟩ := nonacuteDirectRotation_compressions_eq_cosine U V D
  have hdiag : U.diagBlock K = 0 := by
    have hPP : U.starProjection * U.starProjection = U.starProjection :=
      (isStarProjection_starProjection (U := U)).isIdempotentElem.eq
    have hPcPc : Uᗮ.starProjection * Uᗮ.starProjection = Uᗮ.starProjection :=
      (isStarProjection_starProjection (U := Uᗮ)).isIdempotentElem.eq
    have hCP : Commute (Proposition35.section3CosAngleOperator U V) U.starProjection :=
      Commute.cfc_real (Proposition35.section3AngleOperator_comm_projection U V) Real.cos
    have hCPc : Commute (Proposition35.section3CosAngleOperator U V) Uᗮ.starProjection := by
      rw [Submodule.starProjection_orthogonal' U]
      exact (Commute.one_right _).sub_right hCP
    rw [Submodule.diagBlock_def]
    change U.starProjection * K * U.starProjection +
      Uᗮ.starProjection * K * Uᗮ.starProjection = 0
    dsimp only [K]
    rw [mul_sub, sub_mul, mul_sub, sub_mul, hU, hUc,
      ← hCP.eq, mul_assoc, hPP, ← hCPc.eq, mul_assoc, hPcPc]
    simp
  have hconj := U.two_smul_diagBlock K
  rw [hdiag, smul_zero] at hconj
  have h := DFunLike.congr_fun hconj (U.reflection x)
  change 0 = K (U.reflection x) + U.reflection (K (U.reflection (U.reflection x))) at h
  rw [Submodule.reflection_reflection] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The real and skew parts of the canonical rotation satisfy its
Pythagorean identity in the operator algebra. -/
theorem nonacuteDirectRotation_cosine_sq_sub_skew_sq
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    let C := Proposition35.section3CosAngleOperator U V
    let K := nonacuteDirectRotation U V D - C
    C * C - K * K = 1 := by
  let R := nonacuteDirectRotation U V D
  let C := Proposition35.section3CosAngleOperator U V
  let K := R - C
  have hC : star C = C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg U V)).isSelfAdjoint.star_eq
  have hK : star K = -K := Proposition35.star_nonacuteDirectRotation_sub_cosine U V D
  have hKC : K * C = C * K := by
    dsimp only [K]
    rw [sub_mul, mul_sub, (Proposition35.nonacuteDirectRotation_comm_cosine U V D).eq]
  have hR : R = C + K := by dsimp only [K]; abel
  have hRstar : star R = C - K := by rw [hR, star_add, hC, hK, sub_eq_add_neg]
  change C * C - K * K = 1
  calc
    _ = (C - K) * (C + K) := by noncomm_ring [hKC]
    _ = star R * R := by rw [← hR, ← hRstar]
    _ = 1 := Unitary.star_mul_self_of_mem (nonacuteDirectRotation_mem_unitary U V D)

end TauCeti.DavisKahan
