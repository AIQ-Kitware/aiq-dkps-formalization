/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearOptimizerStructure

/-!
# Signed sine roots and the nuclear optimizer certificate

A self-adjoint calibrated displacement that fixes the common sector
is automatically positive. Its complementary signed sine has modulus
exactly equal to the intrinsic sine, including the right-angle sector.
These facts use only unitary algebra and positive square roots.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal

attribute [local instance] _root_.ContinuousLinearMap.realAlgebra
  _root_.ContinuousLinearMap.realIsScalarTower

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The signed sine associated with a Hermitian calibrated relative
unitary is self-adjoint and has precisely the intrinsic sine as its
modulus. The right-angle sector is included without an inverse cosine. -/
theorem nuclearTransportDual_signed_sine_structure
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (Z : E ≃ₗᵢ[𝕜] E)
    (hfix : (1 - (Z : E →L[𝕜] E)) *
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker.starProjection = 0)
    (hself : IsSelfAdjoint (star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E)))) :
    let C := Proposition35.section3CosAngleOperator K L
    let V := nuclearTransportDual K L D
    let A := star (V : E →L[𝕜] E) * ((Z : E →L[𝕜] E) - C)
    IsSelfAdjoint A ∧ A.modulus = K.sinAngleOperator L ∧
      A * A = K.sinAngleOperator L * K.sinAngleOperator L ∧
      star (V : E →L[𝕜] E) * (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E)) =
        K.sinAngleOperator L - A := by
  let C := Proposition35.section3CosAngleOperator K L
  let S := K.sinAngleOperator L
  let V := nuclearTransportDual K L D
  let W := (V.trans Z.symm).trans V.symm
  let A := star (V : E →L[𝕜] E) * ((Z : E →L[𝕜] E) - C)
  let H := star (V : E →L[𝕜] E) * (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E))
  have hS : S.IsPositive := K.isPositive_sinAngleOperator L
  have hC : C.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)
  have hW : (W : E →L[𝕜] E) =
      star (V : E →L[𝕜] E) * star (Z : E →L[𝕜] E) * (V : E →L[𝕜] E) := by
    rw [V.star_eq_symm, Z.star_eq_symm]
    ext x
    rfl
  have hsum : (Z : E →L[𝕜] E) + (W : E →L[𝕜] E) = C + C := by
    rw [hW]
    exact nuclearTransportDual_relative_positive_average K L D Z hfix hself
  have hswap : (W : E →L[𝕜] E) + (Z : E →L[𝕜] E) = C + C := by rw [add_comm]; exact hsum
  have hstruct := TauCeti.ContinuousLinearMap.unitary_positive_average_structure
    C (W : E →L[𝕜] E) (Z : E →L[𝕜] E) hC
      (Unitary.linearIsometryEquiv.symm W).property (Unitary.linearIsometryEquiv.symm Z).property hswap
  have hCWstar : C * (W : E →L[𝕜] E) = C * star (Z : E →L[𝕜] E) := by
    have h := hstruct.2.2
    rwa [mul_sub, sub_eq_zero] at h
  have hweighted : C * (Z : E →L[𝕜] E) + C * star (Z : E →L[𝕜] E) = C * C + C * C := by
    rw [← hCWstar, ← mul_add, hsum, mul_add]
  have hCZ : Commute C (Z : E →L[𝕜] E) := hstruct.2.1
  have hZstarC : star (Z : E →L[𝕜] E) * C = C * star (Z : E →L[𝕜] E) := by
    have h := congrArg star hCZ.eq
    rw [star_mul, star_mul, hC.isSelfAdjoint.star_eq] at h
    exact h
  have hZm : (Z : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := (Unitary.linearIsometryEquiv.symm Z).property
  have hVm : (V : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := (Unitary.linearIsometryEquiv.symm V).property
  have hCS : C * C + S * S = 1 := Proposition35.section3CosAngleOperator_sq_add_sinAngleOperator_sq K L
  have hgram : star ((Z : E →L[𝕜] E) - C) * ((Z : E →L[𝕜] E) - C) = S * S := by
    rw [star_sub, hC.isSelfAdjoint.star_eq, sub_mul, mul_sub, mul_sub,
      Unitary.star_mul_self_of_mem hZm, hZstarC]
    calc
      _ = 1 - (C * (Z : E →L[𝕜] E) + C * star (Z : E →L[𝕜] E)) + C * C := by abel
      _ = 1 - (C * C + C * C) + C * C := by rw [hweighted]
      _ = S * S := by rw [← hCS]; abel
  have hAgram : star A * A = S * S := by
    calc
      _ = star ((Z : E →L[𝕜] E) - C) *
          (((V : E →L[𝕜] E) * star (V : E →L[𝕜] E)) * ((Z : E →L[𝕜] E) - C)) := by
            dsimp only [A]
            rw [star_mul, star_star]
            simp only [mul_assoc]
      _ = star ((Z : E →L[𝕜] E) - C) * ((Z : E →L[𝕜] E) - C) := by
        rw [Unitary.mul_star_self_of_mem hVm, one_mul]
      _ = S * S := hgram
  have hmod : S = A.modulus := (ContinuousLinearMap.eq_modulus_iff).mpr
    ⟨hS, by change S * S = star A * A; exact hAgram.symm⟩
  have hH : H = S - A := by
    change star (V : E →L[𝕜] E) * _ = _
    have hVB : star (V : E →L[𝕜] E) * (nonacuteDirectRotation K L D - C) = S :=
      nuclearTransportDual_adjoint_mul_skew K L D
    rw [← hVB]
    dsimp only [A, V, C]
    rw [← mul_sub]
    congr 1
    abel
  have hA : IsSelfAdjoint A := by
    have h : A = S - H := by rw [hH]; abel
    rw [h]
    exact hS.isSelfAdjoint.sub hself
  exact ⟨hA, hmod.symm, by simpa only [hA.star_eq] using hAgram, hH⟩

/-- For a relative unitary fixing the whole common sector, a
self-adjoint nuclear dual displacement is automatically positive.
This holds over either scalar field and in arbitrary Hilbert dimension. -/
theorem nuclearTransportDual_isPositive_of_isSelfAdjoint
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (Z : E ≃ₗᵢ[𝕜] E)
    (hfix : (1 - (Z : E →L[𝕜] E)) *
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker.starProjection = 0)
    (hself : IsSelfAdjoint (star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E)))) :
    (star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E))).IsPositive := by
  obtain ⟨hA, hmod, _, hH⟩ := nuclearTransportDual_signed_sine_structure K L D Z hfix hself
  rw [hH, ← hmod]
  apply (ContinuousLinearMap.nonneg_iff_isPositive).mp
  rw [ContinuousLinearMap.modulus_eq_abs, CFC.abs_sub_self _ hA]
  exact nsmul_nonneg (CFC.negPart_nonneg _) 2

/-- The Hermitian dual conditions force finite native nuclear
cost whenever the projection difference is trace class. Thus checking
the conditions does not require a separate displacement-ideal test. -/
theorem nuclearTransportDual_displacement_finite_of_isSelfAdjoint
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (Z : E ≃ₗᵢ[𝕜] E)
    (hfix : (1 - (Z : E →L[𝕜] E)) *
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker.starProjection = 0)
    (hself : IsSelfAdjoint (star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E)))) :
    (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E)).nuclearENorm ≠ ∞ := by
  let S := K.sinAngleOperator L
  let V := nuclearTransportDual K L D
  let A := star (V : E →L[𝕜] E) * ((Z : E →L[𝕜] E) - Proposition35.section3CosAngleOperator K L)
  let H := star (V : E →L[𝕜] E) * (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E))
  obtain ⟨_, hmod, _, hH⟩ := nuclearTransportDual_signed_sine_structure K L D Z hfix hself
  have hSfinite : S.nuclearENorm ≠ ∞ := by
    simpa only [S, Submodule.sinAngleOperator_def, ContinuousLinearMap.nuclearENorm_def,
      ContinuousLinearMap.singularValue_modulus] using hΔ
  have hAfinite : A.nuclearENorm ≠ ∞ := by
    have hn : A.modulus.nuclearENorm = A.nuclearENorm := by
      simp only [ContinuousLinearMap.nuclearENorm_def, ContinuousLinearMap.singularValue_modulus]
    rw [← hn, hmod]
    exact hSfinite
  have hHfinite : H.nuclearENorm ≠ ∞ := by
    change H = S - A at hH
    rw [hH, sub_eq_add_neg]
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨hSfinite, by rwa [ContinuousLinearMap.nuclearENorm_neg]⟩)
      (S.nuclearENorm_add_le (-A))
  have hVm : (V : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := (Unitary.linearIsometryEquiv.symm V).property
  have hX : nonacuteDirectRotation K L D - (Z : E →L[𝕜] E) = (V : E →L[𝕜] E) * H := by
    dsimp only [H]
    rw [← mul_assoc, Unitary.mul_star_self_of_mem hVm, one_mul]
  rw [hX]
  have hbound := ContinuousLinearMap.nuclearENorm_comp_comp_le (V : E →L[𝕜] E) H (1 : E →L[𝕜] E)
  change ((V : E →L[𝕜] E) * H).nuclearENorm ≤
    ‖(V : E →L[𝕜] E)‖ₑ * H.nuclearENorm * ‖(1 : E →L[𝕜] E)‖ₑ at hbound
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) hHfinite) (by finiteness)) hbound

section Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **An entirely Hermitian certificate for every nuclear optimizer.**
For a trace-class projection difference and balanced defects, global
minimality of an arbitrary transporter is equivalent to fixation of
the projection-agreement sector and a self-adjoint dual displacement.
Positivity and finite nuclear displacement follow from those equations. -/
theorem nuclear_isMin_iff_hermitian_certificate_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : F ≃ₗᵢ[ℂ] F) (hT : K.map T.toLinearMap = L) :
    let R := nonacuteDirectRotation K L D
    (∀ W : F ≃ₗᵢ[ℂ] F, K.map W.toLinearMap = L →
      (1 - (T : F →L[ℂ] F)).nuclearENorm ≤ (1 - (W : F →L[ℂ] F)).nuclearENorm) ↔
      (∀ x, K.starProjection x = L.starProjection x → T x = x) ∧
        IsSelfAdjoint (star (nuclearTransportDual K L D : F →L[ℂ] F) *
          (R - (T.symm : F →L[ℂ] F) * R)) := by
  constructor
  · intro hmin
    have h := (nuclear_isMin_iff_certificate_complex K L D hΔ T hT).mp hmin
    exact ⟨h.2.1, h.2.2.isSelfAdjoint⟩
  · rintro ⟨hfixed, hself⟩
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
        unitary (F →L[ℂ] F))
    let Z := R.trans T.symm
    let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
    let Q := B.ker.starProjection
    let X := nonacuteDirectRotation K L D - (Z : F →L[ℂ] F)
    have hfix : (1 - (Z : F →L[ℂ] F)) * Q = 0 := by
      ext x
      have hx := B.ker.starProjection_apply_mem x
      change Q x ∈ B.ker at hx
      rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub] at hx
      change K.starProjection (Q x) - L.starProjection (Q x) = 0 at hx
      have hR : R (Q x) = Q x :=
        nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D _ (sub_eq_zero.mp hx)
      have hTQ := hfixed (Q x) (sub_eq_zero.mp hx)
      have hZQ : Z (Q x) = Q x := by
        apply T.injective
        change T (T.symm (R (Q x))) = T (Q x)
        rw [T.apply_symm_apply, hR, hTQ]
      change Q x - Z (Q x) = 0
      rw [hZQ, sub_self]
    have hself' : IsSelfAdjoint (star (nuclearTransportDual K L D : F →L[ℂ] F) * X) := hself
    have hpos := nuclearTransportDual_isPositive_of_isSelfAdjoint K L D Z hfix hself'
    have hXfinite := nuclearTransportDual_displacement_finite_of_isSelfAdjoint K L D hΔ Z hfix hself'
    have hfactor : 1 - (T : F →L[ℂ] F) = -(X * (Z.symm : F →L[ℂ] F)) := by
      ext x
      change x - T x = -(R (Z.symm x) - Z (Z.symm x))
      rw [Z.apply_symm_apply]
      have hRZ : R (Z.symm x) = T x := by
        change R (R.symm (T x)) = T x
        exact R.apply_symm_apply _
      rw [hRZ, neg_sub]
    have hfinite : (1 - (T : F →L[ℂ] F)).nuclearENorm ≠ ∞ := by
      rw [hfactor, ContinuousLinearMap.nuclearENorm_neg]
      have hbound := ContinuousLinearMap.nuclearENorm_comp_comp_le
        (1 : F →L[ℂ] F) X (Z.symm : F →L[ℂ] F)
      change (X * (Z.symm : F →L[ℂ] F)).nuclearENorm ≤
        ‖(1 : F →L[ℂ] F)‖ₑ * X.nuclearENorm * ‖(Z.symm : F →L[ℂ] F)‖ₑ at hbound
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) hXfinite) (by finiteness)) hbound
    exact (nuclear_isMin_iff_certificate_complex K L D hΔ T hT).mpr ⟨hfinite, hfixed, hpos⟩

end Complex

end TauCeti.DavisKahan
