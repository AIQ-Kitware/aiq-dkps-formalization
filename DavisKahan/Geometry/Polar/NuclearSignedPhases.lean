/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearPhase

/-!
# Opposite nuclear-optimal phases and exact separation

The phases R(C+iS) and R(C-iS) both transport the pair and attain its
native nuclear projection gap. Reflection conjugation relates one to
the adjoint of the other, so their costs agree even when infinite.
Their operator-norm separation is exactly twice the projection gap.
Thus a nontrivial pair with an identified crossed defect has distinct
optimal phases, without a compactness or finite-rank hypothesis.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem star_cosine_add_i_sine_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    star (Proposition35.section3CosAngleOperator K L + Complex.I • K.sinAngleOperator L) =
      Proposition35.section3CosAngleOperator K L - Complex.I • K.sinAngleOperator L := by
  have hC := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hS := (K.isPositive_sinAngleOperator L).isSelfAdjoint
  rw [star_add, star_smul, hC.star_eq, hS.star_eq]
  simp [sub_eq_add_neg]

private theorem commute_projection_cosine_add_i_sine_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    Commute K.starProjection
      (Proposition35.section3CosAngleOperator K L + Complex.I • K.sinAngleOperator L) :=
  (Proposition35.section3CosAngleOperator_comm_projection K L).symm.add_right
    ((K.commute_starProjection_sinAngleOperator L).smul_right Complex.I)

/-- The opposite common phase of completed direct rotation, using the
adjoint of C+iS. It is defined as an actual ambient unitary. -/
@[expose]
def negativeNuclearPhaseRotation_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) : E ≃ₗᵢ[ℂ] E :=
  Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D *
        star (Proposition35.section3CosAngleOperator K L + Complex.I • K.sinAngleOperator L),
      mul_mem (nonacuteDirectRotation_mem_unitary K L D)
        (Unitary.star_mem (cosine_add_i_sine_mem_unitary_complex K L))⟩ : unitary (E →L[ℂ] E))

/-- The opposite common phase is a transporter of the full actual pair. -/
theorem negativeNuclearPhaseRotation_map_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    K.map (negativeNuclearPhaseRotation_complex K L D).toLinearMap = L := by
  let F := Proposition35.section3CosAngleOperator K L + Complex.I • K.sinAngleOperator L
  let V := Unitary.linearIsometryEquiv
    (⟨star F, Unitary.star_mem (cosine_add_i_sine_mem_unitary_complex K L)⟩ : unitary (E →L[ℂ] E))
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[ℂ] E))
  have hcomm : Commute (star F) K.starProjection := by
    change star F * K.starProjection = K.starProjection * star F
    have h := congrArg star (commute_projection_cosine_add_i_sine_complex K L).eq
    simpa only [star_mul, (isSelfAdjoint_starProjection K).star_eq] using h
  have hVmap : K.map V.toLinearMap = K := (K.map_eq_self_iff_commute_starProjection V).mpr hcomm
  have hRmap : K.map R.toLinearMap = L :=
    (K.map_eq_iff_intertwines_reflection L R).mpr (nonacuteDirectRotation_reflection_intertwines K L D)
  change K.map (R.toLinearMap.comp V.toLinearMap) = L
  rw [Submodule.map_comp, hVmap, hRmap]

/-- Source reflection conjugates the adjoint of the positive phase to
the negative phase. This is the exact symmetry behind equal nuclear costs. -/
theorem negativeNuclearPhaseRotation_eq_reflection_conjugate_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    K.reflection.conjStarAlgEquiv (star (nuclearPhaseRotation_complex K L D : E →L[ℂ] E)) =
      (negativeNuclearPhaseRotation_complex K L D : E →L[ℂ] E) := by
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let S := K.sinAngleOperator L
  let F := C + Complex.I • S
  have hJR : K.reflection.conjStarAlgEquiv R = star R := by
    apply ContinuousLinearMap.ext
    intro x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, K.reflection_symm]
    have h := congrArg K.reflection (nonacuteDirectRotation_reflection_eq_reflection_star K L D x)
    simpa only [K.reflection_reflection] using h
  have hJF : K.reflection.conjStarAlgEquiv F = F := by
    have hcomm := (K.commute_reflection_iff.mpr (commute_projection_cosine_add_i_sine_complex K L)).eq
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg (fun T : E →L[ℂ] E => T (K.reflection.symm x)) hcomm
    change K.reflection (F (K.reflection.symm x)) = F (K.reflection (K.reflection.symm x)) at h
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      K.reflection.apply_symm_apply] using h
  have hRF : Commute R (star F) := by
    rw [show star F = C - Complex.I • S from star_cosine_add_i_sine_complex K L]
    exact (Proposition35.nonacuteDirectRotation_comm_cosine K L D).sub_right
      ((nonacuteDirectRotation_comm_sinAngleOperator K L D).smul_right Complex.I)
  change K.reflection.conjStarAlgEquiv (star (R * F)) = R * star F
  rw [star_mul, map_mul, map_star, map_star, hJF, hJR, star_star]
  exact hRF.eq.symm

/-- The opposite phase has the same exact native nuclear projection
cost as the positive phase, including infinite values. -/
theorem gauge_nuclear_negativeNuclearPhaseRotation_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
        (1 - (negativeNuclearPhaseRotation_complex K L D : E →L[ℂ] E)) =
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
        (K.starProjection - L.starProjection) := by
  let Φ := OperatorIdealFamily.schatten ℂ 1 (by norm_num)
  have hdisp : 1 - (negativeNuclearPhaseRotation_complex K L D : E →L[ℂ] E) =
      K.reflection.conjStarAlgEquiv (star (1 - (nuclearPhaseRotation_complex K L D : E →L[ℂ] E))) := by
    rw [star_sub, star_one, map_sub, map_one,
      negativeNuclearPhaseRotation_eq_reflection_conjugate_complex]
  rw [hdisp, LinearIsometryEquiv.conjStarAlgEquiv_apply,
    Φ.gauge_comp_linearIsometryEquiv_left, Φ.gauge_comp_linearIsometryEquiv_right]
  calc
    Φ.gauge (star (1 - (nuclearPhaseRotation_complex K L D : E →L[ℂ] E))) =
        Φ.gauge (1 - (nuclearPhaseRotation_complex K L D : E →L[ℂ] E)) := by
      simp only [Φ, OperatorIdealFamily.gauge_schatten, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.singularValue_adjoint]
    _ = _ := gauge_nuclear_nuclearPhaseRotation_complex K L D

/-- Every ambient unitary transporter has cost at least that of the
opposite phase. No block restriction is placed on competitors. -/
theorem negativeNuclearPhaseRotation_isMin_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
        (1 - (negativeNuclearPhaseRotation_complex K L D : E →L[ℂ] E)) ≤
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (U : E →L[ℂ] E)) := by
  rw [gauge_nuclear_negativeNuclearPhaseRotation_complex]
  exact (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge_projection_sub_le_unitary_displacement
    K L U hmap

/-- The two opposite global nuclear phases have exact operator-norm
separation twice the projection gap, with zero/right angles included. -/
theorem norm_nuclearPhaseRotation_sub_negative_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    ‖(nuclearPhaseRotation_complex K L D : E →L[ℂ] E) -
      (negativeNuclearPhaseRotation_complex K L D : E →L[ℂ] E)‖ =
      2 * ‖K.starProjection - L.starProjection‖ := by
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let S := K.sinAngleOperator L
  let R' := Unitary.linearIsometryEquiv
    (⟨R, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[ℂ] E))
  have hdiff : (nuclearPhaseRotation_complex K L D : E →L[ℂ] E) -
      (negativeNuclearPhaseRotation_complex K L D : E →L[ℂ] E) =
      ((2 : ℂ) * Complex.I) • (R * S) := by
    change R * (C + Complex.I • S) - R * star (C + Complex.I • S) = _
    rw [star_cosine_add_i_sine_complex]
    simp only [mul_add, mul_sub, mul_smul_comm]
    module
  rw [hdiff, norm_smul, norm_mul, RCLike.norm_two, Complex.norm_I, mul_one]
  have hnorm : ‖R * S‖ = ‖S‖ := ContinuousLinearMap.opNorm_linearIsometryEquiv_comp R' S
  rw [hnorm]
  change 2 * ‖K.sinAngleOperator L‖ = _
  rw [Submodule.sinAngleOperator_def, ContinuousLinearMap.norm_modulus]

end TauCeti.DavisKahan
