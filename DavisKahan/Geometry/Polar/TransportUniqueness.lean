/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.Geometry.Angle.CosineKernel

/-!
# Uniqueness from relative phase and crossed-defect actions

The cosine-weighted relative unitary determines a transporter away from
right angles. Its two crossed-defect actions determine the remainder.
These are Hilbert-space geometric uniqueness statements, independent of
finite dimension, a particular spectral penalty or optimality.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The phase formula modulo the cosine kernel and the two defect
actions determine the entire ambient transporter. This is a uniqueness
statement on arbitrary complex Hilbert spaces, without any optimality
or feasibility assumption. -/
theorem transport_eq_of_phase_and_defect_actions_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R T S : E ≃ₗᵢ[ℂ] E)
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hTsrc : ∀ x : halmosSourceDefect K L, T x = (D x : E))
    (hTtgt : ∀ y : halmosTargetDefect K L, T y = (D.symm y : E))
    (hSsrc : ∀ x : halmosSourceDefect K L, S x = (D x : E))
    (hStgt : ∀ y : halmosTargetDefect K L, S y = (D.symm y : E))
    (hphase : Proposition35.section3CosAngleOperator K L * (R.trans T.symm : E →L[ℂ] E) =
      Proposition35.section3CosAngleOperator K L * (R.trans S.symm : E →L[ℂ] E)) : T = S := by
  let C := Proposition35.section3CosAngleOperator K L
  let N := C.ker
  let : CompleteSpace N := C.isClosed_ker.completeSpace_coe
  have hagree := LinearIsometryEquiv.eq_on_orthogonal_ker_of_relative_left_mul_eq
    C R T S hphase
  have hker (x : E) (hx : x ∈ N) : T x = S x := by
    change x ∈ (Proposition35.section3CosAngleOperator K L).ker at hx
    rw [Proposition35.ker_section3CosAngleOperator_eq_crossedDefectSum] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, map_add, hTsrc ⟨u, hu⟩, hSsrc ⟨u, hu⟩,
      hTtgt ⟨v, hv⟩, hStgt ⟨v, hv⟩]
  ext x
  rw [← N.starProjection_add_starProjection_orthogonal x, map_add, map_add,
    hker _ (Submodule.starProjection_apply_mem _ _),
    hagree _ (Submodule.starProjection_apply_mem _ _)]

/-- The right relative-phase convention and both defect actions determine
an ambient unitary uniquely whenever the reference unitary preserves the
cosine. No optimality, feasibility or cosine commutation of the competing
unitaries is assumed. The Hilbert space may be infinite dimensional. -/
theorem transport_eq_of_right_phase_and_defect_actions_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R T S : E ≃ₗᵢ[ℂ] E)
    (hRC : Commute (R : E →L[ℂ] E) (Proposition35.section3CosAngleOperator K L))
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hTsrc : ∀ x : halmosSourceDefect K L, T x = (D x : E))
    (hTtgt : ∀ y : halmosTargetDefect K L, T y = (D.symm y : E))
    (hSsrc : ∀ x : halmosSourceDefect K L, S x = (D x : E))
    (hStgt : ∀ y : halmosTargetDefect K L, S y = (D.symm y : E))
    (hphase : Proposition35.section3CosAngleOperator K L * (T.trans R.symm : E →L[ℂ] E) =
      Proposition35.section3CosAngleOperator K L * (S.trans R.symm : E →L[ℂ] E)) : T = S := by
  let C := Proposition35.section3CosAngleOperator K L
  change Commute (R : E →L[ℂ] E) C at hRC
  have hC : IsSelfAdjoint C :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hRsC : Commute (R.symm : E →L[ℂ] E) C := by
    rw [← R.adjoint_eq_symm]
    change Commute (star (R : E →L[ℂ] E)) C
    rw [commute_iff_eq]
    simpa only [star_mul, hC.star_eq] using (congrArg star hRC.eq).symm
  have hCT : C * (T : E →L[ℂ] E) = C * (S : E →L[ℂ] E) := by
    ext x
    apply R.symm.injective
    change R.symm (C (T x)) = R.symm (C (S x))
    calc
      _ = C (R.symm (T x)) := congrArg (fun B : E →L[ℂ] E => B (T x)) hRsC.eq
      _ = C (R.symm (S x)) := congrArg (fun B : E →L[ℂ] E => B x) hphase
      _ = _ := (congrArg (fun B : E →L[ℂ] E => B (S x)) hRsC.eq).symm
  have hinv (V : E ≃ₗᵢ[ℂ] E)
      (hsrc : ∀ x : halmosSourceDefect K L, V x = (D x : E))
      (htgt : ∀ y : halmosTargetDefect K L, V y = (D.symm y : E)) :
      (∀ x : halmosSourceDefect K L, V.symm x = (D x : E)) ∧
        (∀ y : halmosTargetDefect K L, V.symm y = (D.symm y : E)) := by
    constructor
    · intro x
      apply V.injective
      rw [V.apply_symm_apply, htgt, D.symm_apply_apply]
    · intro y
      apply V.injective
      rw [V.apply_symm_apply, hsrc, D.apply_symm_apply]
  have hTi := hinv T hTsrc hTtgt
  have hSi := hinv S hSsrc hStgt
  have heq : T.symm = S.symm := by
    apply transport_eq_of_phase_and_defect_actions_complex K L
      (LinearIsometryEquiv.refl ℂ E) T.symm S.symm D hTi.1 hTi.2 hSi.1 hSi.2
    have hTrel : ((LinearIsometryEquiv.refl ℂ E).trans T.symm.symm : E →L[ℂ] E) =
        (T : E →L[ℂ] E) := by ext x; rfl
    have hSrel : ((LinearIsometryEquiv.refl ℂ E).trans S.symm.symm : E →L[ℂ] E) =
        (S : E →L[ℂ] E) := by ext x; rfl
    rw [hTrel, hSrel]
    exact hCT
  simpa only [LinearIsometryEquiv.symm_symm] using
    congrArg (fun V : E ≃ₗᵢ[ℂ] E => V.symm) heq

end TauCeti.DavisKahan
