/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedAcuteClassification

/-!
# Exact metric parameterization of isoclinic optimizer families

When the whole principal cosine is the same positive supercritical scalar,
compatible ambient projections parameterize all Charbonnier optimizers.
The correspondence scales every operator distance by twice the sine of the
optimal phase. In particular this is a continuous bijection with continuous
inverse, rather than only a set-theoretic injection. A Grassmannian manifold
identification is not needed for the metric statement.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- On a positive supercritical isoclinic pair, all compatible projections
give all global Charbonnier optimizers, bijectively. Their exact operator
distance is `2s` times projection distance, with `s>0`. The minimum is taken
over every ambient complex unitary transporter. -/
theorem exists_scaled_isometric_smoothed_isoclinic_family_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (c : ℝ) (hc : c ∈ Set.Ioo 0 1)
    (hCscalar : Proposition35.section3CosAngleOperator K L = (c : ℂ) • 1)
    (hcritical : smoothingRadius tau * c < (smoothingRadius tau)⁻¹) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let M := {P : E →L[ℂ] E // IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
      ∀ x, P (K.reflection x) = K.reflection (P x)}
    let beta := smoothingRadius tau * c / (smoothingRadius tau)⁻¹
    let s := Real.sqrt (1 - beta ^ 2)
    0 < s ∧ ∃ f : M → (E ≃ₗᵢ[ℂ] E),
      Function.Injective f ∧
      (∀ P, K.map (f P).toLinearMap = L ∧
        smoothedDisplacementCost tau (f P).toLinearMap = smoothedTransportMinimum tau K L ∧
        ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
          smoothedDisplacementCost tau (f P).toLinearMap ≤
            smoothedDisplacementCost tau S.toLinearMap) ∧
      (∀ P, (R.trans (f P).symm : E →L[ℂ] E) =
        ((beta : ℂ) - (s : ℂ) * Complex.I) • 1 + (2 * (s : ℂ) * Complex.I) • P.val) ∧
      (∀ P Q, ‖(f P : E →L[ℂ] E) - (f Q : E →L[ℂ] E)‖ = 2 * s * ‖P.val - Q.val‖) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E,
        (K.map T.toLinearMap = L ∧
          ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
            smoothedDisplacementCost tau T.toLinearMap ≤
              smoothedDisplacementCost tau S.toLinearMap) ↔ ∃ P, f P = T := by
  classical
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let M := {P : E →L[ℂ] E // IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
    ∀ x, P (K.reflection x) = K.reflection (P x)}
  let a := smoothingRadius tau
  let beta := a * c / a⁻¹
  let s := Real.sqrt (1 - beta ^ 2)
  let C := Proposition35.section3CosAngleOperator K L
  let U := weightedPhaseFactor a a⁻¹ C
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb : 0 < a⁻¹ := inv_pos.mpr ha0
  have hbeta0 : 0 < beta := div_pos (mul_pos ha0 hc.1) hb
  have hbeta1 : beta < 1 := (div_lt_one hb).mpr hcritical
  have hs : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hC : IsSelfAdjoint C := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  have hCe (x : E) : C x = (c : ℂ) • x := by
    rw [show C = (c : ℂ) • 1 from hCscalar]
    rfl
  have hinj : Function.Injective C := by
    intro x y hxy
    rw [hCe, hCe] at hxy
    exact smul_right_injective E (Complex.ofReal_ne_zero.mpr hc.1.ne') hxy
  have hU : U = ((beta : ℂ) + (s : ℂ) * Complex.I) • 1 := by
    ext x
    rw [show U = cfc (weightedPhaseSymbol a a⁻¹) C from rfl,
      ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ (hCe x),
      weightedPhaseSymbol_eq_clip a a⁻¹ c hb ha0.le ⟨hc.1.le, hc.2.le⟩,
      min_eq_right hbeta1.le]
    rfl
  have hformula (P : E →L[ℂ] E) : U * P + star U * (1 - P) =
      ((beta : ℂ) - (s : ℂ) * Complex.I) • 1 + (2 * (s : ℂ) * Complex.I) • P := by
    have hstar : star ((beta : ℂ) + (s : ℂ) * Complex.I) =
        (beta : ℂ) - (s : ℂ) * Complex.I := by simp [sub_eq_add_neg]
    rw [hU, star_smul, star_one, hstar]
    simp only [smul_mul_assoc, one_mul]
    module
  have hex (P : M) := exists_smoothed_transport_from_projection_complex
    tau htau K L hKL P.val P.property.1 P.property.2.1 P.property.2.2
  let f (P : M) := Classical.choose (hex P)
  have hf (P : M) := Classical.choose_spec (hex P)
  have hphase (P : M) : (R.trans (f P).symm : E →L[ℂ] E) =
      ((beta : ℂ) - (s : ℂ) * Complex.I) • 1 + (2 * (s : ℂ) * Complex.I) • P.val :=
    (hf P).2.1.trans (hformula P.val)
  have hnorm (P Q : M) : ‖(f P : E →L[ℂ] E) - (f Q : E →L[ℂ] E)‖ =
      2 * s * ‖P.val - Q.val‖ := by
    rw [LinearIsometryEquiv.norm_sub_eq_of_relative_affine R (f P) (f Q)
      P.val Q.val _ _ (hphase P) (hphase Q)]
    have hk : ‖2 * (s : ℂ) * Complex.I‖ = 2 * s := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.le]
    rw [hk]
  refine ⟨hs, f, ?_, ?_, hphase, hnorm, ?_⟩
  · intro P Q heq
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have h := hnorm P Q
    rw [heq, sub_self, norm_zero] at h
    nlinarith [norm_nonneg (P.val - Q.val)]
  · intro P
    exact ⟨(hf P).1, (hf P).2.2.1, (hf P).2.2.2⟩
  · intro T
    constructor
    · rintro ⟨hT, hmin⟩
      obtain ⟨P, hP, hPR, hPJ, hTphase⟩ :=
        (smoothed_transport_isMin_iff_projection_of_injective_cosine_complex
          tau htau K L hKL T hT hinj).mp hmin
      let p : M := ⟨P, hP, hPR, hPJ⟩
      refine ⟨p, LinearIsometryEquiv.eq_of_relative_eq R ?_⟩
      exact (hf p).2.1.trans hTphase.symm
    · rintro ⟨P, rfl⟩
      exact ⟨(hf P).1, (hf P).2.2.2⟩

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
