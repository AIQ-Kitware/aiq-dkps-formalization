/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedAcuteClassification
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedNonacuteClassification
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCommutatorCutoff

/-!
# Every nearest subspace-preserving unitary

An operator-norm commutator defect below one makes a subspace and its
unitary image uniformly acute. The complete transport classification then
describes every nearest preserving unitary, including nonunique families
above the Charbonnier transition. The all-angle criterion also allows
arbitrary right-angle defect exchanges, without a commutator cutoff.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every closest unitary preserving a prescribed subspace has the
compatible projection formula whenever the input commutator defect is
strictly below one. No subcritical-angle assumption is needed. -/
theorem smoothed_correction_isMin_iff_projection_of_commutator_lt_one_complex
    (tau : ℝ) (htau : 0 < tau) (K : Submodule ℂ E) (A V : E ≃ₗᵢ[ℂ] E)
    (hV : K.map V.toLinearMap = K)
    (hdefect : ‖(A : E →L[ℂ] E) * K.starProjection -
      K.starProjection * (A : E →L[ℂ] E)‖ < 1) :
    let L := K.map A.toLinearMap
    let hKL := (A.toLinearEquiv.finrank_map_eq K).symm
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let U := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹
      (Proposition35.section3CosAngleOperator K L)
    (∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = K →
      smoothedOperatorDistance tau A.toLinearMap V.toLinearMap ≤
        smoothedOperatorDistance tau A.toLinearMap S.toLinearMap) ↔
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
        (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
        (V : E →L[ℂ] E) = (U * P + star U * (1 - P)) *
          (A.trans R.symm : E →L[ℂ] E) := by
  let L := K.map A.toLinearMap
  let hKL := (A.toLinearEquiv.finrank_map_eq K).symm
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let U := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹
    (Proposition35.section3CosAngleOperator K L)
  let T := V.symm.trans A
  let C₀ := A.trans R.symm
  have hT : K.map T.toLinearMap = L :=
    transporter_of_correction_preserves_subspace K A V hV
  have hacute : IsUniformlyAcute K L := by
    change K.projectionGap (K.map A.toLinearMap) < 1
    rw [Submodule.projectionGap_unitary_image_eq_commutator]
    exact hdefect
  have hcorr : A.trans T.symm = V := by ext x; simp [T]
  have hmin := correction_isMin_iff_transport_isMin tau K A T
  rw [hcorr] at hmin
  have hclass := smoothed_transport_isMin_iff_projection_of_isUniformlyAcute_complex
    tau htau K L hKL hacute T hT
  have hfactor : (R.trans T.symm : E →L[ℂ] E) * (C₀ : E →L[ℂ] E) =
      (V : E →L[ℂ] E) := by
    ext x
    change T.symm (R (R.symm (A x))) = V x
    simp [T]
  constructor
  · intro h
    obtain ⟨P, hP, hPR, hPJ, hphase⟩ := hclass.mp (hmin.mp h)
    refine ⟨P, hP, hPR, hPJ, ?_⟩
    exact hfactor.symm.trans (congrArg (fun Z : E →L[ℂ] E => Z * (C₀ : E →L[ℂ] E)) hphase)
  · rintro ⟨P, hP, hPR, hPJ, hphase⟩
    apply hmin.mpr
    apply hclass.mpr
    refine ⟨P, hP, hPR, hPJ, ?_⟩
    change (V : E →L[ℂ] E) = (U * P + star U * (1 - P)) * (C₀ : E →L[ℂ] E) at hphase
    have hrel := hfactor.trans hphase
    have h := congrArg (fun Z : E →L[ℂ] E => Z * star (C₀ : E →L[ℂ] E)) hrel
    have hunit : (C₀ : E →L[ℂ] E) ∈ unitary (E →L[ℂ] E) :=
      (Unitary.linearIsometryEquiv.symm C₀).property
    simpa only [mul_assoc, Unitary.mul_star_self_of_mem hunit, mul_one] using h

/-- Every nearest unitary preserving a prescribed subspace, with no
restriction on the input commutator or on its principal angles. The
weighted phase formula and reflecting kernel condition describe every
nonunique optimizer as well as the unique canonical regime. -/
theorem smoothed_correction_isMin_iff_phase_and_kernel_complex
    (tau : ℝ) (htau : 0 < tau) (K : Submodule ℂ E) (A V : E ≃ₗᵢ[ℂ] E)
    (hV : K.map V.toLinearMap = K) :
    let L := K.map A.toLinearMap
    let hKL := (A.toLinearEquiv.finrank_map_eq K).symm
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let C := Proposition35.section3CosAngleOperator K L
    let U := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹ C
    let T := V.symm.trans A
    (∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = K →
      smoothedOperatorDistance tau A.toLinearMap V.toLinearMap ≤
        smoothedOperatorDistance tau A.toLinearMap S.toLinearMap) ↔
      (∀ x, C x = 0 → T x = star (T : E →L[ℂ] E) x) ∧
      ∃ P : E →L[ℂ] E, IsStarProjection P ∧ Commute P (R : E →L[ℂ] E) ∧
        (∀ x, P (K.reflection x) = K.reflection (P x)) ∧
        (∀ x, C x = 0 → P x = 0) ∧
        C * (V : E →L[ℂ] E) = C * (U * P + star U * (1 - P)) *
          (A.trans R.symm : E →L[ℂ] E) := by
  let L := K.map A.toLinearMap
  let hKL := (A.toLinearEquiv.finrank_map_eq K).symm
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  let U := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹ C
  let T := V.symm.trans A
  let C₀ := A.trans R.symm
  have hT : K.map T.toLinearMap = L :=
    transporter_of_correction_preserves_subspace K A V hV
  have hcorr : A.trans T.symm = V := by ext x; simp [T]
  have hmin := correction_isMin_iff_transport_isMin tau K A T
  rw [hcorr] at hmin
  have hclass := smoothed_transport_isMin_iff_phase_and_kernel_complex
    tau htau K L hKL T hT
  have hfactor : (R.trans T.symm : E →L[ℂ] E) * (C₀ : E →L[ℂ] E) =
      (V : E →L[ℂ] E) := by
    ext x
    change T.symm (R (R.symm (A x))) = V x
    simp [T]
  dsimp only at hclass ⊢
  constructor
  · intro h
    obtain ⟨hself, P, hP, hPR, hPJ, hPker, hphase⟩ := hclass.mp (hmin.mp h)
    refine ⟨hself, P, hP, hPR, hPJ, hPker, ?_⟩
    change C * (V : E →L[ℂ] E) = C * (U * P + star U * (1 - P)) * (C₀ : E →L[ℂ] E)
    rw [← hfactor, ← mul_assoc, hphase]
  · rintro ⟨hself, P, hP, hPR, hPJ, hPker, hphase⟩
    apply hmin.mpr
    apply hclass.mpr
    refine ⟨hself, P, hP, hPR, hPJ, hPker, ?_⟩
    change C * (V : E →L[ℂ] E) = C * (U * P + star U * (1 - P)) * (C₀ : E →L[ℂ] E)
      at hphase
    rw [← hfactor, ← mul_assoc] at hphase
    have h := congrArg (fun Z : E →L[ℂ] E => Z * star (C₀ : E →L[ℂ] E)) hphase
    have hunit : (C₀ : E →L[ℂ] E) ∈ unitary (E →L[ℂ] E) :=
      (Unitary.linearIsometryEquiv.symm C₀).property
    simpa only [mul_assoc, Unitary.mul_star_self_of_mem hunit, mul_one] using h

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
