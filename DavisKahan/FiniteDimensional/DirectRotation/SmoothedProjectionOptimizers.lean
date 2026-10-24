/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSignedOptimizers

/-!
# Attainment for arbitrary compatible multiplicity projections

An orthogonal projection commuting with the canonical rotation and source
reflection selects the positive optimal phase on its range and the negative
phase on its orthogonal complement. Every such selection gives an ambient
global optimizer. The projection need not be diagonal in a previously chosen
principal frame; a common paired frame is derived from the projection itself.

This includes arbitrary acute multiplicity splittings. At right angles the
construction gives compatible reflected phases; the larger arbitrary-unitary
defect family still requires a separate assembly theorem.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every compatible orthogonal multiplicity projection gives an actual
globally minimizing ambient weighted transporter. Its relative phase is
the positive optimal spectral factor on the projection range and the
negative factor on the orthogonal complement. -/
theorem exists_weighted_transport_from_projection_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hPR : Commute P (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)))
    (hPJ : ∀ x, P (K.reflection x) = K.reflection (P x)) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let U := weightedPhaseFactor a b (Proposition35.section3CosAngleOperator K L)
    ∃ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L ∧
      (R.trans T.symm : E →L[ℂ] E) = U * P + star U * (1 - P) ∧
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
          weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L) ∧
      ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
        UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) ≤
          UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • S.toLinearMap - (b : ℂ) • LinearMap.id) := by
  classical
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  let U := weightedPhaseFactor a b C
  let U' : unitary (E →L[ℂ] E) := ⟨U, weightedPhaseFactor_mem_unitary a b C inferInstance⟩
  obtain ⟨hPC, n, m, e, theta, eps, sign, hθ, hC0, hC1, hCf,
    hR0, hR1, hRf, hJ0, hJf, hPe⟩ :=
    exists_subspace_paired_rotation_projection_basis_complex K L hKL P hP hPR hPJ
  obtain ⟨T, hT, hZp, hTf, hatt, hmin⟩ := exists_signed_weighted_transport_in_frame_complex
    a b hb hab K L hKL R
    ((K.map_eq_iff_intertwines_reflection L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L (finiteCrossedDefectEquiv K L hKL)))
    e theta eps hθ hC0 hC1 hCf hR0 hR1 hRf hJ0 hJf sign
  have hCp (r : Fin 2) (i : Fin n) : C (e (.inl (r, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (r, i)) := by
    by_cases hr : r = 0
    · subst r; exact hC0 i
    · have hr1 : r = 1 := by omega
      subst r; exact hC1 i
  have hUe (r : Fin 2) (i : Fin n) : U (e (.inl (r, i))) =
      circlePhase 1 (optimalWeightedPhase a b (theta i)) • e (.inl (r, i)) :=
    weightedPhaseFactor_apply_cos a b (theta i) C _
      ⟨(hθ i).1.le, by linarith [(hθ i).2, Real.pi_pos]⟩ (hCp r i)
  have hUs (r : Fin 2) (i : Fin n) : star U (e (.inl (r, i))) =
      circlePhase 1 (-optimalWeightedPhase a b (theta i)) • e (.inl (r, i)) := by
    rw [circlePhase_neg_eq_star]
    exact unitary_star_apply_of_apply_eq_smul U' _ (norm_circlePhase 1 _ zero_le_one) _ (hUe r i)
  have hUf (x : E) (hx : C x = x) : U x = x :=
    weightedPhaseFactor_apply_one a b hab.le C x hx
  have hUsf (x : E) (hx : C x = x) : star U x = x := by
    have h := unitary_star_apply_of_apply_eq_smul U' (1 : ℂ) (by simp) x
      (by simpa only [one_smul] using hUf x hx)
    simpa only [star_one, one_smul] using h
  have hformula : (R.trans T.symm : E →L[ℂ] E) = U * P + star U * (1 - P) := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro j
    change (R.trans T.symm) (e j) = U (P (e j)) + star U (e j - P (e j))
    rcases j with ⟨r, i⟩ | j
    · rw [hZp]
      have hp := hPe r i
      cases hs : sign i
      · have hp0 : P (e (.inl (r, i))) = 0 := by simpa [hs] using hp
        rw [hp0, map_zero, sub_zero, zero_add, hUs]
        simp
      · have hp1 : P (e (.inl (r, i))) = e (.inl (r, i)) := by
          simpa [hs] using hp
        rw [hp1, sub_self, map_zero, add_zero, hUe]
        simp
    · have hZf : (R.trans T.symm) (e (.inr j)) = e (.inr j) := by
        apply T.injective
        change T (T.symm (R (e (.inr j)))) = T (e (.inr j))
        rw [T.apply_symm_apply, show R (e (.inr j)) = _ from hRf j, hTf]
      have hCP : C (P (e (.inr j))) = P (e (.inr j)) := by
        have h := DFunLike.congr_fun hPC.eq (e (.inr j))
        change P (C (e (.inr j))) = C (P (e (.inr j))) at h
        rw [hCf] at h
        exact h.symm
      have hCsub : C (e (.inr j) - P (e (.inr j))) = e (.inr j) - P (e (.inr j)) := by
        rw [map_sub, show C (e (.inr j)) = _ from hCf j, hCP]
      rw [hZf, hUf _ hCP, hUsf _ hCsub]
      abel
  exact ⟨T, hT, hformula, hatt, hmin⟩

/-- Arbitrary compatible multiplicity projections also give globally
optimal transporters for the literal Charbonnier cost. -/
theorem exists_smoothed_transport_from_projection_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hPR : Commute P (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)))
    (hPJ : ∀ x, P (K.reflection x) = K.reflection (P x)) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let U := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹
      (Proposition35.section3CosAngleOperator K L)
    ∃ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L ∧
      (R.trans T.symm : E →L[ℂ] E) = U * P + star U * (1 - P) ∧
      smoothedDisplacementCost tau T.toLinearMap = smoothedTransportMinimum tau K L ∧
      ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
        smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  obtain ⟨T, hT, hphase, hatt, hmin⟩ := exists_weighted_transport_from_projection_complex
    a a⁻¹ (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha) K L hKL P hP hPR hPJ
  have hTc := smoothedDisplacementCost_eq_weightedNuclear tau htau
    (Unitary.linearIsometryEquiv.symm T)
  change smoothedDisplacementCost tau T.toLinearMap =
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
        Module.finrank ℂ E * tau at hTc
  refine ⟨T, hT, hphase, ?_, ?_⟩
  · rw [hTc, hatt]
    rfl
  · intro S hS
    have hSc := smoothedDisplacementCost_eq_weightedNuclear tau htau
      (Unitary.linearIsometryEquiv.symm S)
    change smoothedDisplacementCost tau S.toLinearMap =
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • S.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
          Module.finrank ℂ E * tau at hSc
    rw [hTc, hSc]
    exact sub_le_sub_right (hmin S hS) _

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
