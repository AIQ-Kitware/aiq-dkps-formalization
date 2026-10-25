/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedProjectionOptimizers
public import ForTauCeti.Analysis.InnerProductSpace.PairedProjectionExtension

/-!
# Every projection on an actual acute multiplicity space is attained

The parameter is an arbitrary orthogonal projection on one canonical-rotation
eigenspace. Its reflected extension is constructed in the original ambient
space, and gives a globally minimizing transporter over all ambient competitors.
No preselected diagonal basis or projection-extension hypothesis is supplied.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every orthogonal projection on a supercritical acute rotation
multiplicity space occurs as the exact phase parameter of a global
ambient weighted transport minimizer. Other angles may be arbitrary. -/
theorem exists_weighted_transport_with_multiplicity_projection_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (mu : ℂ) (hmu : ‖mu‖ = 1) (hc : 0 < mu.re) (hcritical : a * mu.re < b) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let N := Module.End.eigenspace R.toLinearMap mu
    let beta := a * mu.re / b
    let s := Real.sqrt (1 - beta ^ 2)
    ∀ Q : N →L[ℂ] N, IsStarProjection Q →
      ∃ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L ∧
        (∀ x : N, (R.trans T.symm) x =
          ((beta : ℂ) - (s : ℂ) * Complex.I) • (x : E) +
            (2 * (s : ℂ) * Complex.I) • (Q x : E)) ∧
        (∀ x : N, (R.trans T.symm) (K.reflection x) =
          ((beta : ℂ) - (s : ℂ) * Complex.I) • K.reflection x +
            (2 * (s : ℂ) * Complex.I) • K.reflection (Q x)) ∧
        UnitarilyInvariantSeminorm.nuclear ℂ E E
          ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
            weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L) ∧
        ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
          UnitarilyInvariantSeminorm.nuclear ℂ E E
              ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) ≤
            UnitarilyInvariantSeminorm.nuclear ℂ E E
              ((a : ℂ) • S.toLinearMap - (b : ℂ) • LinearMap.id) := by
  let U : unitary (E →L[ℂ] E) :=
    ⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩
  let R := Unitary.linearIsometryEquiv U
  let N := Module.End.eigenspace R.toLinearMap mu
  let C := Proposition35.section3CosAngleOperator K L
  let beta := a * mu.re / b
  let s := Real.sqrt (1 - beta ^ 2)
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  have hR (x : N) : R x = mu • (x : E) := Module.End.mem_eigenspace_iff.mp x.property
  have hRJ (x : N) : R (K.reflection x) = star mu • K.reflection x := by
    change (U : E →L[ℂ] E) (K.reflection x) = _
    rw [nonacuteDirectRotation_reflection_eq_reflection_star K L
      (finiteCrossedDefectEquiv K L hKL),
      unitary_star_apply_of_apply_eq_smul U mu hmu x (hR x), map_smul]
  have hnonreal : mu ≠ star mu := by
    intro heq
    have him : mu.im = 0 := RCLike.conj_eq_iff_im.mp heq.symm
    have hsquare := Complex.sq_norm_sub_sq_re mu
    rw [hmu, him] at hsquare
    have hre : mu.re = 1 := by nlinarith
    rw [hre, mul_one] at hcritical
    exact (lt_trans hcritical hab).false
  have horth (x y : N) : inner ℂ (x : E) (K.reflection y) = 0 :=
    unitary_eigenvectors_inner_eq_zero_of_ne U mu (star mu) hmu hnonreal
      x (K.reflection y) (hR x) (hRJ y)
  dsimp only
  intro Q hQ
  obtain ⟨P, ⟨hP, hPR, hPJ, hPx, _⟩, _⟩ := exists_unique_paired_projection_extension N K.reflection R
    K.reflection_involutive horth mu (star mu) hR hRJ Q hQ
  obtain ⟨T, hT, hphase, hatt, hmin⟩ :=
    exists_weighted_transport_from_projection_complex a b hb hab K L hKL P hP hPR hPJ
  have hbeta1 : beta < 1 := (div_lt_one hb).mpr hcritical
  have hc1 : mu.re ≤ 1 := mu.re_le_norm.trans_eq hmu
  have hCx (x : N) : C (x : E) = (mu.re : ℂ) • (x : E) :=
    unitary_real_part_apply_of_apply_eq_smul U C
      (nonacuteDirectRotation_add_star_eq_two_cosine K L (finiteCrossedDefectEquiv K L hKL))
      mu hmu x (hR x)
  let F := weightedPhaseFactor a b C
  let F' : unitary (E →L[ℂ] E) := ⟨F, weightedPhaseFactor_mem_unitary a b C inferInstance⟩
  have hsymbol : weightedPhaseSymbol a b (mu.re : ℂ) =
      (beta : ℂ) + (s : ℂ) * Complex.I := by
    rw [weightedPhaseSymbol_eq_clip a b mu.re hb (hb.le.trans hab.le) ⟨hc.le, hc1⟩,
      min_eq_right hbeta1.le]
  have hFx (x : N) : F (x : E) = ((beta : ℂ) + (s : ℂ) * Complex.I) • (x : E) := by
    rw [show F = cfc (weightedPhaseSymbol a b) C from rfl,
      ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ (hCx x), hsymbol]
  have hFstar (x : N) : star F (x : E) =
      ((beta : ℂ) - (s : ℂ) * Complex.I) • (x : E) := by
    have hnorm : ‖(beta : ℂ) + (s : ℂ) * Complex.I‖ = 1 := by
      rw [← hsymbol]
      exact norm_circlePhase 1 _ zero_le_one
    have h := unitary_star_apply_of_apply_eq_smul F' _ hnorm x (hFx x)
    have hcoef : star ((beta : ℂ) + (s : ℂ) * Complex.I) =
        (beta : ℂ) - (s : ℂ) * Complex.I := by simp [sub_eq_add_neg]
    simpa only [hcoef] using h
  have hZN (x : N) : (R.trans T.symm) x =
      ((beta : ℂ) - (s : ℂ) * Complex.I) • (x : E) +
        (2 * (s : ℂ) * Complex.I) • (Q x : E) := by
    change (R.trans T.symm : E →L[ℂ] E) (x : E) = _
    rw [hphase]
    change F (P (x : E)) + star F ((x : E) - P (x : E)) = _
    rw [hPx]
    change F (Q x : E) + star F ((x - Q x : N) : E) = _
    rw [hFx, hFstar]
    simp only [Submodule.coe_sub]
    module
  refine ⟨T, hT, hZN, ?_, hatt, hmin⟩
  intro x
  have hRmap : K.map R.toLinearMap = L :=
    (K.map_eq_iff_intertwines_reflection L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L (finiteCrossedDefectEquiv K L hKL))
  rw [K.relative_transport_commutes_reflection L R T hRmap hT, hZN, map_add, map_smul, map_smul]

/-- Every orthogonal projection on one actual supercritical acute
multiplicity space is attained for the literal Charbonnier objective. -/
theorem exists_smoothed_transport_with_multiplicity_projection_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (mu : ℂ) (hmu : ‖mu‖ = 1) (hc : 0 < mu.re)
    (hcritical : smoothingRadius tau * mu.re < (smoothingRadius tau)⁻¹) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let N := Module.End.eigenspace R.toLinearMap mu
    let beta := smoothingRadius tau * mu.re / (smoothingRadius tau)⁻¹
    let s := Real.sqrt (1 - beta ^ 2)
    ∀ Q : N →L[ℂ] N, IsStarProjection Q →
      ∃ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L ∧
        (∀ x : N, (R.trans T.symm) x =
          ((beta : ℂ) - (s : ℂ) * Complex.I) • (x : E) +
            (2 * (s : ℂ) * Complex.I) • (Q x : E)) ∧
        (∀ x : N, (R.trans T.symm) (K.reflection x) =
          ((beta : ℂ) - (s : ℂ) * Complex.I) • K.reflection x +
            (2 * (s : ℂ) * Complex.I) • K.reflection (Q x)) ∧
        smoothedDisplacementCost tau T.toLinearMap = smoothedTransportMinimum tau K L ∧
        ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
          smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  dsimp only
  intro Q hQ
  obtain ⟨T, hT, hphase, hreflect, hatt, hmin⟩ :=
    exists_weighted_transport_with_multiplicity_projection_complex a a⁻¹
      (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha)
      K L hKL mu hmu hc hcritical Q hQ
  have hTc := smoothedDisplacementCost_eq_weightedNuclear tau htau
    (Unitary.linearIsometryEquiv.symm T)
  change smoothedDisplacementCost tau T.toLinearMap =
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
        Module.finrank ℂ E * tau at hTc
  refine ⟨T, hT, hphase, hreflect, ?_, ?_⟩
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

/-- The complete set of orthogonal projections on one supercritical acute
multiplicity space injects into the ambient Charbonnier minimizers. This
family has the explicit separation factor `2s` in operator norm. It is a
set-theoretic injection; no continuity or topological classification of
the chosen extension is asserted. -/
theorem exists_injective_smoothed_multiplicity_family_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (mu : ℂ) (hmu : ‖mu‖ = 1) (hc : 0 < mu.re)
    (hcritical : smoothingRadius tau * mu.re < (smoothingRadius tau)⁻¹) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let N := Module.End.eigenspace R.toLinearMap mu
    let beta := smoothingRadius tau * mu.re / (smoothingRadius tau)⁻¹
    let s := Real.sqrt (1 - beta ^ 2)
    ∃ f : {Q : N →L[ℂ] N // IsStarProjection Q} → (E ≃ₗᵢ[ℂ] E),
      Function.Injective f ∧
      (∀ Q, K.map (f Q).toLinearMap = L ∧
        smoothedDisplacementCost tau (f Q).toLinearMap = smoothedTransportMinimum tau K L ∧
        ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
          smoothedDisplacementCost tau (f Q).toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap) ∧
      ∀ Q Q', 2 * s * ‖Q.val - Q'.val‖ ≤ ‖(f Q : E →L[ℂ] E) - (f Q' : E →L[ℂ] E)‖ := by
  classical
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let N := Module.End.eigenspace R.toLinearMap mu
  let a := smoothingRadius tau
  let beta := a * mu.re / a⁻¹
  let s := Real.sqrt (1 - beta ^ 2)
  have ha0 : 0 < a := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hb : 0 < a⁻¹ := inv_pos.mpr ha0
  have hbeta0 : 0 < beta := div_pos (mul_pos ha0 hc) hb
  have hbeta1 : beta < 1 := (div_lt_one hb).mpr hcritical
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (show 0 < 1 - beta ^ 2 by
    nlinarith [mul_pos (sub_pos.mpr hbeta1) (add_pos hbeta0 zero_lt_one)])).ne'
  have hcoef : 2 * (s : ℂ) * Complex.I ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (Complex.ofReal_ne_zero.mpr hs)) Complex.I_ne_zero
  have hex (Q : {Q : N →L[ℂ] N // IsStarProjection Q}) :=
    exists_smoothed_transport_with_multiplicity_projection_complex
      tau htau K L hKL mu hmu hc hcritical Q.val Q.property
  let f (Q : {Q : N →L[ℂ] N // IsStarProjection Q}) := Classical.choose (hex Q)
  have hf (Q) := Classical.choose_spec (hex Q)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro Q Q' hT
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    apply smul_right_injective E hcoef
    change (2 * (s : ℂ) * Complex.I) • (Q.val x : E) =
      (2 * (s : ℂ) * Complex.I) • (Q'.val x : E)
    have h1 := (hf Q).2.1 x
    have h2 := (hf Q').2.1 x
    change (R.trans (f Q).symm) (x : E) =
      ((beta : ℂ) - (s : ℂ) * Complex.I) • (x : E) +
        (2 * (s : ℂ) * Complex.I) • (Q.val x : E) at h1
    change (R.trans (f Q').symm) (x : E) =
      ((beta : ℂ) - (s : ℂ) * Complex.I) • (x : E) +
        (2 * (s : ℂ) * Complex.I) • (Q'.val x : E) at h2
    rw [hT] at h1
    exact add_left_cancel (h1.symm.trans h2)
  · intro Q
    exact ⟨(hf Q).1, (hf Q).2.2.2⟩
  · intro Q Q'
    have h := N.relative_phase_projection_separation R (f Q) (f Q') Q.val Q'.val
      ((beta : ℂ) - (s : ℂ) * Complex.I) (2 * (s : ℂ) * Complex.I)
      ((hf Q).2.1) ((hf Q').2.1)
    have hk : ‖2 * (s : ℂ) * Complex.I‖ = 2 * s := by
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one]
      rw [abs_of_nonneg (show 0 ≤ s from Real.sqrt_nonneg _)]
    rwa [hk] at h

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
