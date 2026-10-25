/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerNoMixing
public import DavisKahan.Geometry.Angle.CosineKernel

/-!
# All optimizers for transport onto the orthogonal complement

For a complementary right-angle pair, a feasible weighted nuclear
transporter is globally minimizing exactly when it is self-adjoint.
The criterion ranges over all ambient competitors. Thus every unitary
identification of the complementary defect spaces, paired with its adjoint,
attains the minimum. The result does not assemble this family with mixed
positive-angle and fixed summands.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- On the actual right-angle kernel of any pair, every global Charbonnier
minimizer is self-adjoint and exchanges the two source-reflection sectors.
Positive angles and fixed directions elsewhere are unrestricted. -/
theorem smoothed_minimizer_right_defect_reflecting_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap)
    (x : E) (hx : Proposition35.section3CosAngleOperator K L x = 0) :
    T x = star (T : E →L[ℂ] E) x ∧ T (K.reflection x) = -K.reflection (T x) :=
  ⟨smoothed_minimizer_selfAdjoint_on_right_defect_complex tau htau K L hKL T hT hmin x hx,
    Proposition35.transport_anticommutes_reflection_on_cosine_kernel K L T hT
      (smoothed_minimizer_commutes_cosine_complex tau htau K L hKL T hT hmin) x hx⟩

/-- A complementary pair has identically zero principal cosine on the
whole ambient space. -/
theorem cosine_orthogonalComplement_eq_zero_complex (K : Submodule ℂ E) :
    Proposition35.section3CosAngleOperator K Kᗮ = 0 := by
  rw [Proposition35.section3CosAngleOperator_eq_canonicalAbsoluteValue]
  have hcore : spectraCanonicalIntertwiner K Kᗮ = 0 := by
    simp only [spectraCanonicalIntertwiner, Submodule.orthogonal_orthogonal,
      Submodule.starProjection_orthogonal]
    change (1 - K.starProjection) * K.starProjection + K.starProjection *
      (1 - K.starProjection) = 0
    simp only [sub_mul, mul_sub, one_mul, mul_one, K.isIdempotentElem_starProjection.eq,
      sub_self, zero_add]
  rw [hcore, ContinuousLinearMap.modulus_zero]

/-- The exact weighted value on a complementary pair is `a` times the
ambient complex dimension. Feasibility separately requires equal ranks. -/
theorem weightedRotationMinimum_orthogonalComplement_complex
    (a b : ℝ) (hb : 0 < b) (K : Submodule ℂ E) :
    weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K Kᗮ) =
      a * Module.finrank ℂ E := by
  let C := Proposition35.section3CosAngleOperator K Kᗮ
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K Kᗮ)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  let e := stdOrthonormalBasis ℂ E
  have he (i) : C (e i) = (0 : ℂ) • e i := by
    rw [show C = 0 from cosine_orthogonalComplement_eq_zero_complex K]
    simp
  rw [weightedRotationMinimum,
    ContinuousLinearMap.re_trace_cfc_eq_sum
      (fun z => weightedPhaseMinimum a b (Real.arccos z.re)) C e (fun _ => 0) he]
  simp only [Complex.zero_re, Real.arccos_zero, weightedPhaseMinimum, Real.cos_pi_div_two,
    mul_zero, Real.sin_pi_div_two, mul_one, ite_eq_right (not_le.mpr hb), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Among all ambient unitary transports onto the orthogonal complement,
the weighted nuclear optimizers are exactly the self-adjoint ones.
This includes arbitrary multiplicities and the zero-dimensional space. -/
theorem minimizing_weighted_transport_orthogonalComplement_iff_selfAdjoint_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K : Submodule ℂ E) (hKK : Module.finrank ℂ K = Module.finrank ℂ Kᗮ)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = Kᗮ) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K Kᗮ) ↔
      IsSelfAdjoint (T : E →L[ℂ] E) := by
  constructor
  · intro hatt
    change star (T : E →L[ℂ] E) = (T : E →L[ℂ] E)
    ext x
    exact (minimizing_weighted_transport_selfAdjoint_on_right_defect_complex
      a b hb hab K Kᗮ hKK T hT hatt x (by
        rw [cosine_orthogonalComplement_eq_zero_complex K]
        rfl)).symm
  · intro hself
    have hanti (x : E) : T (K.reflection x) = -K.reflection (T x) := by
      rw [(K.map_eq_iff_intertwines_reflection Kᗮ T).mp hT x,
        Submodule.reflection_orthogonal_apply]
    have htr := trace_eq_zero_of_anticommute_involution T.toLinearMap
      K.reflection K.reflection_involutive hanti
    have hcost := nuclear_weighted_selfAdjoint_unitary a b hb.le hab.le
      (Unitary.linearIsometryEquiv.symm T) hself
    change UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        a * Module.finrank ℂ E - b * (LinearMap.trace ℂ E T.toLinearMap).re at hcost
    rw [htr, Complex.zero_re, mul_zero, sub_zero] at hcost
    exact hcost.trans (weightedRotationMinimum_orthogonalComplement_complex a b hb K).symm

/-- For the literal Charbonnier cost, the complete complementary-pair
criterion is again self-adjointness, over all ambient unitary competitors. -/
theorem smoothed_transport_orthogonalComplement_isMin_iff_selfAdjoint_complex
    (tau : ℝ) (htau : 0 < tau)
    (K : Submodule ℂ E) (hKK : Module.finrank ℂ K = Module.finrank ℂ Kᗮ)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = Kᗮ) :
    (∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = Kᗮ →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap) ↔
      IsSelfAdjoint (T : E →L[ℂ] E) := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb : 0 < a⁻¹ := inv_pos.mpr ha0
  have hab : a⁻¹ < a := ((inv_lt_one₀ ha0).mpr ha).trans ha
  constructor
  · intro hmin
    exact (minimizing_weighted_transport_orthogonalComplement_iff_selfAdjoint_complex
      a a⁻¹ hb hab K hKK T hT).mp
      (smoothed_minimizer_weighted_cost_eq_complex tau htau K Kᗮ hKK T hT hmin)
  · intro hself S hS
    have hatt := (minimizing_weighted_transport_orthogonalComplement_iff_selfAdjoint_complex
      a a⁻¹ hb hab K hKK T hT).mpr hself
    obtain ⟨W, _, hW, hmin⟩ :=
      exists_unitary_minimizing_weighted_transport a a⁻¹ hb hab K Kᗮ hKK
    have hle : UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) ≤
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • S.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) := by
      rw [hatt, ← hW]
      exact hmin S hS
    have hTc := smoothedDisplacementCost_eq_weightedNuclear tau htau
      (Unitary.linearIsometryEquiv.symm T)
    have hSc := smoothedDisplacementCost_eq_weightedNuclear tau htau
      (Unitary.linearIsometryEquiv.symm S)
    change smoothedDisplacementCost tau T.toLinearMap = _ at hTc
    change smoothedDisplacementCost tau S.toLinearMap = _ at hSc
    rw [hTc, hSc]
    exact sub_le_sub_right hle _

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
