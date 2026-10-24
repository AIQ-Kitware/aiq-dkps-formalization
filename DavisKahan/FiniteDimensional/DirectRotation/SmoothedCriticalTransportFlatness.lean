/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCriticalFlatness
import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseTransport
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedQuarticStability
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSpectralCost
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# Failure of quadratic growth for actual critical planar transports

The tangent-circle flatness certificate is realized by actual unitary
transporters and the literal Charbonnier singular-value cost. The main
endpoint uses the established source and target complex lines at the exact
smoothed critical angle. Every neighborhood of the canonical planar rotation
contains nonzero feasible competitors violating any proposed positive
quadratic growth modulus.

This supplies the operator interpretation in the journal paper's critical
flatness proposition. It complements the unrestricted quartic lower bound;
the flatness calculation does not assert an optimal quartic coefficient.
-/

noncomputable section
open scoped InnerProductSpace ComplexConjugate
namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

private def unitPhaseIsometry (z : ℂ) (hz : ‖z‖ = 1) : E ≃ₗᵢ[ℂ] E where
  toLinearEquiv := DistribMulAction.toLinearEquiv ℂ E
    (Units.mk0 z (by intro h; simp [h] at hz))
  norm_map' x := by change ‖z • x‖ = ‖x‖; rw [norm_smul, hz, one_mul]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
private theorem unitPhaseIsometry_apply (z : ℂ) (hz : ‖z‖ = 1) (x : E) :
    unitPhaseIsometry z hz x = z • x := rfl

omit [CompleteSpace E] in
private theorem critical_phase_nuclear_cost (a b d : ℝ)
    (e : OrthonormalBasis (Fin 2) ℂ E) (R : E ≃ₗᵢ[ℂ] E)
    (hR0 : (a : ℂ) • R (e 0) = ((b : ℂ) + d * Complex.I) • e 0)
    (hR1 : (a : ℂ) • R (e 1) = ((b : ℂ) - d * Complex.I) • e 1)
    (z : ℂ) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • R.toLinearMap - ((b : ℂ) * z) • LinearMap.id) =
        twoFocusCost b d ((b : ℂ) * z) := by
  let lam : Fin 2 → ℂ := ![(b : ℂ) + d * Complex.I - (b : ℂ) * z,
    (b : ℂ) - d * Complex.I - (b : ℂ) * z]
  have heigen (i : Fin 2) :
      (((a : ℂ) • R.toLinearMap - ((b : ℂ) * z) • LinearMap.id : E →ₗ[ℂ] E)) (e i) =
        lam i • e i := by
    fin_cases i
    · change (a : ℂ) • R (e 0) - ((b : ℂ) * z) • e 0 = _
      rw [hR0, ← sub_smul]
      rfl
    · change (a : ℂ) • R (e 1) - ((b : ℂ) * z) • e 1 = _
      rw [hR1, ← sub_smul]
      rfl
  rw [nuclear_eq_sum_norm_eigenvalues e _ lam heigen, Fin.sum_univ_two]
  rfl

private theorem critical_phase_actual_cost (tau : ℝ) (htau : 0 < tau) (d : ℝ)
    (e : OrthonormalBasis (Fin 2) ℂ E) (R : E ≃ₗᵢ[ℂ] E)
    (hR0 : (smoothingRadius tau : ℂ) • R (e 0) =
      (((smoothingRadius tau)⁻¹ : ℝ) + d * Complex.I) • e 0)
    (hR1 : (smoothingRadius tau : ℂ) • R (e 1) =
      (((smoothingRadius tau)⁻¹ : ℝ) - d * Complex.I) • e 1)
    (z : ℂ) (hz : ‖z‖ = 1) :
    smoothedDisplacementCost tau
      ((R.trans (unitPhaseIsometry (conj z) (by simpa using hz))).toLinearMap) =
        twoFocusCost ((smoothingRadius tau)⁻¹) d
          ((((smoothingRadius tau)⁻¹ : ℝ) : ℂ) * z) - 2 * tau := by
  let S : E ≃ₗᵢ[ℂ] E := unitPhaseIsometry (conj z) (by simpa using hz)
  let W := R.trans S
  let a := smoothingRadius tau
  let b := a⁻¹
  let N := UnitarilyInvariantSeminorm.nuclear ℂ E E
  have hdim : Module.finrank ℂ E = 2 := by simpa using Module.finrank_eq_card_basis e.toBasis
  have hzz : z * conj z = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hfactor : ((a : ℂ) • R.toLinearMap - ((b : ℂ) * z) • LinearMap.id) ∘ₗ
      S.toLinearMap = (a : ℂ) • W.toLinearMap - (b : ℂ) • LinearMap.id := by
    ext x
    change (a : ℂ) • R ((conj z) • x) - ((b : ℂ) * z) • ((conj z) • x) =
      (a : ℂ) • ((conj z) • R x) - (b : ℂ) • x
    rw [R.map_smul, smul_smul]
    congr 1
    rw [smul_smul, mul_assoc, hzz, mul_one]
  have hn : N ((a : ℂ) • W.toLinearMap - (b : ℂ) • LinearMap.id) =
      twoFocusCost b d ((b : ℂ) * z) := by
    calc
      _ = N (((a : ℂ) • R.toLinearMap - ((b : ℂ) * z) • LinearMap.id) ∘ₗ S.toLinearMap) :=
        congrArg N hfactor.symm
      _ = N ((a : ℂ) • R.toLinearMap - ((b : ℂ) * z) • LinearMap.id) :=
        N.map_comp_linearIsometryEquiv S _
      _ = _ := critical_phase_nuclear_cost a b d e R hR0 hR1 z
  have hcost := smoothedDisplacementCost_eq_weightedNuclear tau htau
    (Unitary.linearIsometryEquiv.symm W)
  change smoothedDisplacementCost tau W.toLinearMap = _
  change smoothedDisplacementCost tau W.toLinearMap =
    N ((a : ℂ) • W.toLinearMap - (b : ℂ) • LinearMap.id) - Module.finrank ℂ E * tau at hcost
  rw [hcost, hn, hdim]
  simp [a, b]

omit [CompleteSpace E] in
private theorem critical_phase_frobenius_sq
    (e : OrthonormalBasis (Fin 2) ℂ E) (R : E ≃ₗᵢ[ℂ] E)
    (z : ℂ) (hz : ‖z‖ = 1) :
    UnitarilyInvariantSeminorm.frobenius ℂ E E
      ((R.trans (unitPhaseIsometry (conj z) (by simpa using hz))).toLinearMap -
        R.toLinearMap) ^ 2 = 2 * ‖z - 1‖ ^ 2 := by
  rw [UnitarilyInvariantSeminorm.sq_frobenius_apply e, Fin.sum_univ_two]
  have heq (i : Fin 2) :
      (((R.trans (unitPhaseIsometry (conj z) (by simpa using hz))).toLinearMap -
        R.toLinearMap) (e i)) = (conj z - 1) • R (e i) := by
    change (conj z) • R (e i) - R (e i) = _
    rw [sub_smul, one_smul]
  rw [heq, heq, norm_smul, norm_smul, R.norm_map, R.norm_map,
    e.norm_eq_one, e.norm_eq_one, mul_one]
  have hnorm : ‖conj z - 1‖ = ‖z - 1‖ := by
    rw [show conj z - 1 = conj (z - 1) by simp, Complex.norm_conj]
  rw [hnorm]
  ring

/-- Literal spectral cost on a critical complex plane has no positive
quadratic growth modulus, even when competitors are required to transport
the same source subspace and remain arbitrarily close to the rotation. -/
theorem critical_planar_transport_no_quadratic_modulus
    (tau : ℝ) (htau : 0 < tau) (d : ℝ) (hd : 0 < d)
    (e : OrthonormalBasis (Fin 2) ℂ E) (R : E ≃ₗᵢ[ℂ] E)
    (hR0 : (smoothingRadius tau : ℂ) • R (e 0) =
      (((smoothingRadius tau)⁻¹ : ℝ) + d * Complex.I) • e 0)
    (hR1 : (smoothingRadius tau : ℂ) • R (e 1) =
      (((smoothingRadius tau)⁻¹ : ℝ) - d * Complex.I) • e 1)
    (U : Submodule ℂ E) (c radius : ℝ) (hc : 0 < c) (hradius : 0 < radius) :
    ∃ W : E ≃ₗᵢ[ℂ] E, U.map W.toLinearMap = U.map R.toLinearMap ∧
      0 < UnitarilyInvariantSeminorm.frobenius ℂ E E (W.toLinearMap - R.toLinearMap) ∧
      UnitarilyInvariantSeminorm.frobenius ℂ E E (W.toLinearMap - R.toLinearMap) < radius ∧
      smoothedDisplacementCost tau W.toLinearMap -
          smoothedDisplacementCost tau R.toLinearMap <
        c * UnitarilyInvariantSeminorm.frobenius ℂ E E
          (W.toLinearMap - R.toLinearMap) ^ 2 := by
  let b := (smoothingRadius tau)⁻¹
  have hb : 0 < b := inv_pos.mpr (lt_trans zero_lt_one (one_lt_smoothingRadius tau htau))
  obtain ⟨z, hz, hchord, hsmall, hcost⟩ := critical_phase_no_quadratic_modulus
    b d (2 * c) (radius / 2) hb hd (by positivity) (by positivity)
  let W := R.trans (unitPhaseIsometry (conj z) (by simpa using hz))
  let D := UnitarilyInvariantSeminorm.frobenius ℂ E E (W.toLinearMap - R.toLinearMap)
  have hD0 : 0 ≤ D := apply_nonneg _ _
  have hDsq : D ^ 2 = 2 * ‖z - 1‖ ^ 2 := critical_phase_frobenius_sq e R z hz
  have hDpos : 0 < D := by nlinarith [sq_pos_of_pos hchord]
  have hDbound : D ≤ 2 * ‖z - 1‖ := by
    nlinarith [sq_pos_of_pos hchord]
  have hWmap : W.toLinearMap = (conj z) • R.toLinearMap := by ext x; rfl
  have hznz : conj z ≠ 0 := by
    intro h
    have hz0 : z = 0 := by simpa using congrArg conj h
    simp [hz0] at hz
  have hbase := critical_phase_actual_cost tau htau d e R hR0 hR1 1 (by simp)
  have hWone : R.trans (unitPhaseIsometry (conj (1 : ℂ)) (by simp)) = R := by
    ext x
    change conj (1 : ℂ) • R x = R x
    simp
  rw [hWone] at hbase
  have hfocal : twoFocusCost b d ((b : ℂ) * 1) = 2 * d := by
    rw [mul_one, twoFocusCost_ofReal]
    simp [Real.sqrt_sq_eq_abs, abs_of_pos hd]
  have hactual := critical_phase_actual_cost tau htau d e R hR0 hR1 z hz
  change smoothedDisplacementCost tau W.toLinearMap =
    twoFocusCost b d ((b : ℂ) * z) - 2 * tau at hactual
  change smoothedDisplacementCost tau R.toLinearMap =
    twoFocusCost b d ((b : ℂ) * 1) - 2 * tau at hbase
  rw [hfocal] at hbase
  refine ⟨W, ?_, hDpos, ?_, ?_⟩
  · rw [hWmap, Submodule.map_smul _ _ _ hznz]
  · change D < radius
    linarith
  · rw [hactual, hbase]
    change twoFocusCost b d ((b : ℂ) * z) - 2 * tau - (2 * d - 2 * tau) < c * D ^ 2
    rw [hDsq]
    nlinarith only [hcost]


open TauCeti.DavisKahan1970.Section4Examples

private theorem scalarPhaseTransport_zero_scaled_basis (a theta : ℝ) (i : Fin 2) :
    (a : ℂ) • SchattenPhaseTransition.scalarPhaseTransport theta 0
      (EuclideanSpace.basisFun (Fin 2) ℂ i) =
      (if i = 0 then ((a * Real.cos theta : ℝ) : ℂ) + (a * Real.sin theta) * Complex.I
        else ((a * Real.cos theta : ℝ) : ℂ) - (a * Real.sin theta) * Complex.I) •
      (EuclideanSpace.basisFun (Fin 2) ℂ i) := by
  change ((a : ℂ) • (SchattenPhaseTransition.scalarPhaseTransport theta 0).toLinearMap)
    (EuclideanSpace.basisFun (Fin 2) ℂ i) = _
  rw [SchattenPhaseTransition.scalarPhaseTransport_toLinearMap,
    example42Competitor_eq_phase_smul, example42Phase_zero, one_smul]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [example42DirectRotation, example42Phase, Matrix.toLpLin_apply,
      EuclideanSpace.basisFun_apply] <;> ring

/-- At the exact smoothed critical angle, actual unitary transports of the
established source and target complex lines violate every local positive
quadratic growth bound around the canonical planar rotation. -/
theorem smoothed_critical_planar_no_quadratic_growth
    (tau : ℝ) (htau : 0 < tau) (c radius : ℝ) (hc : 0 < c) (hradius : 0 < radius) :
    let theta := smoothedCriticalAngle tau
    let R := SchattenPhaseTransition.scalarPhaseTransport theta 0
    ∃ W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane,
      ComplexTraceOptimality.sourceLine.map W.toLinearMap =
        ComplexTraceOptimality.targetLine theta ∧
      0 < UnitarilyInvariantSeminorm.frobenius ℂ ComplexPlane ComplexPlane
        (W.toLinearMap - R.toLinearMap) ∧
      UnitarilyInvariantSeminorm.frobenius ℂ ComplexPlane ComplexPlane
        (W.toLinearMap - R.toLinearMap) < radius ∧
      smoothedDisplacementCost tau W.toLinearMap -
          smoothedDisplacementCost tau R.toLinearMap <
        c * UnitarilyInvariantSeminorm.frobenius ℂ ComplexPlane ComplexPlane
          (W.toLinearMap - R.toLinearMap) ^ 2 := by
  let a := smoothingRadius tau
  let theta := smoothedCriticalAngle tau
  let R := SchattenPhaseTransition.scalarPhaseTransport theta 0
  have ha1 : 1 < a := one_lt_smoothingRadius tau htau
  have ha : 0 < a := zero_lt_one.trans ha1
  have hb : 0 < a⁻¹ := inv_pos.mpr ha
  have hb1 : a⁻¹ < 1 := (inv_lt_one₀ ha).mpr ha1
  have hθ : theta ∈ Set.Icc 0 (Real.pi / 2) := smoothedCriticalAngle_mem_Icc tau
  have hcos : Real.cos theta = (a⁻¹) ^ 2 := cos_smoothedCriticalAngle tau htau
  have hθpos : 0 < theta := by
    apply lt_of_le_of_ne hθ.1
    intro hzero
    have hz : Real.cos theta = 1 := by rw [← hzero]; simp
    nlinarith
  have hsin : 0 < Real.sin theta := Real.sin_pos_of_pos_of_lt_pi hθpos
    (lt_of_le_of_lt hθ.2 (by linarith [Real.pi_pos]))
  have hreal : a * Real.cos theta = a⁻¹ := by
    rw [hcos]
    field_simp
  have hR0 := scalarPhaseTransport_zero_scaled_basis a theta 0
  have hR1 := scalarPhaseTransport_zero_scaled_basis a theta 1
  simp only [ite_true, hreal] at hR0
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, hreal] at hR1
  obtain ⟨W, hmap, hpos, hnear, hcost⟩ := critical_planar_transport_no_quadratic_modulus
    tau htau (a * Real.sin theta) (mul_pos ha hsin)
    (EuclideanSpace.basisFun (Fin 2) ℂ) R
    (by simpa only [Complex.ofReal_mul] using hR0)
    (by simpa only [Complex.ofReal_mul] using hR1)
    ComplexTraceOptimality.sourceLine c radius hc hradius
  refine ⟨W, ?_, hpos, hnear, hcost⟩
  rw [hmap]
  exact SchattenPhaseTransition.scalarPhaseTransport_transports theta 0

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
