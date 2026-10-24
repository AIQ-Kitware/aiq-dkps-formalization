/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCommutingCorrection
import ForTauCeti.Analysis.InnerProductSpace.NuclearTrace

/-!
# Quartic stability at the smoothed transport transition

A family of rotated nuclear support functionals gives a root growth
inequality on the critical isoclinic family. It covers every transporter,
including those mixing the principal planes. The explicit critical rotation
has a positive cosine scalar and a source-reflection-reversed quarter turn.
The fourth-power error certificate remains nontrivial when the strict
subcritical quadratic coefficient vanishes.

The underlying support and trace identities are classical. Their application
to the exact constrained critical transport problem is the research extension.
-/

noncomputable section
open scoped InnerProductSpace
namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
 [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
private theorem rotation_mem_unitary (J : unitary (E →L[ℂ] E))
    (hJ : star (J : E →L[ℂ] E) = -(J : E →L[ℂ] E))
    (u v : ℝ) (huv : u ^ 2 + v ^ 2 = 1) :
    (u : ℂ) • (J : E →L[ℂ] E) + (v : ℂ) • (1 : E →L[ℂ] E) ∈
      unitary (E →L[ℂ] E) := by
  have hsq : (J : E →L[ℂ] E) * (J : E →L[ℂ] E) = -1 := by
    have h := Unitary.coe_star_mul_self J
    rw [hJ, neg_mul] at h
    exact neg_eq_iff_eq_neg.mp h
  have huvC : (u : ℂ) ^ 2 + (v : ℂ) ^ 2 = 1 := by exact_mod_cast huv
  have hstar (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  have heq : (u : ℂ) • (J : E →L[ℂ] E) + (v : ℂ) • (1 : E →L[ℂ] E) ∈
      unitary (E →L[ℂ] E) := by
    constructor
    · simp only [star_add, star_smul, hstar, star_one, hJ,
        add_mul, mul_add, smul_mul_smul_comm, neg_mul,
        mul_one, one_mul, hsq, smul_neg]
      calc
        _ = ((u : ℂ) ^ 2 + (v : ℂ) ^ 2) • (1 : E →L[ℂ] E) := by module
        _ = 1 := by rw [huvC, one_smul]
    · simp only [star_add, star_smul, hstar, star_one, hJ,
        add_mul, mul_add, smul_mul_smul_comm, mul_neg,
        mul_one, one_mul, hsq, smul_neg]
      calc
        _ = ((u : ℂ) ^ 2 + (v : ℂ) ^ 2) • (1 : E →L[ℂ] E) := by module
        _ = 1 := by rw [huvC, one_smul]
  exact heq

/-- A two-dimensional family of unitary support functionals yields a root
bound for a quarter-turn residual. -/
theorem nuclear_quarterTurn_root_bound (J : unitary (E →L[ℂ] E))
    (hJ : star (J : E →L[ℂ] E) = -(J : E →L[ℂ] E))
    (Z : E →L[ℂ] E)
    (htrJ : LinearMap.trace ℂ E (J : E →L[ℂ] E).toLinearMap = 0)
    (htrJZ : LinearMap.trace ℂ E
      ((J : E →L[ℂ] E).toLinearMap * Z.toLinearMap) = 0)
    (b d : ℝ) :
    Real.sqrt (((Module.finrank ℂ E : ℝ) * d) ^ 2 +
        (b * (Module.finrank ℂ E - (LinearMap.trace ℂ E Z.toLinearMap).re)) ^ 2) ≤
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((d : ℂ) • (J : E →L[ℂ] E).toLinearMap +
          (b : ℂ) • (LinearMap.id - Z.toLinearMap)) := by
  let n : ℝ := Module.finrank ℂ E
  let L := n * d
  let x := b * (n - (LinearMap.trace ℂ E Z.toLinearMap).re)
  let D := Real.sqrt (L ^ 2 + x ^ 2)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  by_cases hD : D = 0
  · change D ≤ _
    rw [hD]
    exact apply_nonneg (UnitarilyInvariantSeminorm.nuclear ℂ E E) _
  have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hD)
  have hDsq : D ^ 2 = L ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  let u := L / D
  let v := x / D
  have huv : u ^ 2 + v ^ 2 = 1 := by
    dsimp only [u, v]
    field_simp
    exact hDsq.symm
  let T : unitary (E →L[ℂ] E) :=
    ⟨(-u : ℂ) • (J : E →L[ℂ] E) + (v : ℂ) • (1 : E →L[ℂ] E),
      by simpa only [Complex.ofReal_neg] using
        rotation_mem_unitary J hJ (-u) v (by nlinarith [huv])⟩
  let j := (J : E →L[ℂ] E).toLinearMap
  let M := (d : ℂ) • j + (b : ℂ) • (LinearMap.id - Z.toLinearMap)
  have hsq : j * j = -1 := by
    have h := Unitary.coe_star_mul_self J
    rw [hJ, neg_mul] at h
    have h' := neg_eq_iff_eq_neg.mp h
    exact congrArg ContinuousLinearMap.toLinearMap h'
  have hprod : (Unitary.linearIsometryEquiv T).toLinearMap * M =
      ((u * d + v * b : ℝ) : ℂ) • (1 : E →ₗ[ℂ] E) +
      ((v * d - u * b : ℝ) : ℂ) • j +
      ((u * b : ℝ) : ℂ) • (j * Z.toLinearMap) -
      ((v * b : ℝ) : ℂ) • Z.toLinearMap := by
    change ((-u : ℂ) • j + (v : ℂ) • (1 : E →ₗ[ℂ] E)) *
      ((d : ℂ) • j + (b : ℂ) • (1 - Z.toLinearMap)) = _
    simp only [add_mul, mul_add, mul_sub, smul_mul_smul_comm,
      mul_one, one_mul, hsq, smul_neg]
    push_cast
    module
  have htrace : (LinearMap.trace ℂ E
      ((Unitary.linearIsometryEquiv T).toLinearMap * M)).re = u * L + v * x := by
    rw [hprod]
    simp only [map_sub, map_add, map_smul, LinearMap.trace_one]
    simp [j, htrJ, htrJZ, n, L, x, Complex.mul_re]
    ring
  have hs := re_trace_isometry_comp_le_nuclear (Unitary.linearIsometryEquiv T) M
  change (LinearMap.trace ℂ E
    ((Unitary.linearIsometryEquiv T).toLinearMap * M)).re ≤ _ at hs
  rw [htrace] at hs
  have hval : u * L + v * x = D := by
    dsimp only [u, v]
    field_simp
    nlinarith [hDsq]
  rw [hval] at hs
  exact hs


omit [CompleteSpace E] in
theorem trace_defect_eq_sq_frobenius_div_two (Z : E ≃ₗᵢ[ℂ] E) :
    (Module.finrank ℂ E : ℝ) - (LinearMap.trace ℂ E Z.toLinearMap).re =
      UnitarilyInvariantSeminorm.frobenius ℂ E E
        (Z.toLinearMap - LinearMap.id) ^ 2 / 2 := by
  let e := stdOrthonormalBasis ℂ E
  have hdelta (i) : ‖(Z.toLinearMap - (LinearMap.id : E →ₗ[ℂ] E)) (e i)‖ ^ 2 =
      2 * (1 - (⟪e i, Z (e i)⟫_ℂ).re) := by
    have h := norm_sub_sq (𝕜 := ℂ) (e i) (Z (e i))
    rw [e.norm_eq_one, Z.norm_map, e.norm_eq_one] at h
    change ‖e i - Z (e i)‖ ^ 2 = 1 ^ 2 - 2 * (⟪e i, Z (e i)⟫_ℂ).re + 1 ^ 2 at h
    change ‖Z (e i) - e i‖ ^ 2 = _
    rw [norm_sub_rev]
    linarith
  rw [UnitarilyInvariantSeminorm.sq_frobenius_apply e,
    LinearMap.trace_eq_sum_inner _ e]
  rw [show (∑ i, ⟪e i, Z.toLinearMap (e i)⟫_ℂ).re =
    ∑ i, (⟪e i, Z (e i)⟫_ℂ).re from map_sum Complex.reAddGroupHom _ _]
  simp only [hdelta, mul_sub, mul_one, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  rw [← Finset.mul_sum]
  ring

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
private theorem trace_eq_zero_of_involution_conj_neg
    (F : E →ₗ[ℂ] E) (hF : F * F = 1) (A : E →ₗ[ℂ] E)
    (hanti : F * A * F = -A) : LinearMap.trace ℂ E A = 0 := by
  have h := LinearMap.trace_mul_comm ℂ F (A * F)
  rw [← mul_assoc, hanti, map_neg, mul_assoc, hF, mul_one] at h
  linear_combination -(1 / 2 : ℂ) * h

/-- On a reflection commutant, the critical residual has a quartic
Frobenius lower bound inside an explicit square root. -/
theorem nuclear_quarterTurn_root_bound_of_commute
    (J : unitary (E →L[ℂ] E))
    (hJ : star (J : E →L[ℂ] E) = -(J : E →L[ℂ] E))
    (F : E →ₗ[ℂ] E) (hF : F * F = 1)
    (hanti : F * (J : E →L[ℂ] E).toLinearMap * F =
      -(J : E →L[ℂ] E).toLinearMap)
    (Z : E ≃ₗᵢ[ℂ] E) (hcomm : Commute F Z.toLinearMap) (b d : ℝ) :
    Real.sqrt (((Module.finrank ℂ E : ℝ) * d) ^ 2 +
        (b / 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
          (Z.toLinearMap - LinearMap.id) ^ 2) ^ 2) ≤
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((d : ℂ) • (J : E →L[ℂ] E).toLinearMap +
          (b : ℂ) • (LinearMap.id - Z.toLinearMap)) := by
  let j := (J : E →L[ℂ] E).toLinearMap
  have htrJ : LinearMap.trace ℂ E j = 0 :=
    trace_eq_zero_of_involution_conj_neg F hF j hanti
  have hantiZ : F * (j * Z.toLinearMap) * F = -(j * Z.toLinearMap) := by
    calc
      _ = F * j * (Z.toLinearMap * F) := by noncomm_ring
      _ = F * j * (F * Z.toLinearMap) := by rw [hcomm.eq.symm]
      _ = (F * j * F) * Z.toLinearMap := by noncomm_ring
      _ = _ := by rw [hanti, neg_mul]
  have htrJZ : LinearMap.trace ℂ E (j * Z.toLinearMap) = 0 :=
    trace_eq_zero_of_involution_conj_neg F hF _ hantiZ
  have h := nuclear_quarterTurn_root_bound J hJ
    Z.toContinuousLinearEquiv.toContinuousLinearMap htrJ htrJZ b d
  change Real.sqrt (((Module.finrank ℂ E : ℝ) * d) ^ 2 +
      (b * (Module.finrank ℂ E - (LinearMap.trace ℂ E Z.toLinearMap).re)) ^ 2) ≤ _ at h
  rw [trace_defect_eq_sq_frobenius_div_two] at h
  have hcoeff : b / 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
      (Z.toLinearMap - LinearMap.id) ^ 2 =
      b * (UnitarilyInvariantSeminorm.frobenius ℂ E E
        (Z.toLinearMap - LinearMap.id) ^ 2 / 2) := by ring
  rw [hcoeff]
  convert h using 1
  congr 1



/-- The root certificate applies to every ambient transporter in a critical
isoclinic rotation model, including competitors mixing all planes. -/
theorem weighted_critical_transport_root_bound
    (a b d : ℝ) (J : unitary (E →L[ℂ] E))
    (hJ : star (J : E →L[ℂ] E) = -(J : E →L[ℂ] E))
    (K : Submodule ℂ E) (R : E ≃ₗᵢ[ℂ] E)
    (hanti : K.reflection.toLinearMap * (J : E →L[ℂ] E).toLinearMap *
      K.reflection.toLinearMap = -(J : E →L[ℂ] E).toLinearMap)
    (hcrit : (a : ℂ) • R.toLinearMap - (b : ℂ) • LinearMap.id =
      (d : ℂ) • (J : E →L[ℂ] E).toLinearMap)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = K.map R.toLinearMap) :
    Real.sqrt (((Module.finrank ℂ E : ℝ) * d) ^ 2 +
        (b / 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
          (T.toLinearMap - R.toLinearMap) ^ 2) ^ 2) ≤
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) := by
  let Z := R.trans T.symm
  have hpres : K.map Z.toLinearMap = K := correction_preserves_subspace K R T hT
  have hcommx := (K.map_eq_iff_intertwines_reflection K Z).mp hpres
  have hcomm : Commute K.reflection.toLinearMap Z.toLinearMap := by
    ext x
    exact (hcommx x).symm
  have hF : K.reflection.toLinearMap * K.reflection.toLinearMap = 1 := by
    ext x
    exact K.reflection_involutive x
  have hg := nuclear_quarterTurn_root_bound_of_commute J hJ
    K.reflection.toLinearMap hF hanti Z hcomm b d
  let N := UnitarilyInvariantSeminorm.nuclear ℂ E E
  let F := UnitarilyInvariantSeminorm.frobenius ℂ E E
  have hres : (d : ℂ) • (J : E →L[ℂ] E).toLinearMap +
      (b : ℂ) • (LinearMap.id - Z.toLinearMap) =
        (a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap := by
    rw [← hcrit]
    module
  rw [hres] at hg
  have hfactor : (a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap =
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) ∘ₗ Z.toLinearMap := by
    ext x
    simp [Z]
  have hN : N ((a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap) =
      N ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) := by
    rw [hfactor]
    exact N.map_comp_linearIsometryEquiv Z _
  have hFfactor : T.toLinearMap ∘ₗ (Z.toLinearMap - LinearMap.id) =
      R.toLinearMap - T.toLinearMap := by ext x; simp [Z]
  have hFnorm : F (Z.toLinearMap - LinearMap.id) = F (T.toLinearMap - R.toLinearMap) := by
    calc
      _ = F (T.toLinearMap ∘ₗ (Z.toLinearMap - LinearMap.id)) :=
        (F.map_linearIsometryEquiv_comp T _).symm
      _ = F (R.toLinearMap - T.toLinearMap) := congrArg F hFfactor
      _ = _ := by rw [← neg_sub, map_neg_eq_map]
  change Real.sqrt (((Module.finrank ℂ E : ℝ) * d) ^ 2 +
      (b / 2 * F (Z.toLinearMap - LinearMap.id) ^ 2) ^ 2) ≤
        N ((a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap) at hg
  rw [hFnorm, hN] at hg
  exact hg


private theorem nuclear_unitary_eq_finrank (J : unitary (E →L[ℂ] E)) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E (J : E →L[ℂ] E).toLinearMap =
      Module.finrank ℂ E := by
  let N := UnitarilyInvariantSeminorm.nuclear ℂ E E
  let e := stdOrthonormalBasis ℂ E
  have hid : N (LinearMap.id : E →ₗ[ℂ] E) = Module.finrank ℂ E := by
    have h := nuclear_eq_sum_norm_eigenvalues e (LinearMap.id : E →ₗ[ℂ] E)
      (fun _ => (1 : ℂ)) (fun i => by simp)
    change N LinearMap.id = ∑ i : Fin (Module.finrank ℂ E), ‖(1 : ℂ)‖ at h
    simpa only [norm_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using h
  have hmap : (J : E →L[ℂ] E).toLinearMap =
      (Unitary.linearIsometryEquiv J).toLinearMap := by ext x; rfl
  rw [hmap]
  have h := N.map_linearIsometryEquiv_comp (Unitary.linearIsometryEquiv J)
    (LinearMap.id : E →ₗ[ℂ] E)
  simp only [LinearMap.comp_id] at h
  convert h.trans hid using 1
  congr 1

/-- At a homogeneous critical rotation, every admissible transporter obeys
an explicit root growth inequality. In particular the minimum remains isolated
although the quadratic certificate vanishes. -/
theorem smoothed_critical_transport_root_growth
    (tau d : ℝ) (hτ : 0 < tau) (hd : 0 ≤ d)
    (J : unitary (E →L[ℂ] E))
    (hJ : star (J : E →L[ℂ] E) = -(J : E →L[ℂ] E))
    (K : Submodule ℂ E) (R : E ≃ₗᵢ[ℂ] E)
    (hanti : K.reflection.toLinearMap * (J : E →L[ℂ] E).toLinearMap *
      K.reflection.toLinearMap = -(J : E →L[ℂ] E).toLinearMap)
    (hcrit : (smoothingRadius tau : ℂ) • R.toLinearMap -
      (((smoothingRadius tau)⁻¹ : ℝ) : ℂ) • LinearMap.id =
        (d : ℂ) • (J : E →L[ℂ] E).toLinearMap)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = K.map R.toLinearMap) :
    Real.sqrt (((Module.finrank ℂ E : ℝ) * d) ^ 2 +
        ((smoothingRadius tau)⁻¹ / 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
          (T.toLinearMap - R.toLinearMap) ^ 2) ^ 2) - Module.finrank ℂ E * d ≤
      smoothedDisplacementCost tau T.toLinearMap -
        smoothedDisplacementCost tau R.toLinearMap := by
  have hg := weighted_critical_transport_root_bound
    (smoothingRadius tau) (smoothingRadius tau)⁻¹ d J hJ K R hanti hcrit T hT
  have hcost (V : E ≃ₗᵢ[ℂ] E) : smoothedDisplacementCost tau V.toLinearMap =
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((smoothingRadius tau : ℂ) • V.toLinearMap -
          (((smoothingRadius tau)⁻¹ : ℝ) : ℂ) • LinearMap.id) -
        Module.finrank ℂ E * tau := by
    have h := smoothedDisplacementCost_eq_weightedNuclear tau hτ
      (Unitary.linearIsometryEquiv.symm V)
    convert h using 1 <;> rfl
  have hRcost : smoothedDisplacementCost tau R.toLinearMap =
      (Module.finrank ℂ E : ℝ) * d - Module.finrank ℂ E * tau := by
    rw [hcost, hcrit, map_smul_eq_mul,
      nuclear_unitary_eq_finrank]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
    ring
  rw [hcost, hRcost]
  linarith

/-- A near-minimizer in the critical model has an explicit fourth-power
error bound. -/
theorem smoothed_critical_transport_error_bound
    (tau d epsilon : ℝ) (hτ : 0 < tau) (hd : 0 ≤ d)
    (J : unitary (E →L[ℂ] E))
    (hJ : star (J : E →L[ℂ] E) = -(J : E →L[ℂ] E))
    (K : Submodule ℂ E) (R : E ≃ₗᵢ[ℂ] E)
    (hanti : K.reflection.toLinearMap * (J : E →L[ℂ] E).toLinearMap *
      K.reflection.toLinearMap = -(J : E →L[ℂ] E).toLinearMap)
    (hcrit : (smoothingRadius tau : ℂ) • R.toLinearMap -
      (((smoothingRadius tau)⁻¹ : ℝ) : ℂ) • LinearMap.id =
        (d : ℂ) • (J : E →L[ℂ] E).toLinearMap)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = K.map R.toLinearMap)
    (hgap : smoothedDisplacementCost tau T.toLinearMap -
      smoothedDisplacementCost tau R.toLinearMap ≤ epsilon) :
    ((smoothingRadius tau)⁻¹) ^ 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
        (T.toLinearMap - R.toLinearMap) ^ 4 ≤
      4 * epsilon * (2 * Module.finrank ℂ E * d + epsilon) := by
  have hg := smoothed_critical_transport_root_growth tau d hτ hd J hJ K R hanti hcrit T hT
  let L : ℝ := Module.finrank ℂ E * d
  let x := (smoothingRadius tau)⁻¹ / 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
    (T.toLinearMap - R.toLinearMap) ^ 2
  have hroot : Real.sqrt (L ^ 2 + x ^ 2) ≤ L + epsilon := by
    change Real.sqrt (L ^ 2 + x ^ 2) - L ≤ _ at hg
    linarith
  have hsq : L ^ 2 + x ^ 2 ≤ (L + epsilon) ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg (L ^ 2 + x ^ 2)) hroot 2
    rwa [Real.sq_sqrt (by positivity)] at h
  dsimp only [L, x] at hsq
  nlinarith only [hsq]

/-- The positive imaginary coefficient of the critical weighted rotation. -/
def criticalSmoothedLength (tau : ℝ) : ℝ :=
  Real.sqrt ((smoothingRadius tau) ^ 2 - ((smoothingRadius tau)⁻¹) ^ 2)

private theorem criticalSmoothedLength_radicand_pos (tau : ℝ) (hτ : 0 < tau) :
    0 < (smoothingRadius tau) ^ 2 - ((smoothingRadius tau)⁻¹) ^ 2 := by
  have ha := one_lt_smoothingRadius tau hτ
  have ha0 : 0 < smoothingRadius tau := lt_trans zero_lt_one ha
  have hb0 : 0 < (smoothingRadius tau)⁻¹ := inv_pos.mpr ha0
  have hb : (smoothingRadius tau)⁻¹ < smoothingRadius tau :=
    lt_trans ((inv_lt_one₀ ha0).mpr ha) ha
  nlinarith

theorem criticalSmoothedLength_pos (tau : ℝ) (hτ : 0 < tau) :
    0 < criticalSmoothedLength tau := Real.sqrt_pos.mpr (criticalSmoothedLength_radicand_pos tau hτ)

theorem criticalSmoothedLength_sq (tau : ℝ) (hτ : 0 < tau) :
    criticalSmoothedLength tau ^ 2 =
      (smoothingRadius tau) ^ 2 - ((smoothingRadius tau)⁻¹) ^ 2 :=
  Real.sq_sqrt (criticalSmoothedLength_radicand_pos tau hτ).le

/-- The unitary rotating each source plane through the critical angle. -/
def criticalSmoothedRotation (tau : ℝ) (hτ : 0 < tau)
    (J : unitary (E →L[ℂ] E))
    (hJ : star (J : E →L[ℂ] E) = -(J : E →L[ℂ] E)) : E ≃ₗᵢ[ℂ] E := by
  let a := smoothingRadius tau
  let b := a⁻¹
  let d := criticalSmoothedLength tau
  have ha : a ≠ 0 := ne_of_gt (lt_trans zero_lt_one (one_lt_smoothingRadius tau hτ))
  have hsq : (d / a) ^ 2 + (b / a) ^ 2 = 1 := by
    have hd := criticalSmoothedLength_sq tau hτ
    change d ^ 2 = a ^ 2 - b ^ 2 at hd
    field_simp
    nlinarith only [hd]
  exact Unitary.linearIsometryEquiv
    ⟨((d / a : ℝ) : ℂ) • (J : E →L[ℂ] E) + ((b / a : ℝ) : ℂ) • 1,
      rotation_mem_unitary J hJ (d / a) (b / a) hsq⟩

omit [FiniteDimensional ℂ E] in
theorem criticalSmoothedRotation_normal_form (tau : ℝ) (hτ : 0 < tau)
    (J : unitary (E →L[ℂ] E))
    (hJ : star (J : E →L[ℂ] E) = -(J : E →L[ℂ] E)) :
    (smoothingRadius tau : ℂ) • (criticalSmoothedRotation tau hτ J hJ).toLinearMap -
      (((smoothingRadius tau)⁻¹ : ℝ) : ℂ) • LinearMap.id =
        (criticalSmoothedLength tau : ℂ) • (J : E →L[ℂ] E).toLinearMap := by
  let a := smoothingRadius tau
  have ha : a ≠ 0 := ne_of_gt (lt_trans zero_lt_one (one_lt_smoothingRadius tau hτ))
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hd : (a : ℂ) * ((criticalSmoothedLength tau / a : ℝ) : ℂ) =
      (criticalSmoothedLength tau : ℂ) := by push_cast; field_simp [haC]
  have hb : (a : ℂ) * ((a⁻¹ / a : ℝ) : ℂ) = ((a⁻¹ : ℝ) : ℂ) := by push_cast; field_simp [haC]
  ext x
  change (a : ℂ) • (((criticalSmoothedLength tau / a : ℝ) : ℂ) •
    (J : E →L[ℂ] E) x + ((a⁻¹ / a : ℝ) : ℂ) • x) - ((a⁻¹ : ℝ) : ℂ) • x = _
  rw [smul_add, smul_smul, smul_smul, hd, hb]
  abel

/-- A fourth-power error certificate at the actual critical rotation,
without a supplied principal-plane chart. -/
theorem criticalSmoothedRotation_error_bound
    (tau epsilon : ℝ) (hτ : 0 < tau)
    (J : unitary (E →L[ℂ] E))
    (hJ : star (J : E →L[ℂ] E) = -(J : E →L[ℂ] E))
    (K : Submodule ℂ E)
    (hanti : K.reflection.toLinearMap * (J : E →L[ℂ] E).toLinearMap *
      K.reflection.toLinearMap = -(J : E →L[ℂ] E).toLinearMap)
    (T : E ≃ₗᵢ[ℂ] E)
    (hT : K.map T.toLinearMap = K.map (criticalSmoothedRotation tau hτ J hJ).toLinearMap)
    (hgap : smoothedDisplacementCost tau T.toLinearMap -
      smoothedDisplacementCost tau (criticalSmoothedRotation tau hτ J hJ).toLinearMap ≤ epsilon) :
    ((smoothingRadius tau)⁻¹) ^ 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
        (T.toLinearMap - (criticalSmoothedRotation tau hτ J hJ).toLinearMap) ^ 4 ≤
      4 * epsilon * (2 * Module.finrank ℂ E * criticalSmoothedLength tau + epsilon) :=
  smoothed_critical_transport_error_bound tau (criticalSmoothedLength tau) epsilon hτ
    (criticalSmoothedLength_pos tau hτ).le J hJ K (criticalSmoothedRotation tau hτ J hJ)
    hanti (criticalSmoothedRotation_normal_form tau hτ J hJ) T hT hgap

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
