/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCriticalStability
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSubspaceStability
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCriticalAngle

/-!
# Quartic stability throughout the closed canonical regime

The nuclear support certificate can be selected at a parameter different
from the objective parameter. A small inward shift makes every dual weight
positive, at a second-order support error. Balancing these terms gives
quartic growth for all principal angles at or below the smoothed cutoff,
including mixed critical and strictly subcritical lists and fixed directions.

The final theorems use the literal displacement singular-value cost, the
accepted principal angles, and every admissible ambient unitary. They give
an explicit fourth-power objective-error certificate and uniqueness of the
canonical minimizer through the transition. The critical isoclinic family
has a sharper root certificate in `SmoothedCriticalStability`.
-/

public section

noncomputable section
namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
open scoped InnerProductSpace

private theorem shifted_denominator_bounds
    (a b t theta : ℝ) (hb : 0 < b) (hab : b < a)
    (ht : t ∈ Set.Icc 0 b) (hcos : b ≤ a * Real.cos theta) :
    let r := Real.sqrt ((a * Real.cos theta - t) ^ 2 + (a * Real.sin theta) ^ 2)
    a - t ≤ r ∧ r ≤ a := by
  dsimp only
  let r := Real.sqrt ((a * Real.cos theta - t) ^ 2 + (a * Real.sin theta) ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = (a * Real.cos theta - t) ^ 2 + (a * Real.sin theta) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have ha0 : 0 < a := hb.trans hab
  have hat : 0 ≤ a - t := sub_nonneg.mpr (ht.2.trans hab.le)
  have hc : a * Real.cos theta ≤ a := mul_le_of_le_one_right ha0.le (Real.cos_le_one _)
  have htrig := congrArg (fun x : ℝ => a ^ 2 * x) (Real.sin_sq_add_cos_sq theta)
  constructor
  · apply (sq_le_sq₀ hat hr0).mp
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hc)]
  · apply (sq_le_sq₀ hr0 ha0.le).mp
    have hct : 0 ≤ a * Real.cos theta - t := sub_nonneg.mpr (ht.2.trans hcos)
    nlinarith [mul_nonneg ht.1 hct, sq_nonneg t]

private theorem shifted_dualReal_lower
    (a b delta theta : ℝ) (hb : 0 < b) (hab : b < a)
    (hdelta : delta ∈ Set.Icc 0 b) (hcos : b ≤ a * Real.cos theta) :
    delta / a ≤ dualReal a (b - delta) theta := by
  obtain ⟨hrlo, hrhi⟩ := shifted_denominator_bounds a b (b - delta) theta hb hab
    ⟨by linarith [hdelta.2], by linarith [hdelta.1]⟩ hcos
  have ha0 : 0 < a := hb.trans hab
  have hrpos : 0 < Real.sqrt ((a * Real.cos theta - (b - delta)) ^ 2 +
      (a * Real.sin theta) ^ 2) := lt_of_lt_of_le (by linarith [hdelta.1] : 0 < a - (b - delta)) hrlo
  unfold dualReal
  rw [ite_eq_left (by linarith [hdelta.1] : b - delta ≤ a * Real.cos theta)]
  apply (div_le_div_iff₀ ha0 hrpos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hrhi hdelta.1]

private theorem shifted_support_deficit_le
    (a b delta theta : ℝ) (hb : 0 < b) (hab : b < a)
    (hdelta : delta ∈ Set.Icc 0 b) (hcos : b ≤ a * Real.cos theta) :
    weightedPhaseMinimum a b theta - weightedSupportValue a b (b - delta) theta ≤
      delta ^ 2 / (a - b) := by
  let u := a * Real.cos theta - (b - delta)
  let v := a * Real.sin theta
  let r := Real.sqrt (u ^ 2 + v ^ 2)
  let s := Real.sqrt ((u - delta) ^ 2 + v ^ 2)
  obtain ⟨hrlo, hrhi⟩ := shifted_denominator_bounds a b (b - delta) theta hb hab
    ⟨by linarith [hdelta.2], by linarith [hdelta.1]⟩ hcos
  have hrpos : 0 < r := lt_of_lt_of_le (by linarith [hdelta.1] : 0 < a - (b - delta)) hrlo
  have hrsq : r ^ 2 = u ^ 2 + v ^ 2 := Real.sq_sqrt (by positivity)
  have hssq : s ^ 2 = (u - delta) ^ 2 + v ^ 2 := Real.sq_sqrt (by positivity)
  have hcanonical : weightedPhaseMinimum a b theta = 2 * s := by
    rw [weightedPhaseMinimum, ite_eq_left hcos]
    congr 1
    apply congrArg Real.sqrt
    dsimp only [u, v]
    have htrig := congrArg (fun x : ℝ => a ^ 2 * x) (Real.sin_sq_add_cos_sq theta)
    nlinarith
  have hsupport : weightedSupportValue a b (b - delta) theta =
      2 * (u / r * (u - delta) + v / r * v) := by
    unfold weightedSupportValue dualReal dualImag
    simp only [ite_eq_left (by linarith [hdelta.1] : b - delta ≤ a * Real.cos theta)]
    change 2 * (u / r * (a * Real.cos theta - b) + v / r * v) = _
    congr 3
    dsimp only [u]
    ring
  rw [hcanonical, hsupport]
  have hnorm : 2 * r * s ≤ s ^ 2 + r ^ 2 := by nlinarith [sq_nonneg (s - r)]
  have hmul : (2 * s - 2 * (u / r * (u - delta) + v / r * v)) * r =
      2 * r * s - 2 * u * (u - delta) - 2 * v ^ 2 := by
    field_simp
    ring
  have hlocal : 2 * s - 2 * (u / r * (u - delta) + v / r * v) ≤ delta ^ 2 / r := by
    apply (le_div_iff₀ hrpos).mpr
    rw [hmul]
    nlinarith only [hnorm, hrsq, hssq]
  have hlow : a - b ≤ r := by linarith [hdelta.1]
  exact hlocal.trans (div_le_div_of_nonneg_left (sq_nonneg delta) (sub_pos.mpr hab) hlow)


variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E] [Fintype ι] [Fintype κ]

omit [CompleteSpace E] in
private theorem sq_frobenius_unitary_sub_id_le (Z : E ≃ₗᵢ[ℂ] E) :
    UnitarilyInvariantSeminorm.frobenius ℂ E E (Z.toLinearMap - LinearMap.id) ^ 2 ≤
      4 * Module.finrank ℂ E := by
  let e := stdOrthonormalBasis ℂ E
  rw [UnitarilyInvariantSeminorm.sq_frobenius_apply e]
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℂ E), (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h : ‖Z (e i) - e i‖ ≤ 2 := by
        calc
          _ ≤ ‖Z (e i)‖ + ‖e i‖ := norm_sub_le _ _
          _ = 2 := by rw [Z.norm_map, e.norm_eq_one]; norm_num
      change ‖Z (e i) - e i‖ ^ 2 ≤ 4
      nlinarith [norm_nonneg (Z (e i) - e i)]
    _ = _ := by simp; ring

omit [CompleteSpace E] in
private theorem shifted_weightedNuclear_growth
    (a b delta : ℝ) (hb : 0 < b) (hab : b < a)
    (hdelta : delta ∈ Set.Icc 0 b) (theta : ι → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Icc 0 (Real.pi / 2))
    (hsub : ∀ i, b ≤ a * Real.cos (theta i))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j))
    (J : E ≃ₗᵢ[ℂ] E) (hJ0 : ∀ i, J (e (.inl (0, i))) = e (.inl (1, i)))
    (Z : E ≃ₗᵢ[ℂ] E) (hcomm : ∀ x, Z (J x) = J (Z x)) :
    b * (delta / a) / 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
        (Z.toLinearMap - LinearMap.id) ^ 2 -
        Module.finrank ℂ E * delta ^ 2 / (2 * (a - b)) ≤
      UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z.toLinearMap) -
        UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • LinearMap.id) := by
  have hbeta0 : 0 ≤ b - delta := by linarith [hdelta.2]
  have hbetaa : b - delta < a := by linarith [hdelta.1]
  have hdiag (i) : (⟪e (.inl (0, i)), Z (e (.inl (0, i)))⟫_ℂ).im =
      (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).im := by
    have h := inner_diagonal_eq_of_commute J Z.toLinearMap hcomm (e (.inl (0, i)))
    rw [hJ0] at h
    exact (congrArg Complex.im h).symm
  have hraw := weightedNuclear_support_with_diagonal_defect a b (b - delta)
    hbeta0 hbetaa theta e A Z.toLinearMap hA0 hA1 hAf hdiag
  have hc : delta / a ≤ 1 := (div_le_one (hb.trans hab)).mpr (hdelta.2.trans hab.le)
  have henergy := mul_sq_frobenius_le_weightedDiagonalDefect a (b - delta) (delta / a)
    hc theta (fun i => shifted_dualReal_lower a b delta (theta i) hb hab hdelta (hsub i)) e Z
  have hscaled := mul_le_mul_of_nonneg_left henergy hb.le
  have hsum : (∑ i, weightedPhaseMinimum a b (theta i)) -
      (∑ i, weightedSupportValue a b (b - delta) (theta i)) ≤
        (Fintype.card ι : ℝ) * (delta ^ 2 / (a - b)) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : ι, delta ^ 2 / (a - b) := Finset.sum_le_sum fun i _ =>
        shifted_support_deficit_le a b delta (theta i) hb hab hdelta (hsub i)
      _ = _ := by simp
  have hdim : Module.finrank ℂ E = 2 * Fintype.card ι + Fintype.card κ := by
    rw [Module.finrank_eq_card_basis e.toBasis]
    simp
  have hdimR : (Module.finrank ℂ E : ℝ) =
      2 * (Fintype.card ι : ℝ) + (Fintype.card κ : ℝ) := by exact_mod_cast hdim
  have hcard : (Fintype.card ι : ℝ) ≤ (Module.finrank ℂ E : ℝ) / 2 := by
    rw [hdimR]
    nlinarith [Nat.cast_nonneg (Fintype.card κ) (α := ℝ)]
  have hdeficit := mul_le_mul_of_nonneg_right hcard
    (div_nonneg (sq_nonneg delta) (sub_pos.mpr hab).le)
  have hcan := weightedNuclear_identity_attains_of_subcritical a b hb hab theta hθ hsub
    e A hA0 hA1 hAf
  have hscaled' : b * (delta / a) / 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
      (Z.toLinearMap - LinearMap.id) ^ 2 ≤
        b * weightedDiagonalDefect a (b - delta) theta e Z.toLinearMap := by
    convert hscaled using 1
    ring
  have hdeficit' : (Fintype.card ι : ℝ) * (delta ^ 2 / (a - b)) ≤
      Module.finrank ℂ E * delta ^ 2 / (2 * (a - b)) := by
    convert hdeficit using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hcan]
  linarith only [hraw, hscaled', hsum, hdeficit']

omit [CompleteSpace E] in
/-- Quartic growth on every paired rotation model in the closed canonical regime. -/
theorem quartic_weightedNuclear_growth
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (theta : ι → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Icc 0 (Real.pi / 2))
    (hsub : ∀ i, b ≤ a * Real.cos (theta i))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j))
    (J : E ≃ₗᵢ[ℂ] E) (hJ0 : ∀ i, J (e (.inl (0, i))) = e (.inl (1, i)))
    (Z : E ≃ₗᵢ[ℂ] E) (hcomm : ∀ x, Z (J x) = J (Z x)) :
    3 * b ^ 2 * (a - b) * UnitarilyInvariantSeminorm.frobenius ℂ E E
        (Z.toLinearMap - LinearMap.id) ^ 4 ≤
      32 * a ^ 2 * Module.finrank ℂ E *
        (UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z.toLinearMap) -
          UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • LinearMap.id)) := by
  let D := UnitarilyInvariantSeminorm.frobenius ℂ E E (Z.toLinearMap - LinearMap.id)
  let n : ℝ := Module.finrank ℂ E
  let g := UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z.toLinearMap) -
    UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • LinearMap.id)
  have hbase := shifted_weightedNuclear_growth a b 0 hb hab ⟨le_rfl, hb.le⟩ theta hθ hsub
    e A hA0 hA1 hAf J hJ0 Z hcomm
  have hg : 0 ≤ g := by simpa only [zero_div, mul_zero, zero_mul, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero] using hbase
  have hD0 : 0 ≤ D := apply_nonneg _ _
  have hn0 : 0 ≤ n := by dsimp only [n]; positivity
  have hdiam : D ^ 2 ≤ 4 * n := sq_frobenius_unitary_sub_id_le Z
  change 3 * b ^ 2 * (a - b) * D ^ 4 ≤ 32 * a ^ 2 * n * g
  by_cases hD : D = 0
  · simp only [hD, zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero]
    positivity
  have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hD)
  have hn : 0 < n := by nlinarith [sq_pos_of_pos hDpos]
  have ha : 0 < a := hb.trans hab
  have htau : 0 < a - b := sub_pos.mpr hab
  let delta := b * (a - b) * D ^ 2 / (4 * a * n)
  have hdelta0 : 0 ≤ delta := by dsimp only [delta]; positivity
  have hdelta1 : delta ≤ b := by
    calc
      _ ≤ b * (a - b) * (4 * n) / (4 * a * n) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiam (by positivity)) (by positivity)
      _ = b * (a - b) / a := by field_simp
      _ ≤ b := (div_le_iff₀ ha).mpr (by nlinarith [sq_nonneg b])
  have hs := shifted_weightedNuclear_growth a b delta hb hab ⟨hdelta0, hdelta1⟩ theta hθ hsub
    e A hA0 hA1 hAf J hJ0 Z hcomm
  change b * (delta / a) / 2 * D ^ 2 - n * delta ^ 2 / (2 * (a - b)) ≤ g at hs
  have hid : b * (delta / a) / 2 * D ^ 2 - n * delta ^ 2 / (2 * (a - b)) =
      3 * b ^ 2 * (a - b) * D ^ 4 / (32 * a ^ 2 * n) := by
    dsimp only [delta]
    field_simp
    ring
  rw [hid] at hs
  have h := (div_le_iff₀ (by positivity : 0 < 32 * a ^ 2 * n)).mp hs
  nlinarith only [h]

/-- The weighted nuclear estimate applies to every actual equal-rank subspace pair. -/
theorem quartic_weighted_transport_growth_of_principalAngles_le
    (a b bound : ℝ) (hb : 0 < b) (hab : b < a)
    (hbound : bound ∈ Set.Icc 0 (Real.pi / 2)) (hcut : b ≤ a * Real.cos bound)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (hmax : ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ bound) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      3 * b ^ 2 * (a - b) * UnitarilyInvariantSeminorm.frobenius ℂ E E
          (T.toLinearMap - R.toLinearMap) ^ 4 ≤
        32 * a ^ 2 * Module.finrank ℂ E *
          (UnitarilyInvariantSeminorm.nuclear ℂ E E
              ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) -
            UnitarilyInvariantSeminorm.nuclear ℂ E E
              ((a : ℂ) • R.toLinearMap - (b : ℂ) • LinearMap.id)) := by
  let D := finiteCrossedDefectEquiv U V hUV
  let Rop := nonacuteDirectRotation U V D
  let R := Unitary.linearIsometryEquiv
    (⟨Rop, nonacuteDirectRotation_mem_unitary U V D⟩ : unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0⟩ :=
    exists_subspace_paired_rotation_basis U V hUV
  have hle := paired_angles_le_of_principalAngles_le U V e theta hθ hC0 hC1 hCf hJ0
    bound hbound.1 hmax
  have hcos (i) : Real.cos bound ≤ Real.cos (theta i) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (hθ i).1.le
      (by linarith [hbound.2, Real.pi_pos]) (hle i)
  have hsub (i) : b ≤ a * Real.cos (theta i) :=
    hcut.trans (mul_le_mul_of_nonneg_left (hcos i) (hb.le.trans hab.le))
  let A := (a : ℂ) • R.toLinearMap
  have hA0 (i) : A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)) := by
    change (a : ℂ) • R (e (.inl (0, i))) = _
    have hr : R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i)) := hR0 i
    rw [hr, smul_smul, Complex.exp_ofReal_mul_I]
    congr 1
    push_cast
    ring
  have hA1 (i) : A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)) := by
    change (a : ℂ) • R (e (.inl (1, i))) = _
    have hr : R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i)) := hR1 i
    rw [hr, smul_smul, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    congr 1
    push_cast
    ring
  have hAf (j) : A (e (.inr j)) = (a : ℂ) • e (.inr j) := by
    change (a : ℂ) • R (e (.inr j)) = _
    rw [show R (e (.inr j)) = e (.inr j) from hRf j]
  have hRref (x : E) : R (U.reflection x) = V.reflection (R x) :=
    nonacuteDirectRotation_reflection_intertwines U V D x
  dsimp only
  intro T hT
  have hTref := (Submodule.map_eq_iff_intertwines_reflection U V T).mp hT
  let Z := R.trans T.symm
  have hcomm (x : E) : Z (U.reflection x) = U.reflection (Z x) := by
    apply T.injective
    change T (T.symm (R (U.reflection x))) = T (U.reflection (T.symm (R x)))
    rw [T.apply_symm_apply, hTref, T.apply_symm_apply, hRref]
  have hg := quartic_weightedNuclear_growth a b hb hab theta
    (fun i => ⟨(hθ i).1.le, (hθ i).2⟩) hsub e A hA0 hA1 hAf U.reflection hJ0 Z hcomm
  let N := UnitarilyInvariantSeminorm.nuclear ℂ E E
  let F := UnitarilyInvariantSeminorm.frobenius ℂ E E
  have hfactor : A - (b : ℂ) • Z.toLinearMap =
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) ∘ₗ Z.toLinearMap := by
    ext x
    simp [A, Z]
  have hN : N (A - (b : ℂ) • Z.toLinearMap) =
      N ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) := by
    rw [hfactor]
    exact N.map_comp_linearIsometryEquiv Z _
  have hFfactor : T.toLinearMap ∘ₗ (Z.toLinearMap - LinearMap.id) =
      R.toLinearMap - T.toLinearMap := by
    ext x
    simp [Z]
  have hF : F (Z.toLinearMap - LinearMap.id) = F (T.toLinearMap - R.toLinearMap) := by
    calc
      _ = F (T.toLinearMap ∘ₗ (Z.toLinearMap - LinearMap.id)) :=
        (F.map_linearIsometryEquiv_comp T _).symm
      _ = F (R.toLinearMap - T.toLinearMap) := congrArg F hFfactor
      _ = _ := by rw [← neg_sub, map_neg_eq_map]
  change 3 * b ^ 2 * (a - b) * F (Z.toLinearMap - LinearMap.id) ^ 4 ≤
    32 * a ^ 2 * Module.finrank ℂ E *
      (N (A - (b : ℂ) • Z.toLinearMap) - N (A - (b : ℂ) • LinearMap.id)) at hg
  rw [hF, hN] at hg
  exact hg

/-- The literal smoothed cost has quartic growth throughout the closed
canonical regime, including arbitrary mixtures of critical and smaller angles. -/
theorem smoothed_transport_quartic_growth_of_principalAngles_le
    (tau bound : ℝ) (hτ : 0 < tau)
    (hbound : bound ∈ Set.Icc 0 (Real.pi / 2))
    (hcut : ((smoothingRadius tau)⁻¹) ^ 2 ≤ Real.cos bound)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (hmax : ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ bound) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      3 * tau * UnitarilyInvariantSeminorm.frobenius ℂ E E
          (T.toLinearMap - R.toLinearMap) ^ 4 ≤
        32 * (smoothingRadius tau) ^ 4 * Module.finrank ℂ E *
          (smoothedDisplacementCost tau T.toLinearMap -
            smoothedDisplacementCost tau R.toLinearMap) := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau hτ
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hab : a⁻¹ < a := lt_trans ((inv_lt_one₀ ha0).mpr ha) ha
  have hsub : a⁻¹ ≤ a * Real.cos bound := by
    have h := mul_le_mul_of_nonneg_left hcut ha0.le
    change a * (a⁻¹) ^ 2 ≤ a * Real.cos bound at h
    rw [pow_two, ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul] at h
    exact h
  have hcost (T : E ≃ₗᵢ[ℂ] E) :
      smoothedDisplacementCost tau T.toLinearMap =
        UnitarilyInvariantSeminorm.nuclear ℂ E E
          ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
            Module.finrank ℂ E * tau :=
    smoothedDisplacementCost_eq_weightedNuclear tau hτ (Unitary.linearIsometryEquiv.symm T)
  dsimp only
  intro T hT
  have hg := quartic_weighted_transport_growth_of_principalAngles_le a a⁻¹ bound
    (inv_pos.mpr ha0) hab hbound hsub U V hUV hmax T hT
  rw [show a - a⁻¹ = tau from smoothingRadius_sub_inv tau hτ] at hg
  have hs := mul_le_mul_of_nonneg_left hg (sq_nonneg a)
  rw [hcost, hcost]
  convert hs using 1
  · field_simp
  · ring


/-- Quartic growth under the exact principal-angle cutoff. -/
theorem smoothed_transport_quartic_growth
    (tau : ℝ) (hτ : 0 < tau)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (hmax : ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ smoothedCriticalAngle tau) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      3 * tau * UnitarilyInvariantSeminorm.frobenius ℂ E E
          (T.toLinearMap - R.toLinearMap) ^ 4 ≤
        32 * (smoothingRadius tau) ^ 4 * Module.finrank ℂ E *
          (smoothedDisplacementCost tau T.toLinearMap -
            smoothedDisplacementCost tau R.toLinearMap) :=
  smoothed_transport_quartic_growth_of_principalAngles_le tau (smoothedCriticalAngle tau) hτ
    (smoothedCriticalAngle_mem_Icc tau) (by rw [cos_smoothedCriticalAngle tau hτ]) U V hUV hmax

omit [CompleteSpace E] in
private theorem linearMap_eq_zero_of_frobenius_eq_zero (A : E →ₗ[ℂ] E)
    (hA : UnitarilyInvariantSeminorm.frobenius ℂ E E A = 0) : A = 0 := by
  let e := stdOrthonormalBasis ℂ E
  have hsum : ∑ i : Fin (Module.finrank ℂ E), ‖A (e i)‖ ^ 2 = 0 := by
    rw [← UnitarilyInvariantSeminorm.sq_frobenius_apply e, hA]
    norm_num
  apply e.toBasis.ext
  intro i
  have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖A (e j)‖)
    (Finset.mem_univ i)
  rw [hsum] at hle
  have hi : ‖A (e i)‖ = 0 := by nlinarith [norm_nonneg (A (e i))]
  simpa using norm_eq_zero.mp hi

/-- A feasible unitary with cost no larger than the canonical rotation
must be that rotation throughout the closed canonical regime. -/
theorem smoothed_transport_eq_canonical_of_cost_le
    (tau : ℝ) (hτ : 0 < tau)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (hmax : ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ smoothedCriticalAngle tau) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau R.toLinearMap →
        T = R := by
  dsimp only
  intro T hT hcost
  have hg := smoothed_transport_quartic_growth tau hτ U V hUV hmax T hT
  let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
  let f := UnitarilyInvariantSeminorm.frobenius ℂ E E (T.toLinearMap - R.toLinearMap)
  have hnonpos : smoothedDisplacementCost tau T.toLinearMap -
      smoothedDisplacementCost tau R.toLinearMap ≤ 0 := sub_nonpos.mpr hcost
  have hrhs := mul_nonpos_of_nonneg_of_nonpos
    (by positivity : 0 ≤ 32 * (smoothingRadius tau) ^ 4 * (Module.finrank ℂ E : ℝ)) hnonpos
  have hprod : 3 * tau * f ^ 4 ≤ 0 := hg.trans hrhs
  have hf4 : f ^ 4 ≤ 0 := by
    by_contra h
    have hpos := mul_pos (by positivity : 0 < 3 * tau) (lt_of_not_ge h)
    exact not_lt_of_ge hprod hpos
  have hf : f = 0 := (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp
    (le_antisymm hf4 (by positivity))
  have hzero := linearMap_eq_zero_of_frobenius_eq_zero (T.toLinearMap - R.toLinearMap) hf
  have heq := sub_eq_zero.mp hzero
  ext x
  exact DFunLike.congr_fun heq x

/-- The objective gap controls the fourth power of the distance to the canonical rotation. -/
theorem smoothed_transport_quartic_error_bound
    (tau epsilon : ℝ) (hτ : 0 < tau)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (hmax : ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ smoothedCriticalAngle tau) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      smoothedDisplacementCost tau T.toLinearMap - smoothedDisplacementCost tau R.toLinearMap ≤ epsilon →
      UnitarilyInvariantSeminorm.frobenius ℂ E E (T.toLinearMap - R.toLinearMap) ^ 4 ≤
        (32 * (smoothingRadius tau) ^ 4 * Module.finrank ℂ E / (3 * tau)) * epsilon := by
  dsimp only
  intro T hT hgap
  have hg := smoothed_transport_quartic_growth tau hτ U V hUV hmax T hT
  have hscaled := mul_le_mul_of_nonneg_left hgap
    (by positivity : 0 ≤ 32 * (smoothingRadius tau) ^ 4 * (Module.finrank ℂ E : ℝ))
  have hprod := hg.trans hscaled
  rw [mul_comm (3 * tau)] at hprod
  have h := (le_div_iff₀ (by positivity : 0 < 3 * tau)).mpr hprod
  convert h using 1
  ring

/-- Feasibility, global minimality, and uniqueness hold through the critical angle. -/
theorem smoothed_canonical_unique_minimizer
    (tau : ℝ) (hτ : 0 < tau)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (hmax : ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ smoothedCriticalAngle tau) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    U.map R.toLinearMap = V ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
        smoothedDisplacementCost tau R.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap ∧
        (smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau R.toLinearMap → T = R) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · apply (U.map_eq_iff_intertwines_reflection V _).mpr
    exact nonacuteDirectRotation_reflection_intertwines U V (finiteCrossedDefectEquiv U V hUV)
  · intro T hT
    have huniq := smoothed_transport_eq_canonical_of_cost_le tau hτ U V hUV hmax T hT
    refine ⟨?_, huniq⟩
    by_contra h
    have heq := huniq (lt_of_not_ge h).le
    exact h (by rw [heq])

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
