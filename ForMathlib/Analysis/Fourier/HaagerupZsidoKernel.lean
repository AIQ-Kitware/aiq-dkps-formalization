/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Haagerup--Zsidó reciprocal Fourier kernel

This file develops the scalar harmonic analysis underlying the sharp
arbitrary-spectrum Sylvester estimate.  It contains no Hilbert-space data.

The Fourier convention needed downstream is the unnormalized integral
`integral fun t => f t * exp (t * x * I)`.  Mathlib's normalized real Fourier
transform is used only for the Poisson-summation calculation.
-/

namespace ForMathlib
namespace HaagerupZsido

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- The positive hyperbolic weight in the limiting Haagerup--Zsidó kernel. -/
def weight (y : ℝ) : ℝ :=
  Real.tanh (Real.pi * y / 2)

theorem weight_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ weight y := by
  rw [weight, Real.tanh_eq]
  have hmono : Real.exp (- (Real.pi * y / 2)) ≤
      Real.exp (Real.pi * y / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  positivity

theorem weight_le_one (y : ℝ) : weight y ≤ 1 :=
  (Real.tanh_lt_one _).le

/-- A two-sided Laplace transform with an oscillatory factor.  This elementary
identity is used both for the Cauchy kernel in Poisson summation and for the
final Fourier transform computation. -/
theorem integral_cexp_neg_mul_abs_mul_cexp
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ,
        Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
      ((2 * y) / (y ^ 2 + x ^ 2) : ℝ) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
      Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))
  let aNeg : ℂ := (y : ℂ) + (x : ℂ) * Complex.I
  let aPos : ℂ := (-y : ℝ) + (x : ℂ) * Complex.I
  have haNeg : 0 < aNeg.re := by simp [aNeg, hy]
  have haPos : aPos.re < 0 := by simp [aPos, hy]
  have hfNeg : Set.EqOn f (fun t : ℝ => Complex.exp (aNeg * t)) (Set.Iic 0) := by
    intro t ht
    dsimp only [f]
    rw [abs_of_nonpos ht, ← Complex.exp_add]
    congr 1
    simp only [aNeg]
    push_cast
    ring
  have hfPos : Set.EqOn f (fun t : ℝ => Complex.exp (aPos * t)) (Set.Ioi 0) := by
    intro t ht
    dsimp only [f]
    rw [abs_of_pos ht, ← Complex.exp_add]
    congr 1
    simp only [aPos]
    push_cast
    ring
  have hintNeg : IntegrableOn f (Set.Iic 0) :=
    (integrableOn_exp_mul_complex_Iic haNeg 0).congr_fun hfNeg.symm measurableSet_Iic
  have hintPos : IntegrableOn f (Set.Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi haPos 0).congr_fun hfPos.symm measurableSet_Ioi
  change ∫ t, f t = _
  rw [← intervalIntegral.integral_Iic_add_Ioi hintNeg hintPos]
  calc
    (∫ t in Set.Iic 0, f t) + ∫ t in Set.Ioi 0, f t =
        (∫ (t : ℝ) in Set.Iic 0, Complex.exp (aNeg * (t : ℂ))) +
          ∫ (t : ℝ) in Set.Ioi 0, Complex.exp (aPos * (t : ℂ)) := by
      congr 1
      · exact setIntegral_congr_fun measurableSet_Iic hfNeg
      · exact setIntegral_congr_fun measurableSet_Ioi hfPos
    _ = (1 : ℂ) / aNeg - (1 : ℂ) / aPos := by
      rw [integral_exp_mul_complex_Iic haNeg,
        integral_exp_mul_complex_Ioi haPos]
      simp
      ring
    _ = ((2 * y) / (y ^ 2 + x ^ 2) : ℝ) := by
      have hden : y ^ 2 + x ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      apply Complex.ext
      · rw [Complex.sub_re, Complex.div_re, Complex.div_re, Complex.ofReal_re]
        simp only [aNeg, aPos, Complex.normSq_apply, Complex.one_re, Complex.one_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        field_simp [hden]
        ring
      · rw [Complex.sub_im, Complex.div_im, Complex.div_im, Complex.ofReal_im]
        simp only [aNeg, aPos, Complex.normSq_apply, Complex.one_re, Complex.one_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        field_simp [hden]
        ring

/-- Fourier transform of the two-sided exponential in Mathlib's normalization. -/
theorem fourier_cexp_neg_two_pi_mul_abs
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    𝓕 (fun t : ℝ =>
        Complex.exp ((-(2 * Real.pi * y * |t|) : ℝ) : ℂ)) x =
      ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hscale : 0 < 2 * Real.pi * y := by positivity
  calc
    (∫ t : ℝ,
        Complex.exp (↑(-2 * Real.pi * t * x) * Complex.I) •
          Complex.exp ((-(2 * Real.pi * y * |t|) : ℝ) : ℂ)) =
        ∫ t : ℝ,
          Complex.exp ((-((2 * Real.pi * y) * |t|) : ℝ) : ℂ) *
            Complex.exp ((((t * (-2 * Real.pi * x) : ℝ) : ℂ) * Complex.I)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hphase :
          Complex.exp (↑(-2 * Real.pi * t * x) * Complex.I) =
            Complex.exp ((((t * (-2 * Real.pi * x) : ℝ) : ℂ) * Complex.I)) := by
        congr 1
        push_cast
        ring
      simp only [smul_eq_mul, hphase]
      ring
    _ = (((2 * (2 * Real.pi * y)) /
          ((2 * Real.pi * y) ^ 2 + (-2 * Real.pi * x) ^ 2) : ℝ) : ℂ) :=
      integral_cexp_neg_mul_abs_mul_cexp (-2 * Real.pi * x) hscale
    _ = ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
      norm_cast
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hden : y ^ 2 + x ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      field_simp [hpi, hden]
      norm_num
      ring

/-- Two-sided exponentials decay faster than every real inverse power. -/
theorem cexp_neg_mul_abs_isLittleO_rpow_cocompact
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (fun x : ℝ => Complex.exp ((-(a * |x|) : ℝ) : ℂ))
      =o[cocompact ℝ] (fun x : ℝ => |x| ^ s) := by
  apply IsLittleO.of_norm_left
  simp only [Complex.norm_exp, Complex.ofReal_re]
  rw [cocompact_eq_atBot_atTop, isLittleO_sup]
  constructor
  · have h := (isLittleO_exp_neg_mul_rpow_atTop ha s).comp_tendsto
      tendsto_neg_atBot_atTop
    refine h.congr' ?_ ?_
    · filter_upwards [eventually_lt_atBot 0] with x hx
      simp [abs_of_neg hx]
    · filter_upwards [eventually_lt_atBot 0] with x hx
      simp [abs_of_neg hx]
  · refine (isLittleO_exp_neg_mul_rpow_atTop ha s).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp [abs_of_pos hx]
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp [abs_of_pos hx]

/-- The Cauchy function occurring as the transform has quadratic decay. -/
theorem cauchy_fourier_isBigO_rpow_neg_two
    {y : ℝ} (hy : 0 < y) :
    (fun x : ℝ => ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ))
      =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  refine IsBigO.of_bound (y / Real.pi) ?_
  filter_upwards [isCompact_Icc.compl_mem_cocompact] with x hx
  have hxabs : 1 ≤ |x| := by
    have hnle : ¬ |x| ≤ 1 := by
      simpa only [mem_compl_iff, mem_Icc, abs_le] using hx
    exact (lt_of_not_ge hnle).le
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hxabs
  have hsum_pos : 0 < y ^ 2 + x ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hx0, sq_nonneg y]
  have hquot_nonneg : 0 ≤ y / (Real.pi * (y ^ 2 + x ^ 2)) := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hquot_nonneg,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg (abs_nonneg x), Real.rpow_two, sq_abs]
  calc
    y / (Real.pi * (y ^ 2 + x ^ 2)) =
        (y / Real.pi) / (y ^ 2 + x ^ 2) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ (y / Real.pi) / x ^ 2 := by
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_ne_zero hx0)
        (by nlinarith [sq_nonneg y])
    _ = (y / Real.pi) * (x ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- The positive tail of the geometric exponential series. -/
theorem tsum_nat_exp_neg_mul_add_one {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ))) =
      Real.exp (-a) / (1 - Real.exp (-a)) := by
  let q := Real.exp (-a)
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact hqlt
  calc
    (∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ))) =
        ∑' n : ℕ, q ^ (n + 1) := by
      apply tsum_congr
      intro n
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ = ∑' n : ℕ, q ^ n * q := by simp_rw [pow_succ]
    _ = (∑' n : ℕ, q ^ n) * q := tsum_mul_right
    _ = (1 - q)⁻¹ * q := by rw [tsum_geometric_of_norm_lt_one hqnorm]
    _ = Real.exp (-a) / (1 - Real.exp (-a)) := by
      simp only [q, div_eq_mul_inv]
      ring

/-- The elementary two-sided geometric lattice sum. -/
theorem tsum_int_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.exp (-a * |(n : ℝ)|)) =
      (1 + Real.exp (-a)) / (1 - Real.exp (-a)) := by
  let f : ℤ → ℝ := fun n => Real.exp (-a * |(n : ℝ)|)
  let q := Real.exp (-a)
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact hqlt
  have hgeo : Summable (fun n : ℕ => q ^ n) :=
    (hasSum_geometric_of_norm_lt_one hqnorm).summable
  have hsum : Summable f := by
    apply Summable.of_nat_of_neg
    · refine hgeo.congr fun n => ?_
      change q ^ n = Real.exp (-a * |(((n : ℕ) : ℤ) : ℝ)|)
      rw [show |(((n : ℕ) : ℤ) : ℝ)| = (n : ℝ) by simp]
      simp only [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    · refine hgeo.congr fun n => ?_
      change q ^ n = Real.exp (-a * |((-(n : ℤ) : ℤ) : ℝ)|)
      rw [show |((-(n : ℤ) : ℤ) : ℝ)| = (n : ℝ) by simp]
      simp only [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
  have heven : Function.Even f := by
    intro n
    simp only [f, Int.cast_neg, abs_neg]
  have hpnat :
      (∑' n : ℕ+, f (n : ℤ)) =
        ∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ)) := by
    calc
      (∑' n : ℕ+, f (n : ℤ)) = ∑' n : ℕ, f (Nat.succPNat n : ℤ) :=
        (Equiv.pnatEquivNat.symm.tsum_eq (fun n : ℕ+ => f (n : ℤ))).symm
      _ = ∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ)) := by
        apply tsum_congr
        intro n
        dsimp only [f, Nat.succPNat]
        rw [abs_of_nonneg]
        · congr 1
        · positivity
  change ∑' n : ℤ, f n = _
  calc
    (∑' n : ℤ, f n) = f 0 + 2 • ∑' n : ℕ+, f (n : ℤ) :=
      tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum
    _ = 1 + 2 * (Real.exp (-a) / (1 - Real.exp (-a))) := by
      rw [hpnat, tsum_nat_exp_neg_mul_add_one ha]
      simp [f]
    _ = (1 + Real.exp (-a)) / (1 - Real.exp (-a)) := by
      have hne : 1 - Real.exp (-a) ≠ 0 := by
        have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
        linarith
      field_simp [hne]
      ring

/-- Poisson summation for the two-sided exponential, before evaluating its
geometric side. -/
theorem poisson_exponential_eq_cauchy_lattice
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ,
        Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
      ∑' n : ℤ,
        ((y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp ((-(2 * Real.pi * y * |t|) : ℝ) : ℂ)
  have hscale : 0 < 2 * Real.pi * y := by positivity
  have hfContinuous : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfDecay : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) :=
    (cexp_neg_mul_abs_isLittleO_rpow_cocompact hscale (-2)).isBigO
  have hFourier : 𝓕 f = fun x : ℝ =>
      ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
    funext x
    exact fourier_cexp_neg_two_pi_mul_abs x hy
  have hFourierDecay : (𝓕 f) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    rw [hFourier]
    exact cauchy_fourier_isBigO_rpow_neg_two hy
  have hPoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay
    hfContinuous (by norm_num : (1 : ℝ) < 2) hfDecay hFourierDecay 0
  simpa only [f, zero_add, hFourier, Int.cast_zero, QuotientAddGroup.mk_zero,
    fourier_eval_zero, mul_one] using hPoisson

/-- The Cauchy lattice sum, written in exponential rather than hyperbolic
notation. -/
theorem tsum_int_inv_sq_add_sq
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) =
      (Real.pi / y) *
        ((1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y)))) := by
  let q : ℝ := Real.exp (-(2 * Real.pi * y))
  let Q : ℝ := (1 + q) / (1 - q)
  have hscale : 0 < 2 * Real.pi * y := by positivity
  have hexpReal :
      (∑' n : ℤ, Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|)) = Q := by
    simpa only [Q, q, neg_mul] using tsum_int_exp_neg_mul_abs hscale
  have hexpComplex :
      (∑' n : ℤ,
          Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
        (Q : ℂ) := by
    calc
      (∑' n : ℤ,
          Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
          ∑' n : ℤ, (Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|) : ℂ) := by
        apply tsum_congr
        intro n
        rw [Complex.ofReal_exp]
        congr 1
        norm_cast
        ring
      _ = (((∑' n : ℤ,
          Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|)) : ℝ) : ℂ) :=
        (Complex.ofReal_tsum _).symm
      _ = (Q : ℂ) := by rw [hexpReal]
  have hPoisson := poisson_exponential_eq_cauchy_lattice hy
  have hscaled :
      (Q : ℂ) = ((y / Real.pi : ℝ) : ℂ) *
        ∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
    calc
      (Q : ℂ) = ∑' n : ℤ,
          ((y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
        rw [← hPoisson, hexpComplex]
      _ = ∑' n : ℤ, ((y / Real.pi : ℝ) : ℂ) *
          (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
        apply tsum_congr
        intro n
        norm_cast
        have hden : y ^ 2 + (n : ℝ) ^ 2 ≠ 0 := by
          nlinarith [sq_nonneg (n : ℝ)]
        field_simp [Real.pi_ne_zero, hden]
      _ = ((y / Real.pi : ℝ) : ℂ) *
          ∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := tsum_mul_left
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  calc
    (∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) =
        (((Real.pi / y : ℝ) : ℂ) * (((y / Real.pi : ℝ) : ℂ) *
          ∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ))) := by
      push_cast
      field_simp [Real.pi_ne_zero, hy.ne']
    _ = (((Real.pi / y : ℝ) : ℂ) * (Q : ℂ)) := by rw [← hscaled]
    _ = (((Real.pi / y) * Q : ℝ) : ℂ) := by push_cast; rfl
    _ = (((Real.pi / y) *
        ((1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y)))) : ℝ) : ℂ) := rfl

/-- The natural-number Cauchy series is summable, uniformly with respect to
the harmless nonnegative square added to its denominator. -/
theorem summable_nat_inv_sq_add_sq (y : ℝ) :
    Summable (fun n : ℕ => (y ^ 2 + (n : ℝ) ^ 2)⁻¹) := by
  have hmajor : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    have h := Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  have htail : Summable (fun n : ℕ =>
      (y ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    apply Summable.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      have hbase : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
      have hden : 0 < y ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      exact (inv_le_inv₀ hden hbase).2 (by nlinarith [sq_nonneg y])
    · exact hmajor
  apply (summable_nat_add_iff 1).mp
  exact htail

/-- The half-lattice version of the Cauchy sum. -/
theorem tsum_nat_inv_sq_add_sq
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) =
      (1 / 2) *
        ((Real.pi / y) *
          ((1 + Real.exp (-(2 * Real.pi * y))) /
            (1 - Real.exp (-(2 * Real.pi * y)))) + y⁻¹ ^ 2) := by
  let fNat : ℕ → ℝ := fun n => (y ^ 2 + (n : ℝ) ^ 2)⁻¹
  let fInt : ℤ → ℝ := fun n => (y ^ 2 + (n : ℝ) ^ 2)⁻¹
  have hNat : Summable fNat := summable_nat_inv_sq_add_sq y
  have hpos : Summable (fun n : ℕ => fInt (n + 1)) := by
    have := (summable_nat_add_iff 1).mpr hNat
    simpa only [fNat, fInt, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one] using this
  have hneg : Summable (fun n : ℕ => fInt (-(n + 1))) := by
    simpa only [fInt, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      neg_sq] using hpos
  have hIntSplit := tsum_of_add_one_of_neg_add_one hpos hneg
  have hNatSplit := hNat.tsum_eq_zero_add
  have hLattice := tsum_int_inv_sq_add_sq hy
  change ∑' n : ℕ, fNat n = _
  simp only [fInt, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Int.cast_zero, neg_sq] at hIntSplit
  simp only [fNat, Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hNatSplit
  have hzero : (y ^ 2 + (0 : ℝ) ^ 2)⁻¹ = y⁻¹ ^ 2 := by simp [inv_pow]
  rw [hzero] at hIntSplit hNatSplit
  nlinarith

/-- Exponential form of the hyperbolic weight. -/
theorem weight_eq_exp_quotient (y : ℝ) :
    weight y =
      (1 - Real.exp (-(Real.pi * y))) /
        (1 + Real.exp (-(Real.pi * y))) := by
  let z : ℝ := Real.pi * y / 2
  have htwo : Real.exp (-(Real.pi * y)) = Real.exp (-z) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [z]
    ring
  rw [weight, show Real.pi * y / 2 = z by rfl, Real.tanh_eq, htwo,
    Real.exp_neg z]
  have hne : Real.exp z ≠ 0 := Real.exp_ne_zero _
  field_simp [hne]

/-- The positive odd part of the Cauchy lattice. -/
theorem tsum_odd_inv_sq_add_sq
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, (y ^ 2 + (((2 * n + 1 : ℕ) : ℝ) ^ 2))⁻¹) =
      (Real.pi / (4 * y)) * weight y := by
  let f : ℕ → ℝ := fun n => (y ^ 2 + (n : ℝ) ^ 2)⁻¹
  have hAll : Summable f := summable_nat_inv_sq_add_sq y
  have hmul : Function.Injective (fun n : ℕ => 2 * n) :=
    mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
  have hEven := hAll.comp_injective hmul
  have hOdd := hAll.comp_injective ((add_left_injective 1).comp hmul)
  have hSplit := (hEven.hasSum.even_add_odd hOdd.hasSum).tsum_eq
  simp only [Function.comp_apply] at hSplit
  have hEvenScale :
      (∑' n : ℕ, f (2 * n)) =
        (1 / 4 : ℝ) * ∑' n : ℕ, ((y / 2) ^ 2 + (n : ℝ) ^ 2)⁻¹ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [f]
    have hdenLeft : y ^ 2 + ((2 * n : ℕ) : ℝ) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (((2 * n : ℕ) : ℝ))]
    have hdenRight : (y / 2) ^ 2 + (n : ℝ) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (n : ℝ)]
    field_simp [hdenLeft, hdenRight]
    norm_num
    ring
  have hOddEq :
      (∑' n : ℕ, f (2 * n + 1)) =
        (∑' n : ℕ, f n) - (1 / 4 : ℝ) *
          ∑' n : ℕ, ((y / 2) ^ 2 + (n : ℝ) ^ 2)⁻¹ := by
    rw [← hEvenScale]
    linarith [hSplit]
  have hAllValue := tsum_nat_inv_sq_add_sq hy
  have hHalfValue := tsum_nat_inv_sq_add_sq (show 0 < y / 2 by positivity)
  rw [hAllValue, hHalfValue] at hOddEq
  let r : ℝ := Real.exp (-(Real.pi * y))
  have hrpos : 0 < r := Real.exp_pos _
  have hrlt : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hFullExp : Real.exp (-(2 * Real.pi * y)) = r ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hHalfExp : Real.exp (-(2 * Real.pi * (y / 2))) = r := by
    dsimp only [r]
    congr 1
    ring
  have hInvHalf : (y / 2)⁻¹ ^ 2 = 4 * y⁻¹ ^ 2 := by
    field_simp [hy.ne']
    ring
  change (∑' n : ℕ, f (2 * n + 1)) = _
  calc
    (∑' n : ℕ, f (2 * n + 1)) =
        (1 / 2) *
            ((Real.pi / y) * ((1 + r ^ 2) / (1 - r ^ 2)) + y⁻¹ ^ 2) -
          (1 / 4) * ((1 / 2) *
            ((Real.pi / (y / 2)) * ((1 + r) / (1 - r)) +
              (y / 2)⁻¹ ^ 2)) := by
      simpa only [hFullExp, hHalfExp] using hOddEq
    _ = (Real.pi / (4 * y)) * weight y := by
      rw [weight_eq_exp_quotient, show Real.exp (-(Real.pi * y)) = r by rfl,
        hInvHalf]
      have hOneSub : 1 - r ≠ 0 := by linarith
      have hOneAdd : 1 + r ≠ 0 := by positivity
      have hSq : 1 - r ^ 2 ≠ 0 := by nlinarith
      field_simp [hy.ne', hOneSub, hOneAdd, hSq]
      ring

/-- Odd-pole partial-fraction expansion of the hyperbolic weight. -/
theorem weight_div_eq_tsum_odd
    {y : ℝ} (hy : 0 < y) :
    weight y / y =
      (4 / Real.pi) *
        ∑' n : ℕ, (y ^ 2 + (((2 * n + 1 : ℕ) : ℝ) ^ 2))⁻¹ := by
  rw [tsum_odd_inv_sq_add_sq hy]
  field_simp [Real.pi_ne_zero, hy.ne']

/-- Integrability of a rescaled Cauchy kernel. -/
theorem integrable_inv_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    Integrable (fun x : ℝ => (c ^ 2 + x ^ 2)⁻¹) := by
  have hcomp := integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hc)
  have hscaled := hcomp.const_mul (c⁻¹ ^ 2)
  apply hscaled.congr
  filter_upwards [] with x
  have hden : c ^ 2 + x ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hc, sq_nonneg x]
  have hbase : 1 + (c⁻¹ * x) ^ 2 ≠ 0 := by positivity
  field_simp [hc, hden, hbase]

/-- Integral of a Cauchy kernel over the positive half-line. -/
theorem integral_Ioi_inv_sq_add_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ in Set.Ioi 0, (c ^ 2 + x ^ 2)⁻¹) =
      Real.pi / (2 * c) := by
  have hchange := integral_comp_mul_left_Ioi
    (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 (inv_pos.mpr hc)
  have hleft :
      (∫ x : ℝ in Set.Ioi 0, (1 + (c⁻¹ * x) ^ 2)⁻¹) =
        c ^ 2 * ∫ x : ℝ in Set.Ioi 0, (c ^ 2 + x ^ 2)⁻¹ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    have hden : c ^ 2 + x ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_pos hc, sq_nonneg x]
    have hbase : 1 + (c⁻¹ * x) ^ 2 ≠ 0 := by positivity
    field_simp [hc.ne', hden, hbase]
  rw [hleft] at hchange
  simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero,
    sub_zero, inv_inv, smul_eq_mul] at hchange
  field_simp [hc.ne'] at hchange ⊢
  nlinarith

/-- The repeated-pole Cauchy integral needed when the two positive parameters
coincide. -/
theorem integral_Ioi_sq_div_sq_add_sq_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ in Set.Ioi 0, x ^ 2 / (c ^ 2 + x ^ 2) ^ 2) =
      Real.pi / (4 * c) := by
  let g : ℝ → ℝ := (id : ℝ → ℝ) / fun x => c ^ 2 + x ^ 2
  let g' : ℝ → ℝ := fun x =>
    (1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1))) /
      (c ^ 2 + x ^ 2) ^ 2
  have hderiv (x : ℝ) := by
    have hden : c ^ 2 + x ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_pos hc, sq_nonneg x]
    exact (hasDerivAt_id x).div ((hasDerivAt_pow 2 x).const_add (c ^ 2)) hden
  have hCauchy : Integrable (fun x : ℝ => (c ^ 2 + x ^ 2)⁻¹) :=
    integrable_inv_sq_add_sq hc.ne'
  have hDerivInt : Integrable g' := by
    apply hCauchy.mono'
    · dsimp only [g']
      have hnum : Continuous (fun x : ℝ =>
          1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1))) := by
        fun_prop
      have hden : Continuous (fun x : ℝ => (c ^ 2 + x ^ 2) ^ 2) := by
        fun_prop
      exact (hnum.div hden fun x => pow_ne_zero _ (by
        nlinarith [sq_pos_of_pos hc, sq_nonneg x])).aestronglyMeasurable
    · filter_upwards [] with x
      have hden : 0 < c ^ 2 + x ^ 2 := by
        nlinarith [sq_pos_of_pos hc, sq_nonneg x]
      have habs : |c ^ 2 - x ^ 2| ≤ c ^ 2 + x ^ 2 := by
        rw [abs_sub_le_iff]
        constructor <;> nlinarith [sq_nonneg c, sq_nonneg x]
      dsimp only [g']
      have hnum : 1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1)) =
          c ^ 2 - x ^ 2 := by norm_num; ring
      rw [hnum]
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hden]
      calc
        |c ^ 2 - x ^ 2| / (c ^ 2 + x ^ 2) ^ 2 ≤
            (c ^ 2 + x ^ 2) / (c ^ 2 + x ^ 2) ^ 2 :=
          div_le_div_of_nonneg_right habs (sq_nonneg _)
        _ = (c ^ 2 + x ^ 2)⁻¹ := by
          field_simp [hden.ne']
  have hgTop : Tendsto g atTop (nhds 0) := by
    have hInv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have hDen : Tendsto (fun x : ℝ => c ^ 2 * x⁻¹ ^ 2 + 1) atTop (nhds 1) := by
      simpa using ((hInv.pow 2).const_mul (c ^ 2)).add tendsto_const_nhds
    have hQuot := hInv.div hDen one_ne_zero
    norm_num only [zero_div] at hQuot
    apply hQuot.congr'
    filter_upwards [eventually_gt_atTop 0] with x hx
    dsimp only [g]
    have hx0 : x ≠ 0 := hx.ne'
    change x⁻¹ / (c ^ 2 * x⁻¹ ^ 2 + 1) = x / (c ^ 2 + x ^ 2)
    field_simp [hx0]
  have hDerivIntegral : (∫ x : ℝ in Set.Ioi 0, g' x) = 0 := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := 0) (m := 0) (fun x _ => hderiv x) hDerivInt.integrableOn hgTop
    simpa [g, g'] using h
  calc
    (∫ x : ℝ in Set.Ioi 0, x ^ 2 / (c ^ 2 + x ^ 2) ^ 2) =
        ∫ x : ℝ in Set.Ioi 0,
          (1 / 2 : ℝ) * (c ^ 2 + x ^ 2)⁻¹ - (1 / 2 : ℝ) * g' x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only [g']
      have hnum : 1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1)) =
          c ^ 2 - x ^ 2 := by norm_num; ring
      rw [hnum]
      have hden : c ^ 2 + x ^ 2 ≠ 0 := by
        nlinarith [sq_pos_of_pos hc, sq_nonneg x]
      field_simp [hden]
      ring
    _ = (1 / 2 : ℝ) * (∫ x : ℝ in Set.Ioi 0, (c ^ 2 + x ^ 2)⁻¹) -
        (1 / 2 : ℝ) * ∫ x : ℝ in Set.Ioi 0, g' x := by
      rw [integral_sub (hCauchy.const_mul _).integrableOn
        (hDerivInt.const_mul _).integrableOn, integral_const_mul, integral_const_mul]
    _ = Real.pi / (4 * c) := by
      rw [integral_Ioi_inv_sq_add_sq hc, hDerivIntegral]
      field_simp [hc.ne']
      ring

/-- The elementary two-Cauchy-denominator integral. -/
theorem integral_Ioi_sq_div_two_quadratics
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    (∫ y : ℝ in Set.Ioi 0,
        y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2))) =
      Real.pi / (2 * (a + c)) := by
  rcases ha.eq_or_lt with rfl | haPos
  · calc
      (∫ y : ℝ in Set.Ioi 0,
          y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + 0 ^ 2))) =
          ∫ y : ℝ in Set.Ioi 0, (c ^ 2 + y ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        have hy0 : y ≠ 0 := hy.ne'
        have hcden : c ^ 2 + y ^ 2 ≠ 0 := by
          nlinarith [sq_pos_of_pos hc, sq_nonneg y]
        field_simp [hy0, hcden]
        ring
      _ = Real.pi / (2 * c) := integral_Ioi_inv_sq_add_sq hc
      _ = Real.pi / (2 * (0 + c)) := by ring
  · by_cases hac : a = c
    · subst a
      calc
        (∫ y : ℝ in Set.Ioi 0,
            y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + c ^ 2))) =
            ∫ y : ℝ in Set.Ioi 0, y ^ 2 / (c ^ 2 + y ^ 2) ^ 2 := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _
          ring_nf
        _ = Real.pi / (4 * c) := integral_Ioi_sq_div_sq_add_sq_sq hc
        _ = Real.pi / (2 * (c + c)) := by ring
    · have hdiff : c ^ 2 - a ^ 2 ≠ 0 := by
        rw [sub_ne_zero]
        intro hsq
        rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
        · exact hac h.symm
        · nlinarith
      have hCInt : Integrable (fun y : ℝ => (c ^ 2 + y ^ 2)⁻¹) :=
        integrable_inv_sq_add_sq hc.ne'
      have hAInt : Integrable (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) :=
        integrable_inv_sq_add_sq haPos.ne'
      calc
        (∫ y : ℝ in Set.Ioi 0,
            y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2))) =
            ∫ y : ℝ in Set.Ioi 0,
              (c ^ 2 / (c ^ 2 - a ^ 2)) * (c ^ 2 + y ^ 2)⁻¹ -
                (a ^ 2 / (c ^ 2 - a ^ 2)) * (a ^ 2 + y ^ 2)⁻¹ := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _
          have hcden : c ^ 2 + y ^ 2 ≠ 0 := by
            nlinarith [sq_pos_of_pos hc, sq_nonneg y]
          have haden : a ^ 2 + y ^ 2 ≠ 0 := by
            nlinarith [sq_pos_of_pos haPos, sq_nonneg y]
          field_simp [hdiff, hcden, haden]
          ring
        _ = (c ^ 2 / (c ^ 2 - a ^ 2)) *
              (∫ y : ℝ in Set.Ioi 0, (c ^ 2 + y ^ 2)⁻¹) -
            (a ^ 2 / (c ^ 2 - a ^ 2)) *
              ∫ y : ℝ in Set.Ioi 0, (a ^ 2 + y ^ 2)⁻¹ := by
          rw [integral_sub (hCInt.const_mul _).integrableOn
            (hAInt.const_mul _).integrableOn, integral_const_mul, integral_const_mul]
        _ = (c ^ 2 / (c ^ 2 - a ^ 2)) * (Real.pi / (2 * c)) -
            (a ^ 2 / (c ^ 2 - a ^ 2)) * (Real.pi / (2 * a)) := by
          rw [integral_Ioi_inv_sq_add_sq hc, integral_Ioi_inv_sq_add_sq haPos]
        _ = Real.pi / (2 * (a + c)) := by
          have hsum : a + c ≠ 0 := by positivity
          field_simp [hdiff, hc.ne', haPos.ne', hsum]
          ring

/-- Integrability of the nonnegative rational kernel used in the telescoping
argument. -/
theorem integrable_sq_div_two_quadratics
    {a c : ℝ} (_ha : 0 ≤ a) (hc : 0 < c) :
    Integrable (fun y : ℝ =>
      y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2))) := by
  have hCauchy : Integrable (fun y : ℝ => (c ^ 2 + y ^ 2)⁻¹) :=
    integrable_inv_sq_add_sq hc.ne'
  apply hCauchy.mono'
  · exact (by fun_prop : Measurable (fun y : ℝ =>
      y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)))).aestronglyMeasurable
  · filter_upwards [] with y
    by_cases hy : y = 0
    · subst y
      simp
      positivity
    · have hySq : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      have hC : 0 < y ^ 2 + c ^ 2 := by positivity
      have hA : 0 < y ^ 2 + a ^ 2 := by positivity
      have hquot : 0 ≤ y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hquot]
      calc
        y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)) ≤
            (y ^ 2 + a ^ 2) / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)) :=
          div_le_div_of_nonneg_right (by nlinarith [sq_nonneg a]) (by positivity)
        _ = (c ^ 2 + y ^ 2)⁻¹ := by
          field_simp [hC.ne', hA.ne']
          ring

/-- The elementary reciprocal series telescopes by steps of two. -/
theorem hasSum_reciprocal_step_difference
    {a : ℝ} (ha : 0 ≤ a) :
    HasSum (fun n : ℕ =>
      (a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) (a + 1)⁻¹ := by
  let u : ℕ → ℝ := fun n => (a + 2 * n + 1)⁻¹
  have hnonneg : ∀ n : ℕ, 0 ≤ u n - u (n + 1) := by
    intro n
    dsimp only [u]
    have hleft : 0 < a + 2 * (n : ℝ) + 1 := by positivity
    have hright : 0 < a + 2 * ((n + 1 : ℕ) : ℝ) + 1 := by positivity
    apply sub_nonneg.mpr
    exact (inv_le_inv₀ hright hleft).2 (by push_cast; linarith)
  have hfinite : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (u n - u (n + 1))) = u 0 - u N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hDenTop : Tendsto (fun n : ℕ => a + 2 * (n : ℝ) + 1) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (a + 1)
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)) using 1
    funext n
    ring
  have huZero : Tendsto u atTop (nhds 0) := by
    exact hDenTop.inv_tendsto_atTop
  rw [show (fun n : ℕ =>
      (a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) =
      fun n : ℕ => u n - u (n + 1) by
    funext n
    dsimp only [u]
    push_cast
    congr 2
    ring]
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
  convert tendsto_const_nhds.sub huZero using 1
  · funext N
    exact hfinite N
  · dsimp only [u]
    norm_num

/-- Integrating the odd-pole expansion against a difference of two adjacent
resolvents produces the elementary step-two telescoping term. -/
theorem integral_weight_mul_reciprocal_difference
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ y : ℝ in Set.Ioi 0,
        weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)) =
      2 / (a + 1) := by
  let c : ℕ → ℝ := fun n => 2 * n + 1
  let F : ℕ → ℝ → ℝ := fun n y =>
    (4 / Real.pi) *
      (y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + a ^ 2)) -
        y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + (a + 2) ^ 2)))
  have hc (n : ℕ) : 0 < c n := by
    dsimp only [c]
    positivity
  have hFInt (n : ℕ) : IntegrableOn (F n) (Set.Ioi 0) := by
    have hA := integrable_sq_div_two_quadratics ha (hc n)
    have hB := integrable_sq_div_two_quadratics (by linarith : 0 ≤ a + 2) (hc n)
    exact ((hA.sub hB).const_mul (4 / Real.pi)).integrableOn
  have hFintegral (n : ℕ) :
      (∫ y : ℝ in Set.Ioi 0, F n y) =
        2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := by
    have hA := integrable_sq_div_two_quadratics ha (hc n)
    have hB := integrable_sq_div_two_quadratics (by linarith : 0 ≤ a + 2) (hc n)
    dsimp only [F]
    rw [integral_const_mul, integral_sub hA.integrableOn hB.integrableOn,
      integral_Ioi_sq_div_two_quadratics ha (hc n),
      integral_Ioi_sq_div_two_quadratics (by linarith : 0 ≤ a + 2) (hc n)]
    dsimp only [c]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hleft : a + (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have hright : a + 2 + (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have hstepLeft : a + 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have hstepRight : a + 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hpi, hleft, hright, hstepLeft, hstepRight]
    ring
  have hFnonneg (n : ℕ) {y : ℝ} (hy : y ∈ Set.Ioi (0 : ℝ)) : 0 ≤ F n y := by
    have hyPos : 0 < y := hy
    have hcommon : 0 < y ^ 2 + (c n) ^ 2 := by positivity
    have hA : 0 < y ^ 2 + a ^ 2 := by positivity
    have hAB : y ^ 2 + a ^ 2 ≤ y ^ 2 + (a + 2) ^ 2 := by
      nlinarith
    have hden :
        (y ^ 2 + (c n) ^ 2) * (y ^ 2 + a ^ 2) ≤
          (y ^ 2 + (c n) ^ 2) * (y ^ 2 + (a + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hAB hcommon.le
    have hquot :
        y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + (a + 2) ^ 2)) ≤
          y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + a ^ 2)) :=
      div_le_div_of_nonneg_left (sq_nonneg y) (mul_pos hcommon hA) hden
    dsimp only [F]
    positivity
  have hFnormIntegral (n : ℕ) :
      (∫ y : ℝ in Set.Ioi 0, ‖F n y‖) =
        2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := by
    calc
      (∫ y : ℝ in Set.Ioi 0, ‖F n y‖) =
          ∫ y : ℝ in Set.Ioi 0, F n y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        change ‖F n y‖ = F n y
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg n hy)]
      _ = 2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := hFintegral n
  have hNormSum : Summable (fun n : ℕ => ∫ y : ℝ in Set.Ioi 0, ‖F n y‖) := by
    apply ((hasSum_reciprocal_step_difference ha).summable.mul_left (2 : ℝ)).congr
    intro n
    exact (hFnormIntegral n).symm
  have hExchange :
      (∑' n : ℕ, ∫ y : ℝ in Set.Ioi 0, F n y) =
        ∫ y : ℝ in Set.Ioi 0, ∑' n : ℕ, F n y :=
    integral_tsum_of_summable_integral_norm hFInt hNormSum
  have hPointwise {y : ℝ} (hy : 0 < y) :
      (∑' n : ℕ, F n y) =
        weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹) := by
    have hw := weight_div_eq_tsum_odd hy
    let D : ℝ := y ^ 2 *
      ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)
    calc
      (∑' n : ℕ, F n y) =
          ∑' n : ℕ, (4 / Real.pi) *
            (y ^ 2 + (2 * n + 1) ^ 2)⁻¹ * D := by
        apply tsum_congr
        intro n
        dsimp only [F, c, D]
        have hC : y ^ 2 + (2 * (n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
        have hA : y ^ 2 + a ^ 2 ≠ 0 := by positivity
        have hB : y ^ 2 + (a + 2) ^ 2 ≠ 0 := by positivity
        field_simp [hC, hA, hB]
      _ = (4 / Real.pi) *
          ((∑' n : ℕ, (y ^ 2 + (2 * n + 1) ^ 2)⁻¹) * D) := by
        rw [← tsum_mul_right, ← tsum_mul_left]
        apply tsum_congr
        intro n
        ring
      _ = (weight y / y) * D := by
        have hw' : weight y / y =
            (4 / Real.pi) *
              ∑' n : ℕ, (y ^ 2 + (2 * (n : ℝ) + 1) ^ 2)⁻¹ := by
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hw
        rw [hw']
        ring
      _ = weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹) := by
        dsimp only [D]
        field_simp [hy.ne']
  calc
    (∫ y : ℝ in Set.Ioi 0,
        weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)) =
        ∫ y : ℝ in Set.Ioi 0, ∑' n : ℕ, F n y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact (hPointwise hy).symm
    _ = ∑' n : ℕ, ∫ y : ℝ in Set.Ioi 0, F n y := hExchange.symm
    _ = ∑' n : ℕ,
        2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := by
      apply tsum_congr
      exact hFintegral
    _ = 2 * (a + 1)⁻¹ := by
      rw [tsum_mul_left, (hasSum_reciprocal_step_difference ha).tsum_eq]
    _ = 2 / (a + 1) := by rw [div_eq_mul_inv]

/-- One-period Laplace--sine integral, from the elementary antiderivative
`-(exp (-y*t) * (y * sin t + cos t)) / (1 + y ^ 2)`. -/
theorem integral_zero_pi_sin_mul_exp_neg (y : ℝ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.sin t * Real.exp (-y * t)) =
      (1 + Real.exp (-Real.pi * y)) / (1 + y ^ 2) := by
  have hden : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
  let F : ℝ → ℝ := fun t =>
    -(Real.exp (-y * t) * (y * Real.sin t + Real.cos t)) / (1 + y ^ 2)
  have hFd (t : ℝ) : HasDerivAt F (Real.sin t * Real.exp (-y * t)) t := by
    have hlin : HasDerivAt (fun t : ℝ => -y * t) (-y) t := by
      simpa using (hasDerivAt_id t).const_mul (-y)
    have hexp := hlin.exp
    have htrig : HasDerivAt (fun t : ℝ => y * Real.sin t + Real.cos t)
        (y * Real.cos t + -Real.sin t) t :=
      ((Real.hasDerivAt_sin t).const_mul y).add (Real.hasDerivAt_cos t)
    have hprod := hexp.mul htrig
    have hval : Real.sin t * Real.exp (-y * t) =
        -(Real.exp (-y * t) * -y * (y * Real.sin t + Real.cos t) +
          Real.exp (-y * t) * (y * Real.cos t + -Real.sin t)) / (1 + y ^ 2) := by
      rw [eq_div_iff hden]
      ring
    rw [hval]
    exact (hprod.neg).div_const (1 + y ^ 2)
  have hint : IntervalIntegrable (fun t => Real.sin t * Real.exp (-y * t))
      MeasureTheory.volume 0 Real.pi :=
    (by fun_prop : Continuous fun t : ℝ =>
      Real.sin t * Real.exp (-y * t)).intervalIntegrable 0 Real.pi
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hFd t) hint]
  simp only [F, Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero,
    mul_zero, mul_one, zero_add, mul_neg]
  rw [show -y * Real.pi = -Real.pi * y by ring, Real.exp_zero]
  ring

/-- Shifting by an integer multiple of `π` preserves the absolute sine. -/
theorem abs_sin_add_nat_mul_pi (s : ℝ) (n : ℕ) :
    |Real.sin (s + n * Real.pi)| = |Real.sin s| := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : s + ((n + 1 : ℕ) : ℝ) * Real.pi =
          (s + (n : ℝ) * Real.pi) + Real.pi := by
        push_cast
        ring
      rw [hstep, Real.sin_add_pi, abs_neg, ih]

/-- Partial Laplace transform of the absolute sine over `N` periods.  Each
period contributes one geometric factor. -/
theorem integral_abs_sin_mul_exp_neg_upto (y : ℝ) (N : ℕ) :
    (∫ t in (0 : ℝ)..((N : ℝ) * Real.pi),
        |Real.sin t| * Real.exp (-y * t)) =
      (∑ n ∈ Finset.range N, Real.exp (-Real.pi * y) ^ n) *
        ((1 + Real.exp (-Real.pi * y)) / (1 + y ^ 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hcast : ((N + 1 : ℕ) : ℝ) * Real.pi =
          (N : ℝ) * Real.pi + Real.pi := by
        push_cast
        ring
      have hcont : Continuous fun t : ℝ => |Real.sin t| * Real.exp (-y * t) := by
        fun_prop
      have hi1 : IntervalIntegrable (fun t => |Real.sin t| * Real.exp (-y * t))
          MeasureTheory.volume 0 ((N : ℝ) * Real.pi) :=
        hcont.intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun t => |Real.sin t| * Real.exp (-y * t))
          MeasureTheory.volume ((N : ℝ) * Real.pi)
          ((N : ℝ) * Real.pi + Real.pi) :=
        hcont.intervalIntegrable _ _
      have hshift :
          (∫ t in ((N : ℝ) * Real.pi)..((N : ℝ) * Real.pi + Real.pi),
              |Real.sin t| * Real.exp (-y * t)) =
            Real.exp (-Real.pi * y) ^ N *
              ((1 + Real.exp (-Real.pi * y)) / (1 + y ^ 2)) := by
        have hcomp := intervalIntegral.integral_comp_add_right
          (a := 0) (b := Real.pi)
          (fun t => |Real.sin t| * Real.exp (-y * t)) ((N : ℝ) * Real.pi)
        rw [zero_add] at hcomp
        rw [show (N : ℝ) * Real.pi + Real.pi =
          Real.pi + (N : ℝ) * Real.pi by ring, ← hcomp]
        calc
          (∫ s in (0 : ℝ)..Real.pi,
              |Real.sin (s + (N : ℝ) * Real.pi)| *
                Real.exp (-y * (s + (N : ℝ) * Real.pi))) =
              ∫ s in (0 : ℝ)..Real.pi,
                Real.exp (-y * ((N : ℝ) * Real.pi)) *
                  (Real.sin s * Real.exp (-y * s)) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le Real.pi_nonneg] at hs
            dsimp only
            have hsin : |Real.sin (s + (N : ℝ) * Real.pi)| = Real.sin s := by
              rw [abs_sin_add_nat_mul_pi]
              exact abs_of_nonneg
                (Real.sin_nonneg_of_nonneg_of_le_pi hs.1 hs.2)
            rw [hsin, show -y * (s + (N : ℝ) * Real.pi) =
              -y * s + -y * ((N : ℝ) * Real.pi) by ring, Real.exp_add]
            ring
          _ = Real.exp (-y * ((N : ℝ) * Real.pi)) *
              ((1 + Real.exp (-Real.pi * y)) / (1 + y ^ 2)) := by
            rw [intervalIntegral.integral_const_mul,
              integral_zero_pi_sin_mul_exp_neg]
          _ = Real.exp (-Real.pi * y) ^ N *
              ((1 + Real.exp (-Real.pi * y)) / (1 + y ^ 2)) := by
            congr 1
            rw [← Real.exp_nat_mul]
            congr 1
            ring
      rw [hcast, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
        ih, hshift, Finset.sum_range_succ]
      ring

/-- Integrability of the absolute sine against an exponential weight. -/
theorem integrableOn_abs_sin_mul_exp_neg {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => |Real.sin t| * Real.exp (-y * t))
      (Set.Ioi 0) := by
  apply (exp_neg_integrableOn_Ioi 0 hy).mono'
  · exact (by fun_prop : Measurable fun t : ℝ =>
      |Real.sin t| * Real.exp (-y * t)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
    have hsin : |Real.sin t| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
    calc
      |Real.sin t| * Real.exp (-y * t) ≤ 1 * Real.exp (-y * t) :=
        mul_le_mul_of_nonneg_right hsin (Real.exp_pos _).le
      _ = Real.exp (-y * t) := one_mul _

/-- The Laplace transform of the absolute sine, by periodic decomposition and
the geometric series. -/
theorem integral_Ioi_abs_sin_mul_exp_neg {y : ℝ} (hy : 0 < y) :
    (∫ t in Set.Ioi (0 : ℝ), |Real.sin t| * Real.exp (-y * t)) =
      (1 + Real.exp (-Real.pi * y)) /
        ((1 - Real.exp (-Real.pi * y)) * (1 + y ^ 2)) := by
  let q : ℝ := Real.exp (-Real.pi * y)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hqne : 1 - q ≠ 0 := by linarith
  have hden : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
  have hb : Filter.Tendsto (fun N : ℕ => (N : ℝ) * Real.pi)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const Real.pi_pos
  have hlim1 := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_abs_sin_mul_exp_neg hy) hb
  have hgeo : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, q ^ n)
      Filter.atTop (nhds (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat
  have hlim2 : Filter.Tendsto
      (fun N : ℕ => ∫ t in (0 : ℝ)..((N : ℝ) * Real.pi),
        |Real.sin t| * Real.exp (-y * t))
      Filter.atTop (nhds ((1 - q)⁻¹ * ((1 + q) / (1 + y ^ 2)))) := by
    apply (hgeo.mul_const ((1 + q) / (1 + y ^ 2))).congr
    intro N
    exact (integral_abs_sin_mul_exp_neg_upto y N).symm
  rw [tendsto_nhds_unique hlim1 hlim2]
  change (1 - q)⁻¹ * ((1 + q) / (1 + y ^ 2)) = (1 + q) / ((1 - q) * (1 + y ^ 2))
  field_simp

/-! ### The explicit Haagerup--Zsidó kernel

The kernel is the sine multiple of the Laplace transform of the hyperbolic
weight.  Its value at zero already vanishes through the sine factor, so no
separate zero branch is required; the natural one-sided limits at zero are
irrelevant for every integral computed below. -/

/-- The inner Laplace factor of the limiting Haagerup--Zsidó kernel. -/
def innerLaplace (t : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), weight y * Real.exp (-|t| * y)

theorem innerLaplace_def (t : ℝ) :
    innerLaplace t = ∫ y in Set.Ioi (0 : ℝ), weight y * Real.exp (-|t| * y) :=
  rfl

/-- The real Haagerup--Zsidó kernel at the sharp parameter. -/
def realKernel (t : ℝ) : ℝ :=
  (Real.sin t / 2) * innerLaplace t

theorem realKernel_def (t : ℝ) :
    realKernel t = (Real.sin t / 2) * innerLaplace t :=
  rfl

/-- The complex reciprocal kernel `-i f₀`. -/
def reciprocalKernel (t : ℝ) : ℂ :=
  -Complex.I * (realKernel t : ℂ)

theorem reciprocalKernel_def (t : ℝ) :
    reciprocalKernel t = -Complex.I * (realKernel t : ℂ) :=
  rfl

theorem continuous_weight : Continuous weight := by
  have h : weight = fun y =>
      (1 - Real.exp (-(Real.pi * y))) / (1 + Real.exp (-(Real.pi * y))) := by
    funext y
    exact weight_eq_exp_quotient y
  rw [h]
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro y
  positivity

theorem innerLaplace_nonneg (t : ℝ) : 0 ≤ innerLaplace t :=
  setIntegral_nonneg measurableSet_Ioi fun _y hy =>
    mul_nonneg (weight_nonneg (le_of_lt hy)) (Real.exp_pos _).le

theorem innerLaplace_neg (t : ℝ) : innerLaplace (-t) = innerLaplace t := by
  simp only [innerLaplace_def, abs_neg]

theorem measurable_innerLaplace : Measurable innerLaplace := by
  have hcont : Continuous fun p : ℝ × ℝ =>
      weight p.2 * Real.exp (-|p.1| * p.2) :=
    (continuous_weight.comp continuous_snd).mul
      (Real.continuous_exp.comp ((continuous_fst.abs.neg).mul continuous_snd))
  exact hcont.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_realKernel : Measurable realKernel :=
  (Real.measurable_sin.div_const 2).mul measurable_innerLaplace

theorem measurable_reciprocalKernel : Measurable reciprocalKernel :=
  (Complex.measurable_ofReal.comp measurable_realKernel).const_mul (-Complex.I)

theorem realKernel_neg (t : ℝ) : realKernel (-t) = -realKernel t := by
  simp only [realKernel_def, Real.sin_neg, innerLaplace_neg]
  ring

theorem norm_reciprocalKernel (t : ℝ) : ‖reciprocalKernel t‖ = |realKernel t| := by
  simp [reciprocalKernel_def]

theorem abs_realKernel (t : ℝ) :
    |realKernel t| = |Real.sin t| / 2 * innerLaplace t := by
  rw [realKernel_def, abs_mul, abs_div, abs_two,
    abs_of_nonneg (innerLaplace_nonneg t)]

/-! ### Exact `L¹` mass -/

/-- The absolute sine is invariant under absolute value of the argument. -/
theorem abs_sin_abs (t : ℝ) : |Real.sin (|t|)| = |Real.sin t| := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, Real.sin_neg, abs_neg]

/-- Integrability of an even function from its positive half-line
restriction. -/
theorem integrable_of_even_integrableOn_Ioi
    {g : ℝ → ℝ} (heven : ∀ t, g (-t) = g t)
    (hg : IntegrableOn g (Set.Ioi 0)) : Integrable g := by
  have hIic : IntegrableOn g (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    have m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, heven, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)) hg
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hg

/-- Two-sided integrability of the absolute sine against a symmetric
exponential. -/
theorem integrable_abs_sin_mul_exp_neg_abs {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ => |Real.sin t| * Real.exp (-y * |t|)) := by
  apply integrable_of_even_integrableOn_Ioi
  · intro t
    simp [Real.sin_neg]
  · apply (integrableOn_abs_sin_mul_exp_neg hy).congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [abs_of_pos (show (0 : ℝ) < t from ht)]

/-- The two-sided Laplace transform of the absolute sine. -/
theorem integral_abs_sin_mul_exp_neg_abs {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, |Real.sin t| * Real.exp (-y * |t|)) =
      2 * ((1 + Real.exp (-Real.pi * y)) /
        ((1 - Real.exp (-Real.pi * y)) * (1 + y ^ 2))) := by
  have h := integral_comp_abs
    (f := fun s : ℝ => |Real.sin s| * Real.exp (-y * s))
  calc
    (∫ t : ℝ, |Real.sin t| * Real.exp (-y * |t|)) =
        ∫ t : ℝ, |Real.sin (|t|)| * Real.exp (-y * |t|) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [abs_sin_abs]
    _ = 2 * ∫ t in Set.Ioi (0 : ℝ), |Real.sin t| * Real.exp (-y * t) := h
    _ = 2 * ((1 + Real.exp (-Real.pi * y)) /
        ((1 - Real.exp (-Real.pi * y)) * (1 + y ^ 2))) := by
      rw [integral_Ioi_abs_sin_mul_exp_neg hy]

/-- The hyperbolic weight cancels the geometric quotient of the absolute-sine
Laplace transform. -/
theorem weight_mul_expRatio {y : ℝ} (hy : 0 < y) :
    weight y * ((1 + Real.exp (-Real.pi * y)) /
      (1 - Real.exp (-Real.pi * y))) = 1 := by
  have hq1 : Real.exp (-(Real.pi * y)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hne : 1 - Real.exp (-(Real.pi * y)) ≠ 0 := by linarith
  have hpos : (0 : ℝ) < 1 + Real.exp (-(Real.pi * y)) := by positivity
  rw [weight_eq_exp_quotient, show -Real.pi * y = -(Real.pi * y) by ring]
  field_simp

/-- The kernel double integrand is integrable on the product of the positive
weight half-line with the full time line.  This single certificate powers
both the exact mass identity and the later Fourier exchange. -/
theorem integrable_kernel_prod :
    Integrable (Function.uncurry fun y t =>
      weight y * (|Real.sin t| * Real.exp (-y * |t|)))
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hcont : Continuous (Function.uncurry fun y t =>
      weight y * (|Real.sin t| * Real.exp (-y * |t|))) :=
    (continuous_weight.comp continuous_fst).mul
      (((Real.continuous_sin.comp continuous_snd).abs).mul
        (Real.continuous_exp.comp (continuous_fst.neg.mul continuous_snd.abs)))
  rw [integrable_prod_iff hcont.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (integrable_abs_sin_mul_exp_neg_abs hy).const_mul (weight y)
  · have hint : Integrable (fun y : ℝ => 2 * (1 + y ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul 2
    apply hint.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    have hq1 : Real.exp (-Real.pi * y) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    have hne : 1 - Real.exp (-Real.pi * y) ≠ 0 := by linarith
    have hy2 : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
    calc
      2 * (1 + y ^ 2)⁻¹ =
          (weight y * ((1 + Real.exp (-Real.pi * y)) /
            (1 - Real.exp (-Real.pi * y)))) * (2 * (1 + y ^ 2)⁻¹) := by
        rw [weight_mul_expRatio hy0, one_mul]
      _ = weight y * (2 * ((1 + Real.exp (-Real.pi * y)) /
            ((1 - Real.exp (-Real.pi * y)) * (1 + y ^ 2)))) := by
        field_simp
      _ = ∫ t : ℝ, ‖weight y * (|Real.sin t| * Real.exp (-y * |t|))‖ := by
        rw [← integral_abs_sin_mul_exp_neg_abs hy0, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (weight_nonneg hy0.le)
            (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))]

/-- The full-line sine-weighted Laplace mass. -/
theorem integral_abs_sin_mul_innerLaplace :
    (∫ t : ℝ, |Real.sin t| * innerLaplace t) = Real.pi := by
  have hswap := integral_integral_swap integrable_kernel_prod
  have hleft :
      (∫ y in Set.Ioi (0 : ℝ),
        ∫ t : ℝ, weight y * (|Real.sin t| * Real.exp (-y * |t|))) =
        Real.pi := by
    calc
      (∫ y in Set.Ioi (0 : ℝ),
          ∫ t : ℝ, weight y * (|Real.sin t| * Real.exp (-y * |t|))) =
          ∫ y in Set.Ioi (0 : ℝ), 2 * (1 + y ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        have hy0 : (0 : ℝ) < y := hy
        have hq1 : Real.exp (-Real.pi * y) < 1 :=
          Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
        have hne : 1 - Real.exp (-Real.pi * y) ≠ 0 := by linarith
        have hy2 : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
        dsimp only
        calc
          (∫ t : ℝ, weight y * (|Real.sin t| * Real.exp (-y * |t|))) =
              weight y * ∫ t : ℝ, |Real.sin t| * Real.exp (-y * |t|) :=
            integral_const_mul _ _
          _ = (weight y * ((1 + Real.exp (-Real.pi * y)) /
                (1 - Real.exp (-Real.pi * y)))) * (2 * (1 + y ^ 2)⁻¹) := by
            rw [integral_abs_sin_mul_exp_neg_abs hy0]
            field_simp
          _ = 2 * (1 + y ^ 2)⁻¹ := by
            rw [weight_mul_expRatio hy0, one_mul]
      _ = 2 * ∫ y in Set.Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ := by
        rw [integral_const_mul]
      _ = Real.pi := by
        rw [integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
        ring
  have hright :
      (∫ t : ℝ,
        ∫ y in Set.Ioi (0 : ℝ), weight y * (|Real.sin t| * Real.exp (-y * |t|))) =
        ∫ t : ℝ, |Real.sin t| * innerLaplace t := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [innerLaplace_def, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    dsimp only
    rw [show -|t| * y = -y * |t| by ring]
    ring
  rw [← hright, ← hswap, hleft]

/-- Integrability of the even envelope of the kernel. -/
theorem integrable_abs_sin_mul_innerLaplace :
    Integrable (fun t : ℝ => |Real.sin t| * innerLaplace t) := by
  have hswap := integrable_kernel_prod.swap
  have h2 := ((integrable_prod_iff hswap.aestronglyMeasurable).mp hswap).2
  apply h2.congr
  filter_upwards [] with t
  calc
    (∫ y in Set.Ioi (0 : ℝ),
        ‖(Function.uncurry fun y t =>
          weight y * (|Real.sin t| * Real.exp (-y * |t|))) ((t, y).swap)‖) =
        ∫ y in Set.Ioi (0 : ℝ), |Real.sin t| * (weight y * Real.exp (-|t| * y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      simp only [Prod.swap_prod_mk, Function.uncurry_apply_pair]
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (weight_nonneg hy0.le)
          (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)),
        show -|t| * y = -y * |t| by ring]
      ring
    _ = |Real.sin t| * innerLaplace t := by
      rw [integral_const_mul, innerLaplace_def]

/-- The real kernel is integrable. -/
theorem integrable_realKernel : Integrable realKernel := by
  apply integrable_abs_sin_mul_innerLaplace.mono'
    measurable_realKernel.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_realKernel]
  have h1 := innerLaplace_nonneg t
  have h2 := abs_nonneg (Real.sin t)
  nlinarith

/-- The reciprocal kernel is integrable. -/
theorem integrable_reciprocalKernel : Integrable reciprocalKernel :=
  integrable_realKernel.ofReal.const_mul (-Complex.I)

/-- The exact `L¹` mass of the real kernel. -/
theorem integral_abs_realKernel : (∫ t : ℝ, |realKernel t|) = Real.pi / 2 := by
  calc
    (∫ t : ℝ, |realKernel t|) =
        ∫ t : ℝ, (1 / 2 : ℝ) * (|Real.sin t| * innerLaplace t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [abs_realKernel]
      ring
    _ = (1 / 2 : ℝ) * ∫ t : ℝ, |Real.sin t| * innerLaplace t :=
      integral_const_mul _ _
    _ = Real.pi / 2 := by
      rw [integral_abs_sin_mul_innerLaplace]
      ring

/-- **Exact mass.**  The reciprocal kernel has `L¹` norm exactly `π / 2`. -/
theorem integral_norm_reciprocalKernel :
    (∫ t : ℝ, ‖reciprocalKernel t‖) = Real.pi / 2 := by
  calc
    (∫ t : ℝ, ‖reciprocalKernel t‖) = ∫ t : ℝ, |realKernel t| := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [norm_reciprocalKernel]
    _ = Real.pi / 2 := integral_abs_realKernel

/-! ### The oscillatory sine transform -/

/-- Two-sided integrability of a symmetric exponential. -/
theorem integrable_exp_neg_mul_abs {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ => Real.exp (-y * |t|)) := by
  apply integrable_of_even_integrableOn_Ioi
  · intro t
    rw [abs_neg]
  · apply (exp_neg_integrableOn_Ioi 0 hy).congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [abs_of_pos (show (0 : ℝ) < t from ht)]

/-- Integrability of the modulated two-sided exponential. -/
theorem integrable_cexp_neg_mul_abs_mul_cexp (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ =>
      Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) := by
  apply (integrable_exp_neg_mul_abs hy).mono'
  · exact (by fun_prop : Measurable fun t : ℝ =>
      Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_exp,
      Complex.ofReal_re, neg_mul]

/-- The oscillatory sine transform against a symmetric exponential, from the
two-sided Laplace transform at the shifted frequencies `x ± 1`. -/
theorem integral_sin_mul_cexp_neg_mul_abs_mul_cexp
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ,
        ((Real.sin t : ℝ) : ℂ) * Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
      Complex.I *
        (((y / (y ^ 2 + (x - 1) ^ 2) : ℝ) : ℂ) -
          ((y / (y ^ 2 + (x + 1) ^ 2) : ℝ) : ℂ)) := by
  have hplus := integral_cexp_neg_mul_abs_mul_cexp (x + 1) hy
  have hminus := integral_cexp_neg_mul_abs_mul_cexp (x - 1) hy
  have hintp := integrable_cexp_neg_mul_abs_mul_cexp (x + 1) hy
  have hintm := integrable_cexp_neg_mul_abs_mul_cexp (x - 1) hy
  have hexpsin (t : ℝ) :
      Complex.exp ((t : ℂ) * Complex.I) -
        Complex.exp (-(t : ℂ) * Complex.I) =
      2 * Complex.sin t * Complex.I := by
    rw [Complex.exp_mul_I,
      show -(t : ℂ) * Complex.I = (-(t : ℂ)) * Complex.I by ring,
      Complex.exp_mul_I, Complex.sin_neg, Complex.cos_neg]
    ring
  have hsin (t : ℝ) : ((Real.sin t : ℝ) : ℂ) =
      (Complex.exp ((t : ℂ) * Complex.I) -
        Complex.exp (-(t : ℂ) * Complex.I)) / (2 * Complex.I) := by
    rw [Complex.ofReal_sin, hexpsin,
      eq_div_iff (by simp [Complex.I_ne_zero] : (2 : ℂ) * Complex.I ≠ 0)]
    ring
  have hphase1 (t : ℝ) : Complex.exp ((t : ℂ) * Complex.I) *
      Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) =
      Complex.exp ((((t * (x + 1) : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase2 (t : ℝ) : Complex.exp (-(t : ℂ) * Complex.I) *
      Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) =
      Complex.exp ((((t * (x - 1) : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpoint (t : ℝ) :
      ((Real.sin t : ℝ) : ℂ) * Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) =
        (1 / (2 * Complex.I)) *
          (Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
              Complex.exp ((((t * (x + 1) : ℝ) : ℂ) * Complex.I)) -
            Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
              Complex.exp ((((t * (x - 1) : ℝ) : ℂ) * Complex.I))) := by
    rw [← hphase1, ← hphase2, hsin]
    ring
  have hd1 : (y ^ 2 + (x - 1) ^ 2 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg y, hy]
  have hd2 : (y ^ 2 + (x + 1) ^ 2 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg y, hy]
  have hc1 : ((y : ℂ) ^ 2 + ((x : ℂ) - 1) ^ 2) ≠ 0 := fun h =>
    hd1 (Complex.ofReal_eq_zero.mp (by push_cast; exact h))
  have hc2 : ((y : ℂ) ^ 2 + ((x : ℂ) + 1) ^ 2) ≠ 0 := fun h =>
    hd2 (Complex.ofReal_eq_zero.mp (by push_cast; exact h))
  calc
    (∫ t : ℝ,
        ((Real.sin t : ℝ) : ℂ) * Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
        ∫ t : ℝ, (1 / (2 * Complex.I)) *
          (Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
              Complex.exp ((((t * (x + 1) : ℝ) : ℂ) * Complex.I)) -
            Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
              Complex.exp ((((t * (x - 1) : ℝ) : ℂ) * Complex.I))) := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact hpoint t
    _ = (1 / (2 * Complex.I)) *
        (((2 * (y : ℝ) / ((y : ℝ) ^ 2 + (x + 1) ^ 2) : ℝ) : ℂ) -
          ((2 * (y : ℝ) / ((y : ℝ) ^ 2 + (x - 1) ^ 2) : ℝ) : ℂ)) := by
      rw [integral_const_mul, integral_sub hintp hintm, hplus, hminus]
    _ = Complex.I *
        (((y / (y ^ 2 + (x - 1) ^ 2) : ℝ) : ℂ) -
          ((y / (y ^ 2 + (x + 1) ^ 2) : ℝ) : ℂ)) := by
      push_cast
      field_simp
      rw [Complex.I_sq]
      ring

end

end HaagerupZsido
end ForMathlib
