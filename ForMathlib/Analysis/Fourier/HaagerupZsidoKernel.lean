/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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

open MeasureTheory Set
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

end

end HaagerupZsido
end ForMathlib
