/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Haagerup--Zsidó kernel: definitions and elementary API

This file defines the hyperbolic `weight`, the inner Laplace factor
`innerLaplace`, the real kernel `realKernel`, and the complex reciprocal kernel
`reciprocalKernel`, together with their elementary algebraic, positivity,
measurability, and parity API.

This is a topic split of `ForTauCeti/Analysis/Fourier/HaagerupZsidoKernel.lean`;
declarations are moved verbatim and remain in the `TauCeti.HaagerupZsido`
namespace.
-/

@[expose] public section

namespace TauCeti
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

theorem reciprocalKernel_neg (t : ℝ) :
    reciprocalKernel (-t) = -reciprocalKernel t := by
  simp only [reciprocalKernel_def, realKernel_neg, Complex.ofReal_neg]
  ring

theorem norm_reciprocalKernel (t : ℝ) : ‖reciprocalKernel t‖ = |realKernel t| := by
  simp [reciprocalKernel_def]

theorem abs_realKernel (t : ℝ) :
    |realKernel t| = |Real.sin t| / 2 * innerLaplace t := by
  rw [realKernel_def, abs_mul, abs_div, abs_two,
    abs_of_nonneg (innerLaplace_nonneg t)]

end

end HaagerupZsido
end TauCeti
