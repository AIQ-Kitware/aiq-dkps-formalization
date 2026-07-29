/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Haagerup--Zsidó kernel: definitions and elementary API

This file defines the hyperbolic `weight`, its Laplace transform
`weightLaplaceTransform`, the real kernel `realKernel`, and the complex reciprocal kernel
`reciprocalKernel`, together with their elementary algebraic, positivity,
measurability, and parity API.

This is a topic split of `ForTauCeti/Analysis/Fourier/HaagerupZsidoKernel.lean`;
declarations are moved verbatim and remain in the `TauCeti.HaagerupZsido`
namespace.
-/

@[expose] public section

namespace TauCeti
namespace HaagerupZsido

open MeasureTheory Set

noncomputable section

/-- The positive hyperbolic weight in the limiting Haagerup--Zsidó kernel. -/
def weight (y : ℝ) : ℝ :=
  Real.tanh (Real.pi * y / 2)

/-- Unfolding lemma for `weight`, for rewriting rather than `show`. -/
theorem weight_def (y : ℝ) : weight y = Real.tanh (Real.pi * y / 2) :=
  rfl

/-- The weight is nonnegative on `[0, ∞)`, where the kernel integral runs.
`tanh` is odd, so this genuinely needs `0 ≤ y` rather than holding outright. -/
theorem weight_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ weight y := by
  rw [weight, Real.tanh_eq]
  have hmono : Real.exp (- (Real.pi * y / 2)) ≤
      Real.exp (Real.pi * y / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  positivity

private theorem weight_le_one (y : ℝ) : weight y ≤ 1 :=
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
irrelevant for every integral computed below.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti` at Davis--Kahan
  commit `f35ffc0`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

/-- The Laplace transform of the hyperbolic weight at `|t|`, the inner factor of
the limiting Haagerup--Zsidó kernel. -/
def weightLaplaceTransform (t : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), weight y * Real.exp (-|t| * y)

/-- Unfolding lemma for `weightLaplaceTransform`. -/
theorem weightLaplaceTransform_def (t : ℝ) :
    weightLaplaceTransform t = ∫ y in Set.Ioi (0 : ℝ), weight y * Real.exp (-|t| * y) :=
  rfl

/-- The real Haagerup--Zsidó kernel at the sharp parameter. -/
def realKernel (t : ℝ) : ℝ :=
  (Real.sin t / 2) * weightLaplaceTransform t

/-- Unfolding lemma for `realKernel`. -/
theorem realKernel_def (t : ℝ) :
    realKernel t = (Real.sin t / 2) * weightLaplaceTransform t :=
  rfl

/-- The complex reciprocal kernel `-i f₀`. -/
def reciprocalKernel (t : ℝ) : ℂ :=
  -Complex.I * (realKernel t : ℂ)

/-- Unfolding lemma for `reciprocalKernel`. -/
theorem reciprocalKernel_def (t : ℝ) :
    reciprocalKernel t = -Complex.I * (realKernel t : ℂ) :=
  rfl

/-- The weight is continuous.  Proved through the exponential-quotient form
rather than from `Real.tanh` directly, because that form makes the positivity of
the denominator visible to `positivity`. -/
theorem continuous_weight : Continuous weight := by
  have h : weight = fun y =>
      (1 - Real.exp (-(Real.pi * y))) / (1 + Real.exp (-(Real.pi * y))) := by
    funext y
    exact weight_eq_exp_quotient y
  rw [h]
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro y
  positivity

/-- The Laplace transform is nonnegative: the integrand is a product of two
nonnegative factors on `Ioi 0`. -/
theorem weightLaplaceTransform_nonneg (t : ℝ) : 0 ≤ weightLaplaceTransform t :=
  setIntegral_nonneg measurableSet_Ioi fun _y hy =>
    mul_nonneg (weight_nonneg (le_of_lt hy)) (Real.exp_pos _).le

private theorem weightLaplaceTransform_neg (t : ℝ) :
    weightLaplaceTransform (-t) = weightLaplaceTransform t := by
  simp only [weightLaplaceTransform_def, abs_neg]

private theorem measurable_weightLaplaceTransform : Measurable weightLaplaceTransform := by
  have hcont : Continuous fun p : ℝ × ℝ =>
      weight p.2 * Real.exp (-|p.1| * p.2) :=
    (continuous_weight.comp continuous_snd).mul
      (Real.continuous_exp.comp ((continuous_fst.abs.neg).mul continuous_snd))
  exact hcont.stronglyMeasurable.integral_prod_right'.measurable

/-- Measurability of the real kernel, needed before it can be integrated
against an operator-valued family. -/
theorem measurable_realKernel : Measurable realKernel :=
  (Real.measurable_sin.div_const 2).mul measurable_weightLaplaceTransform

/-- Measurability of the complex reciprocal kernel. -/
theorem measurable_reciprocalKernel : Measurable reciprocalKernel :=
  (Complex.measurable_ofReal.comp measurable_realKernel).const_mul (-Complex.I)

private theorem realKernel_neg (t : ℝ) : realKernel (-t) = -realKernel t := by
  simp only [realKernel_def, Real.sin_neg, weightLaplaceTransform_neg]
  ring

/-- The reciprocal kernel is **odd**.  This is the symmetry the Haagerup--Zsidó
argument uses to pair `t` with `-t`; it comes from `sin` being odd while the
Laplace transform, depending only on `|t|`, is even. -/
theorem reciprocalKernel_neg (t : ℝ) :
    reciprocalKernel (-t) = -reciprocalKernel t := by
  simp only [reciprocalKernel_def, realKernel_neg, Complex.ofReal_neg]
  ring

/-- Multiplying by `-i` is an isometry, so the complex kernel has the same
modulus as the real one. -/
theorem norm_reciprocalKernel (t : ℝ) : ‖reciprocalKernel t‖ = |realKernel t| := by
  simp [reciprocalKernel_def]

/-- The modulus of the real kernel in closed form.  Only `sin` carries a sign —
the Laplace transform is already nonnegative — which is what makes the `L¹` mass
computable. -/
theorem abs_realKernel (t : ℝ) :
    |realKernel t| = |Real.sin t| / 2 * weightLaplaceTransform t := by
  rw [realKernel_def, abs_mul, abs_div, abs_two,
    abs_of_nonneg (weightLaplaceTransform_nonneg t)]

end

end HaagerupZsido
end TauCeti
