/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Complex smooth-core Green identities for the free--free beam

The Hilbert-space realization of the beam is complex, so the production Green
formula must use the Hermitian pairing.  This file repeats the smooth-core
calculation with complex-valued functions and conjugation in the first slot.

For fourth-order data `u` and `v`, the boundary concomitant

`conj u * v''' - conj u' * v'' + conj u'' * v' - conj u''' * v`

differentiates to `conj u * v'''' - conj u'''' * v`.  Free endpoint
conditions kill the boundary term.  Taking `v = u` gives

`integral conj(u) * u'''' = integral ‖u''‖^2`,

which is the symmetry and positivity calculation required by the complex
closed-operator realization.
-/

open Set
open scoped Interval ComplexConjugate

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace FreeBeam

noncomputable section

/-- Classical complex fourth-order derivative data on the real line. -/
structure ComplexFourthOrderData where
  f0 : ℝ → ℂ
  f1 : ℝ → ℂ
  f2 : ℝ → ℂ
  f3 : ℝ → ℂ
  f4 : ℝ → ℂ
  continuous0 : Continuous f0
  continuous1 : Continuous f1
  continuous2 : Continuous f2
  continuous3 : Continuous f3
  continuous4 : Continuous f4
  deriv0 : ∀ x, HasDerivAt f0 (f1 x) x
  deriv1 : ∀ x, HasDerivAt f1 (f2 x) x
  deriv2 : ∀ x, HasDerivAt f2 (f3 x) x
  deriv3 : ∀ x, HasDerivAt f3 (f4 x) x

namespace ComplexFourthOrderData

/-- Free--free endpoint conditions for a complex smooth function. -/
def FreeBoundary (u : ComplexFourthOrderData) : Prop :=
  u.f2 0 = 0 ∧ u.f3 0 = 0 ∧ u.f2 1 = 0 ∧ u.f3 1 = 0

/-- Conjugation commutes with differentiation along a real variable. -/
theorem hasDerivAt_conj
    {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => conj (f y)) (conj f') x := by
  have hcomp :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp
      x hf.hasFDerivAt
  simpa only [Function.comp_def, Complex.conjCLE_apply] using hcomp.hasDerivAt

/-- Hermitian fourth-order Green boundary concomitant. -/
def greenBoundary (u v : ComplexFourthOrderData) (x : ℝ) : ℂ :=
  conj (u.f0 x) * v.f3 x - conj (u.f1 x) * v.f2 x +
    conj (u.f2 x) * v.f1 x - conj (u.f3 x) * v.f0 x

/-- Derivative of the Hermitian Green concomitant. -/
theorem hasDerivAt_greenBoundary
    (u v : ComplexFourthOrderData) (x : ℝ) :
    HasDerivAt (greenBoundary u v)
      (conj (u.f0 x) * v.f4 x - conj (u.f4 x) * v.f0 x) x := by
  unfold greenBoundary
  convert
    ((((hasDerivAt_conj (u.deriv0 x)).mul (v.deriv3 x)).sub
      ((hasDerivAt_conj (u.deriv1 x)).mul (v.deriv2 x))).add
      ((hasDerivAt_conj (u.deriv2 x)).mul (v.deriv1 x))).sub
      ((hasDerivAt_conj (u.deriv3 x)).mul (v.deriv0 x))
    using 1 <;> ring

/-- Continuity of the complex Green integrand. -/
theorem continuous_greenIntegrand (u v : ComplexFourthOrderData) :
    Continuous fun x =>
      conj (u.f0 x) * v.f4 x - conj (u.f4 x) * v.f0 x := by
  exact
    ((Complex.continuous_conj.comp u.continuous0).mul v.continuous4).sub
      ((Complex.continuous_conj.comp u.continuous4).mul v.continuous0)

/-- Complex fourth-order Green formula with boundary terms. -/
theorem integral_green_formula (u v : ComplexFourthOrderData) :
    (∫ x in (0 : ℝ)..1,
      (conj (u.f0 x) * v.f4 x - conj (u.f4 x) * v.f0 x)) =
      greenBoundary u v 1 - greenBoundary u v 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (hasDerivAt_greenBoundary u v)
    (continuous_greenIntegrand u v).intervalIntegrable

/-- The complex Green boundary term vanishes at a free endpoint. -/
theorem greenBoundary_eq_zero_of_freeEndpoint
    (u v : ComplexFourthOrderData) {x : ℝ}
    (hu2 : u.f2 x = 0) (hu3 : u.f3 x = 0)
    (hv2 : v.f2 x = 0) (hv3 : v.f3 x = 0) :
    greenBoundary u v x = 0 := by
  unfold greenBoundary
  rw [hu2, hu3, hv2, hv3]
  ring

/-- Hermitian Green symmetry on the smooth free--free core. -/
theorem integral_free_green_symmetry
    (u v : ComplexFourthOrderData)
    (hu : u.FreeBoundary) (hv : v.FreeBoundary) :
    (∫ x in (0 : ℝ)..1, conj (u.f0 x) * v.f4 x) =
      ∫ x in (0 : ℝ)..1, conj (u.f4 x) * v.f0 x := by
  rcases hu with ⟨hu20, hu30, hu21, hu31⟩
  rcases hv with ⟨hv20, hv30, hv21, hv31⟩
  have hgreen := integral_green_formula u v
  have h0 : greenBoundary u v 0 = 0 :=
    greenBoundary_eq_zero_of_freeEndpoint u v hu20 hu30 hv20 hv30
  have h1 : greenBoundary u v 1 = 0 :=
    greenBoundary_eq_zero_of_freeEndpoint u v hu21 hu31 hv21 hv31
  rw [h0, h1, sub_zero] at hgreen
  have hsplit := intervalIntegral.integral_sub
    ((Complex.continuous_conj.comp u.continuous0).mul
      v.continuous4).intervalIntegrable
    ((Complex.continuous_conj.comp u.continuous4).mul
      v.continuous0).intervalIntegrable
  rw [hsplit] at hgreen
  exact sub_eq_zero.mp hgreen

/-- Boundary expression for the complex beam energy identity. -/
def energyBoundary (u : ComplexFourthOrderData) (x : ℝ) : ℂ :=
  conj (u.f0 x) * u.f3 x - conj (u.f1 x) * u.f2 x

/-- Derivative of the complex energy boundary expression. -/
theorem hasDerivAt_energyBoundary
    (u : ComplexFourthOrderData) (x : ℝ) :
    HasDerivAt (energyBoundary u)
      (conj (u.f0 x) * u.f4 x - conj (u.f2 x) * u.f2 x) x := by
  unfold energyBoundary
  convert
    ((hasDerivAt_conj (u.deriv0 x)).mul (u.deriv3 x)).sub
      ((hasDerivAt_conj (u.deriv1 x)).mul (u.deriv2 x))
    using 1 <;> ring

/-- Continuity of the complex energy integrand. -/
theorem continuous_energyIntegrand (u : ComplexFourthOrderData) :
    Continuous fun x =>
      conj (u.f0 x) * u.f4 x - conj (u.f2 x) * u.f2 x := by
  exact
    ((Complex.continuous_conj.comp u.continuous0).mul u.continuous4).sub
      ((Complex.continuous_conj.comp u.continuous2).mul u.continuous2)

/-- Complex energy identity with the boundary term visible. -/
theorem integral_energy_formula (u : ComplexFourthOrderData) :
    (∫ x in (0 : ℝ)..1,
      (conj (u.f0 x) * u.f4 x - conj (u.f2 x) * u.f2 x)) =
      energyBoundary u 1 - energyBoundary u 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (hasDerivAt_energyBoundary u)
    (continuous_energyIntegrand u).intervalIntegrable

/-- The complex energy boundary term vanishes at a free endpoint. -/
theorem energyBoundary_eq_zero_of_freeEndpoint
    (u : ComplexFourthOrderData) {x : ℝ}
    (hu2 : u.f2 x = 0) (hu3 : u.f3 x = 0) :
    energyBoundary u x = 0 := by
  unfold energyBoundary
  rw [hu2, hu3]
  ring

/-- Positivity identity on the complex smooth free--free beam core. -/
theorem integral_free_energy
    (u : ComplexFourthOrderData) (hu : u.FreeBoundary) :
    (∫ x in (0 : ℝ)..1, conj (u.f0 x) * u.f4 x) =
      ∫ x in (0 : ℝ)..1, ((Complex.normSq (u.f2 x) : ℝ) : ℂ) := by
  rcases hu with ⟨hu20, hu30, hu21, hu31⟩
  have henergy := integral_energy_formula u
  have h0 : energyBoundary u 0 = 0 :=
    energyBoundary_eq_zero_of_freeEndpoint u hu20 hu30
  have h1 : energyBoundary u 1 = 0 :=
    energyBoundary_eq_zero_of_freeEndpoint u hu21 hu31
  rw [h0, h1, sub_zero] at henergy
  have hsplit := intervalIntegral.integral_sub
    ((Complex.continuous_conj.comp u.continuous0).mul
      u.continuous4).intervalIntegrable
    ((Complex.continuous_conj.comp u.continuous2).mul
      u.continuous2).intervalIntegrable
  rw [hsplit] at henergy
  have hnorm :
      (fun x => conj (u.f2 x) * u.f2 x) =
        fun x => ((Complex.normSq (u.f2 x) : ℝ) : ℂ) := by
    funext x
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [hnorm] at henergy
  exact sub_eq_zero.mp henergy

/-- The real part of the complex beam energy is nonnegative. -/
theorem re_integral_free_energy_nonneg
    (u : ComplexFourthOrderData) (hu : u.FreeBoundary) :
    0 ≤ re (∫ x in (0 : ℝ)..1, conj (u.f0 x) * u.f4 x) := by
  rw [integral_free_energy u hu]
  have hint : IntervalIntegrable
      (fun x => ((Complex.normSq (u.f2 x) : ℝ) : ℂ)) volume 0 1 := by
    exact ((u.continuous2.normSq).ofReal).intervalIntegrable
  rw [← Complex.reCLM_apply]
  rw [Complex.reCLM.integral_comp_comm hint]
  exact intervalIntegral.integral_nonneg (le_of_lt zero_lt_one) fun x _ =>
    Complex.normSq_nonneg (u.f2 x)

end ComplexFourthOrderData

end

end FreeBeam
end Scratch
end Experimental
end DavisKahan
end ForMathlib
