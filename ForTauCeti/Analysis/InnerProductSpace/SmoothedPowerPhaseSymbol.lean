/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SmoothedPowerPhase
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# An analytic phase symbol for the smoothed-power family

Positive smoothing gives a complex differentiable extension of the phase
gradient at every unit-circle point. The equal-gradient two-point CFC
calculus can therefore be applied uniformly in the exponent.

The extension calculation adapts `SchattenPhaseSymbol` and
`CharbonnierPhaseSymbol`; those are formalizations of classical functional
calculus ingredients. This module does not assert independent-plane global
optimization or historical priority for that optimization.
-/

public section

noncomputable section

namespace TauCeti

open scoped ComplexConjugate

/-- Scalar phase gradient without a choice of argument. -/
@[expose] def smoothedPowerPhaseDerivative (p tau : ℝ) (z : ℂ) : ℝ :=
  (conj (smoothedPowerDisplacementGradient p tau z) * (Complex.I * z)).re

theorem smoothedPowerPhaseDerivative_eq (p tau : ℝ) (z : ℂ) :
    smoothedPowerPhaseDerivative p tau z =
      p * (tau ^ 2 + ‖z - 1‖ ^ 2) ^ ((p - 2) / 2) * z.im := by
  simp only [smoothedPowerPhaseDerivative, smoothedPowerDisplacementGradient,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  ring

/-- Complex extension of the phase symbol. -/
@[expose] def smoothedPowerPhaseExtension (p tau : ℝ) (z : ℂ) : ℂ :=
  (p : ℂ) * (((tau ^ 2 + 2 : ℝ) : ℂ) - z - z⁻¹) ^ (((p - 2) / 2 : ℝ) : ℂ) *
    (z - z⁻¹) / (2 * Complex.I)

private theorem radicand_eq (tau : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ((tau ^ 2 + 2 : ℝ) : ℂ) - z - z⁻¹ =
      ((tau ^ 2 + ‖z - 1‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.inv_eq_conj hz]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.ofReal_re, Complex.conj_re]
    rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one hz]
    ring
  · simp only [Complex.sub_im, Complex.ofReal_im, Complex.conj_im]
    ring

/-- Agreement with the actual phase gradient on every unitary scalar. -/
theorem smoothedPowerPhaseExtension_eq_of_norm_eq_one
    (p tau : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    smoothedPowerPhaseExtension p tau z = (smoothedPowerPhaseDerivative p tau z : ℂ) := by
  rw [smoothedPowerPhaseExtension, radicand_eq tau z hz,
    ← Complex.ofReal_cpow (by positivity : 0 ≤ tau ^ 2 + ‖z - 1‖ ^ 2),
    Complex.inv_eq_conj hz, smoothedPowerPhaseDerivative_eq]
  apply (div_eq_iff (mul_ne_zero (by norm_num) Complex.I_ne_zero)).2
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im] <;> ring

/-- Every circle point is regular under positive smoothing, for all real
exponents. Convexity of the cost is a separate hypothesis. -/
theorem differentiableAt_smoothedPowerPhaseExtension
    (p tau : ℝ) (htau : 0 < tau) (z : ℂ) (hz : ‖z‖ = 1) :
    DifferentiableAt ℂ (smoothedPowerPhaseExtension p tau) z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hslit : ((tau ^ 2 + 2 : ℝ) : ℂ) - z - z⁻¹ ∈ Complex.slitPlane := by
    rw [radicand_eq tau z hz, Complex.ofReal_mem_slitPlane]
    exact smoothedPower_radicand_pos tau htau z
  have hrad : DifferentiableAt ℂ
      (fun w : ℂ => ((tau ^ 2 + 2 : ℝ) : ℂ) - w - w⁻¹) z :=
    ((differentiableAt_const _).sub differentiableAt_id).sub
      (differentiableAt_id.inv hz0)
  exact (((differentiableAt_const (p : ℂ)).mul
    (hrad.cpow_const (c := (((p - 2) / 2 : ℝ) : ℂ)) hslit)).mul
      (differentiableAt_id.sub (differentiableAt_id.inv hz0))).div_const _

theorem continuousOn_smoothedPowerPhaseExtension_circle (p tau : ℝ) (htau : 0 < tau) :
    ContinuousOn (smoothedPowerPhaseExtension p tau) (Metric.sphere (0 : ℂ) 1) := by
  intro z hz
  exact (differentiableAt_smoothedPowerPhaseExtension p tau htau z
    (by simpa only [Metric.mem_sphere, dist_zero_right] using hz)).continuousAt.continuousWithinAt

/-- The complex symbol restricts to the actual derivative of the scalar
phase cost. -/
theorem smoothedPowerPhaseDerivative_exp (p tau t : ℝ) :
    smoothedPowerPhaseDerivative p tau (Complex.exp ((t : ℂ) * Complex.I)) =
      smoothedPowerPhaseSlope p tau t := by
  rw [smoothedPowerPhaseDerivative_eq,
    Complex.norm_sub_one_sq_eq_of_norm_eq_one (Complex.norm_exp_ofReal_mul_I t)]
  have hre : (Complex.exp ((t : ℂ) * Complex.I)).re = Real.cos t := by
    rw [Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have him : (Complex.exp ((t : ℂ) * Complex.I)).im = Real.sin t := by
    rw [Complex.exp_mul_I]
    simp [Complex.sin_ofReal_re]
  rw [hre, him]
  dsimp only [smoothedPowerPhaseSlope]
  rw [show tau ^ 2 + 2 * (1 - Real.cos t) = tau ^ 2 + 2 - 2 * Real.cos t by ring]
  ring

/-- Tangential differentiation of the extension is the actual scalar
curvature, including the identity and reflection eigenphases. -/
theorem smoothedPowerPhaseExtension_deriv_mul_I_exp
    (p tau theta : ℝ) (htau : 0 < tau) :
    deriv (smoothedPowerPhaseExtension p tau) (Complex.exp ((theta : ℂ) * Complex.I)) *
      (Complex.I * Complex.exp ((theta : ℂ) * Complex.I)) =
        (smoothedPowerPhaseCurvature p tau theta : ℂ) := by
  have hdiff := differentiableAt_smoothedPowerPhaseExtension p tau htau
    (Complex.exp ((theta : ℂ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I theta)
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (w * Complex.I))
      (Complex.I * Complex.exp ((theta : ℂ) * Complex.I)) (theta : ℂ) := by
    simpa only [Function.comp_def, one_mul, mul_one, mul_comm] using
      (Complex.hasDerivAt_exp ((theta : ℂ) * Complex.I)).comp (theta : ℂ)
        ((hasDerivAt_id' (theta : ℂ)).mul_const Complex.I)
  have hcomp := (hdiff.hasDerivAt.comp (theta : ℂ) hexp).comp_ofReal
  have heq : (fun t : ℝ => smoothedPowerPhaseExtension p tau
      (Complex.exp ((t : ℂ) * Complex.I))) =
      (fun t : ℝ => (smoothedPowerPhaseSlope p tau t : ℂ)) := by
    funext t
    rw [smoothedPowerPhaseExtension_eq_of_norm_eq_one p tau _
      (Complex.norm_exp_ofReal_mul_I t), smoothedPowerPhaseDerivative_exp]
  change HasDerivAt (fun t : ℝ => smoothedPowerPhaseExtension p tau
    (Complex.exp ((t : ℂ) * Complex.I))) _ theta at hcomp
  rw [heq] at hcomp
  exact hcomp.unique (hasDerivAt_smoothedPowerPhaseSlope p tau theta htau).ofReal_comp

end TauCeti
