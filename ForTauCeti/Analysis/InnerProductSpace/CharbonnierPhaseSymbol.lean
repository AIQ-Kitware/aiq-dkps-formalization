/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierSpectralTrace
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# A holomorphic extension of the Charbonnier phase gradient

Positive smoothing keeps the unit-circle radicand in the positive real
axis. The complex extension is therefore differentiable at every circle
point, including the identity. This removes the zero-displacement
exception in second variations of the smoothed spectral cost.
-/

public section

noncomputable section

namespace TauCeti

/-- Complex extension of the scalar Charbonnier phase gradient. -/
@[expose] def charbonnierPhaseExtension (tau : ℝ) (z : ℂ) : ℂ :=
  (((tau ^ 2 + 2 : ℝ) : ℂ) - z - z⁻¹) ^ ((-(1 / 2) : ℝ) : ℂ) *
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

/-- The extension agrees with the real phase gradient on the whole circle. -/
theorem charbonnierPhaseExtension_eq_of_norm_eq_one
    (tau : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    charbonnierPhaseExtension tau z =
      ((z.im / Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2) : ℝ) : ℂ) := by
  rw [charbonnierPhaseExtension, radicand_eq tau z hz,
    ← Complex.ofReal_cpow (by positivity : 0 ≤ tau ^ 2 + ‖z - 1‖ ^ 2),
    Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Complex.inv_eq_conj hz]
  apply (div_eq_iff (mul_ne_zero (by norm_num) Complex.I_ne_zero)).2
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im] <;> ring

/-- Positive smoothing gives complex differentiability even at identity. -/
theorem differentiableAt_charbonnierPhaseExtension
    (tau : ℝ) (htau : 0 < tau) (z : ℂ) (hz : ‖z‖ = 1) :
    DifferentiableAt ℂ (charbonnierPhaseExtension tau) z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hslit : ((tau ^ 2 + 2 : ℝ) : ℂ) - z - z⁻¹ ∈ Complex.slitPlane := by
    rw [radicand_eq tau z hz, Complex.ofReal_mem_slitPlane]
    positivity
  have hrad : DifferentiableAt ℂ
      (fun w : ℂ => ((tau ^ 2 + 2 : ℝ) : ℂ) - w - w⁻¹) z :=
    ((differentiableAt_const _).sub differentiableAt_id).sub
      (differentiableAt_id.inv hz0)
  exact ((hrad.cpow_const (c := ((-(1 / 2) : ℝ) : ℂ)) hslit).mul
    (differentiableAt_id.sub (differentiableAt_id.inv hz0))).div_const _

/-- Continuity on the entire circle is inherited from local complex
differentiability, with no singular displacement endpoint. -/
theorem continuousOn_charbonnierPhaseExtension_circle (tau : ℝ) (htau : 0 < tau) :
    ContinuousOn (charbonnierPhaseExtension tau) (Metric.sphere (0 : ℂ) 1) := by
  intro z hz
  exact (differentiableAt_charbonnierPhaseExtension tau htau z
    (by simpa only [Metric.mem_sphere, dist_zero_right] using hz)).continuousAt.continuousWithinAt

/-- Real tangential differentiation determines the complex derivative
of the extension at every unitary phase. -/
theorem charbonnierPhaseExtension_deriv_mul_I_exp
    (tau theta d : ℝ) (htau : 0 < tau)
    (hphase : HasDerivAt
      (fun t : ℝ => (Complex.exp ((t : ℂ) * Complex.I)).im /
        Real.sqrt (tau ^ 2 + ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2)) d theta) :
    deriv (charbonnierPhaseExtension tau) (Complex.exp ((theta : ℂ) * Complex.I)) *
      (Complex.I * Complex.exp ((theta : ℂ) * Complex.I)) = (d : ℂ) := by
  have hdiff := differentiableAt_charbonnierPhaseExtension tau htau
    (Complex.exp ((theta : ℂ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I theta)
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (w * Complex.I))
      (Complex.I * Complex.exp ((theta : ℂ) * Complex.I)) (theta : ℂ) := by
    simpa only [Function.comp_def, one_mul, mul_one, mul_comm] using
      (Complex.hasDerivAt_exp ((theta : ℂ) * Complex.I)).comp (theta : ℂ)
        ((hasDerivAt_id' (theta : ℂ)).mul_const Complex.I)
  have hcomp := (hdiff.hasDerivAt.comp (theta : ℂ) hexp).comp_ofReal
  change HasDerivAt
    (fun t : ℝ => charbonnierPhaseExtension tau (Complex.exp ((t : ℂ) * Complex.I))) _ theta
      at hcomp
  have heq :
      (fun t : ℝ => charbonnierPhaseExtension tau (Complex.exp ((t : ℂ) * Complex.I))) =
      (fun t : ℝ => (((Complex.exp ((t : ℂ) * Complex.I)).im /
        Real.sqrt (tau ^ 2 + ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2) : ℝ) : ℂ)) := by
    funext t
    exact charbonnierPhaseExtension_eq_of_norm_eq_one tau _ (Complex.norm_exp_ofReal_mul_I t)
  rw [heq] at hcomp
  exact hcomp.unique hphase.ofReal_comp

end TauCeti
