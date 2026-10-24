/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenUnitaryVariation
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# A complex extension of the Schatten phase symbol

On the unit circle, the real phase-gradient symbol agrees with
`p (2 - z - z⁻¹)^((p - 2)/2) (z - z⁻¹) / (2 i)`. This extension is
complex differentiable near every unit-circle point other than `1`.
For `p > 1` it is continuous on the entire unit circle, including `1`.

The extension allows the two-point normal functional-calculus derivative
to be applied without asking the real-valued phase symbol itself to be
complex differentiable.
-/

public section

noncomputable section

namespace TauCeti

open scoped ComplexConjugate

/-- A complex extension of the Schatten phase derivative from the unit
circle, using the principal complex power. -/
def schattenPhaseExtension (p : ℝ) (z : ℂ) : ℂ :=
  (p : ℂ) * (2 - z - z⁻¹) ^ (((p - 2) / 2 : ℝ) : ℂ) * (z - z⁻¹) /
    (2 * Complex.I)

theorem schattenPhaseExtension_def (p : ℝ) (z : ℂ) :
    schattenPhaseExtension p z =
      (p : ℂ) * (2 - z - z⁻¹) ^ (((p - 2) / 2 : ℝ) : ℂ) * (z - z⁻¹) /
        (2 * Complex.I) := by rfl

private theorem unitary_radicand_eq_norm_sub_one_sq (z : ℂ) (hz : ‖z‖ = 1) :
    2 - z - z⁻¹ = ((‖z - 1‖ ^ 2 : ℝ) : ℂ) := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz, one_pow, Complex.normSq_apply] at h
    nlinarith
  rw [Complex.inv_eq_conj hz]
  apply Complex.ext
  · change (2 : ℝ) - z.re - z.re = ‖z - 1‖ ^ 2
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  · simp only [Complex.sub_im, Complex.im_ofNat, Complex.conj_im, Complex.ofReal_im]
    ring

/-- The extension agrees with the actual real phase gradient on every
unitary scalar, including the identity. -/
theorem schattenPhaseExtension_eq_of_norm_eq_one (p : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    schattenPhaseExtension p z = (schattenPhaseDerivative p z : ℂ) := by
  have hpow : (‖z - 1‖ ^ 2) ^ ((p - 2) / 2) = ‖z - 1‖ ^ (p - 2) := by
    calc
      _ = (‖z - 1‖ ^ (2 : ℝ)) ^ ((p - 2) / 2) := by rw [Real.rpow_two]
      _ = ‖z - 1‖ ^ ((2 : ℝ) * ((p - 2) / 2)) :=
        (Real.rpow_mul (norm_nonneg _) _ _).symm
      _ = _ := by congr 1; ring
  rw [schattenPhaseExtension_def, unitary_radicand_eq_norm_sub_one_sq z hz,
    ← Complex.ofReal_cpow (sq_nonneg ‖z - 1‖), hpow, Complex.inv_eq_conj hz,
    schattenPhaseDerivative_eq]
  apply (div_eq_iff (mul_ne_zero (by norm_num) Complex.I_ne_zero)).2
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im] <;> ring

/-- Away from the identity, the unit-circle phase symbol has a complex
differentiable extension. -/
theorem differentiableAt_schattenPhaseExtension (p : ℝ) (z : ℂ)
    (hz : ‖z‖ = 1) (hzone : z ≠ 1) :
    DifferentiableAt ℂ (schattenPhaseExtension p) z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hslit : 2 - z - z⁻¹ ∈ Complex.slitPlane := by
    rw [unitary_radicand_eq_norm_sub_one_sq z hz, Complex.ofReal_mem_slitPlane]
    exact sq_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hzone))
  have hrad : DifferentiableAt ℂ (fun w : ℂ => 2 - w - w⁻¹) z :=
    ((differentiableAt_const (2 : ℂ)).sub differentiableAt_id).sub
      (differentiableAt_id.inv hz0)
  have hpow := hrad.cpow_const (c := (((p - 2) / 2 : ℝ) : ℂ)) hslit
  exact (((differentiableAt_const (p : ℂ)).mul hpow).mul
    (differentiableAt_id.sub (differentiableAt_id.inv hz0))).div_const _

/-- The actual phase symbol is continuous, including at zero
displacement, for every exponent greater than one. -/
theorem continuous_schattenPhaseDerivative (p : ℝ) (hp : 1 < p) :
    Continuous (schattenPhaseDerivative p) := by
  have h : Continuous (fun z : ℂ =>
      (conj (((p * ‖z - 1‖ ^ (p - 2) : ℝ) : ℂ) * (z - 1)) *
        (Complex.I * z)).re) :=
    Complex.continuous_re.comp
      ((Complex.continuous_conj.comp (continuous_norm_sub_one_rpow_gradient p hp)).mul
        ((continuous_const (y := Complex.I)).mul continuous_id))
  convert h using 1
  funext z
  exact schattenPhaseDerivative_def p z

/-- The complex extension is continuous on the entire unit circle, even
though complex differentiability at the identity is not asserted. -/
theorem continuousOn_schattenPhaseExtension_circle (p : ℝ) (hp : 1 < p) :
    ContinuousOn (schattenPhaseExtension p) (Metric.sphere (0 : ℂ) 1) := by
  have heq : Set.EqOn (schattenPhaseExtension p)
      (fun z => (schattenPhaseDerivative p z : ℂ)) (Metric.sphere (0 : ℂ) 1) := by
    intro z hz
    exact schattenPhaseExtension_eq_of_norm_eq_one p z
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz)
  exact (continuousOn_congr heq).2
    (Complex.continuous_ofReal.comp (continuous_schattenPhaseDerivative p hp)).continuousOn

/-- A real phase derivative determines the tangential derivative of
the complex extension on the unit circle. -/
theorem schattenPhaseExtension_deriv_mul_I_exp
    (p theta d : ℝ)
    (hne : Complex.exp ((theta : ℂ) * Complex.I) ≠ 1)
    (hphase : HasDerivAt
      (fun t : ℝ => schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I))) d theta) :
    deriv (schattenPhaseExtension p) (Complex.exp ((theta : ℂ) * Complex.I)) *
      (Complex.I * Complex.exp ((theta : ℂ) * Complex.I)) = (d : ℂ) := by
  have hdiff := differentiableAt_schattenPhaseExtension p
    (Complex.exp ((theta : ℂ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I theta) hne
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (w * Complex.I))
      (Complex.I * Complex.exp ((theta : ℂ) * Complex.I)) (theta : ℂ) := by
    simpa only [Function.comp_def, one_mul, mul_one, mul_comm] using
      (Complex.hasDerivAt_exp ((theta : ℂ) * Complex.I)).comp (theta : ℂ)
        ((hasDerivAt_id' (theta : ℂ)).mul_const Complex.I)
  have hcomp := (hdiff.hasDerivAt.comp (theta : ℂ) hexp).comp_ofReal
  change HasDerivAt
    (fun t : ℝ => schattenPhaseExtension p (Complex.exp ((t : ℂ) * Complex.I))) _ theta at hcomp
  have heq : (fun t : ℝ => schattenPhaseExtension p (Complex.exp ((t : ℂ) * Complex.I))) =
      (fun t : ℝ => (schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) : ℂ)) := by
    funext t
    exact schattenPhaseExtension_eq_of_norm_eq_one p _ (Complex.norm_exp_ofReal_mul_I t)
  rw [heq] at hcomp
  exact hcomp.unique hphase.ofReal_comp

/-- The derivative of the odd phase-gradient symbol is unchanged when
the phase changes sign. -/
theorem hasDerivAt_schattenPhaseDerivative_exp_neg
    (p theta d : ℝ)
    (hphase : HasDerivAt
      (fun t : ℝ => schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I))) d theta) :
    HasDerivAt
      (fun t : ℝ => schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I))) d (-theta) := by
  have h := (hphase.comp_of_eq (-theta) ((hasDerivAt_id' (-theta)).neg) (by simp)).neg
  have h' : HasDerivAt
      (fun t : ℝ => -schattenPhaseDerivative p
        (Complex.exp (((-t : ℝ) : ℂ) * Complex.I))) d (-theta) := by
    simpa only [Function.comp_def, Pi.neg_apply, mul_neg, mul_one, neg_neg] using! h
  convert h' using 1
  funext t
  rw [schattenPhaseDerivative_exp_neg, neg_neg]

/-- For a unitary operator, the complex extension gives exactly the
same functional calculus as the actual self-adjoint phase gradient. -/
theorem schattenUnitaryGradient_eq_cfc_phaseExtension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (p : ℝ) (U : unitary (E →L[ℂ] E)) :
    schattenUnitaryGradient p (U : E →L[ℂ] E) =
      cfc (schattenPhaseExtension p) (U : E →L[ℂ] E) := by
  rw [schattenUnitaryGradient_def]
  apply cfc_congr
  intro z hz
  symm
  exact schattenPhaseExtension_eq_of_norm_eq_one p z
    (by simpa only [Metric.mem_sphere, dist_zero_right] using
      spectrum.subset_circle_of_unitary U.2 hz)

end TauCeti
