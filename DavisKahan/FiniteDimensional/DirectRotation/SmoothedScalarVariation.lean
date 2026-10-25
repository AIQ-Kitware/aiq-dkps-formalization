/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedTwoPhaseVariation

/-!
# Charbonnier variation at scalar and coalesced phases

The one-point functional-calculus derivative complements the distinct
two-phase formula. At a critical scalar unitary every Hermitian direction
has zero second variation, including when the critical spectral space has
arbitrary multiplicity. Higher-order growth requires a separate argument.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- At a scalar unitary the actual gradient derivative is its scalar
phase curvature times the Hermitian direction. Dimension is unrestricted. -/
theorem hasDerivAt_smoothedUnitaryGradient_scalar
    (tau alpha : ℝ) (htau : 0 < tau)
    (U : ℝ → E →L[ℂ] E) (x : ℝ) (H : E →L[ℂ] E)
    (hunit : ∀ t, U t ∈ unitary (E →L[ℂ] E))
    (hU : HasDerivAt U (U x * (Complex.I • H)) x)
    (hscalar : U x = Complex.exp ((alpha : ℂ) * Complex.I) • 1) :
    HasDerivAt (fun t => smoothedUnitaryGradient tau (U t))
      ((smoothedPhaseCurvature tau alpha : ℂ) • H) x := by
  have hdphase := hasDerivAt_smoothedPhaseDerivative_exp tau alpha htau
  simp only [smoothedPhaseDerivative_eq] at hdphase
  have hd := hasDerivAt_cfc_of_scalar (charbonnierPhaseExtension tau)
    (Complex.exp ((alpha : ℂ) * Complex.I)) (Metric.sphere (0 : ℂ) 1)
    (isCompact_sphere 0 1) (continuousOn_charbonnierPhaseExtension_circle tau htau)
    (differentiableAt_charbonnierPhaseExtension tau htau _ (Complex.norm_exp_ofReal_mul_I alpha))
    U x (U x * (Complex.I • H)) hU (fun t => isStarNormal_of_mem_unitary (hunit t))
    (fun t => spectrum.subset_circle_of_unitary (hunit t)) hscalar
  have hd' := hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    smoothedUnitaryGradient_eq_cfc_phaseExtension tau ⟨U t, hunit t⟩)
  apply hd'.congr_deriv
  rw [hscalar, smul_mul_assoc, one_mul, smul_smul, smul_smul, mul_assoc,
    mul_comm (Complex.exp ((alpha : ℂ) * Complex.I)) Complex.I,
    charbonnierPhaseExtension_deriv_mul_I_exp tau alpha _ htau hdphase]

variable [FiniteDimensional ℂ E]

/-- Actual cost Hessian at a scalar unitary, with no artificial second
spectral point and no displacement-invertibility hypothesis. -/
theorem hasDerivAt_deriv_smoothed_unitary_scalar
    (tau alpha : ℝ) (htau : 0 < tau)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hscalar : (U : E →L[ℂ] E) = Complex.exp ((alpha : ℂ) * Complex.I) • 1) :
    let C := fun t : ℝ => smoothedDisplacementCost tau
      ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))).toLinearMap
    HasDerivAt (deriv C) (smoothedPhaseCurvature tau alpha *
      (LinearMap.trace ℂ E (H.adjoint * H).toLinearMap).re) 0 := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  let V : ℝ → E →L[ℂ] E := fun t =>
    (U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))
  let C := fun t : ℝ => smoothedDisplacementCost tau (V t).toLinearMap
  have hunit (t : ℝ) : V t ∈ unitary (E →L[ℂ] E) := by
    apply mul_mem U.2
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  have hV0 : V 0 = (U : E →L[ℂ] E) := by
    simp only [V, zero_smul, NormedSpace.exp_zero, mul_one]
  have hV : HasDerivAt V (V 0 * (Complex.I • H)) 0 := by
    simpa only [V, zero_smul, NormedSpace.exp_zero, mul_one, one_mul] using
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • H) (0 : ℝ)).const_mul
        (U : E →L[ℂ] E)
  have hgrad := hasDerivAt_smoothedUnitaryGradient_scalar tau alpha htau V 0 H
    hunit hV (hV0.trans hscalar)
  let tr : (E →L[ℂ] E) →L[ℝ] ℝ :=
    Complex.reCLM.comp ((traceCLM ℂ E).restrictScalars ℝ)
  have htr (T : E →L[ℂ] E) : tr T = (LinearMap.trace ℂ E T.toLinearMap).re := by
    simp only [tr, _root_.ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
    exact congrArg Complex.re (traceCLM_apply T)
  have hd := tr.hasFDerivAt.comp_hasDerivAt 0 (hgrad.mul_const H)
  have hderiv : deriv C = (fun t => tr (smoothedUnitaryGradient tau (V t) * H)) := by
    funext t
    rw [htr]
    exact (hasDerivAt_smoothed_unitary_right_variation_at tau htau U H hH t).deriv
  change HasDerivAt (fun t => tr (smoothedUnitaryGradient tau (V t) * H))
    (tr (((smoothedPhaseCurvature tau alpha : ℂ) • H) * H)) 0 at hd
  rw [← hderiv] at hd
  apply hd.congr_deriv
  rw [htr, smul_mul_assoc, _root_.ContinuousLinearMap.toLinearMap_smul, map_smul]
  change ((smoothedPhaseCurvature tau alpha : ℂ) *
    LinearMap.trace ℂ E (H * H).toLinearMap).re = _
  rw [show H.adjoint = H from hH.star_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- At a coalesced critical phase every Hermitian direction has zero
second variation. This asserts neither local minimality nor higher-order
growth for an unpaired scalar block. -/
theorem hasDerivAt_deriv_smoothed_unitary_critical_scalar
    (tau alpha : ℝ) (htau : 0 < tau)
    (hcritical : Real.cos alpha = ((smoothingRadius tau)⁻¹) ^ 2)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hscalar : (U : E →L[ℂ] E) = Complex.exp ((alpha : ℂ) * Complex.I) • 1) :
    let C := fun t : ℝ => smoothedDisplacementCost tau
      ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))).toLinearMap
    HasDerivAt (deriv C) 0 0 := by
  have hcurv : smoothedPhaseCurvature tau alpha = 0 := by
    rw [smoothedPhaseCurvature_factor tau alpha htau, hcritical, sub_self,
      mul_zero, zero_div]
  simpa only [hcurv, zero_mul] using
    hasDerivAt_deriv_smoothed_unitary_scalar tau alpha htau U H hH hscalar

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
