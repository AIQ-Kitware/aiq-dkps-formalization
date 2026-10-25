/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPhaseCurvature
public import ForTauCeti.Analysis.CStarAlgebra.TwoPointDerivative

/-!
# Actual Charbonnier second variations on two-phase gradient blocks

The two phases may include identity and reflection eigenvalues. The
operator derivative holds on any complete complex Hilbert space, while
the trace Hessian of the literal singular-value objective is finite
dimensional. These formulas apply to the actual transporter curve.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The complex extension and the actual phase gradient have identical
functional calculus at every unitary. -/
theorem smoothedUnitaryGradient_eq_cfc_phaseExtension
    (tau : ℝ) (U : unitary (E →L[ℂ] E)) :
    smoothedUnitaryGradient tau (U : E →L[ℂ] E) =
      cfc (charbonnierPhaseExtension tau) (U : E →L[ℂ] E) := by
  change cfc (fun z => (smoothedPhaseDerivative tau z : ℂ)) (U : E →L[ℂ] E) = _
  apply cfc_congr
  intro z hz
  change (smoothedPhaseDerivative tau z : ℂ) = charbonnierPhaseExtension tau z
  rw [smoothedPhaseDerivative_eq]
  exact (charbonnierPhaseExtension_eq_of_norm_eq_one tau z
    (by simpa only [Metric.mem_sphere, dist_zero_right] using
      spectrum.subset_circle_of_unitary U.2 hz)).symm

/-- Exact actual gradient derivative at two distinct phases with equal
gradient values. Zero displacement is allowed. -/
theorem hasDerivAt_smoothedUnitaryGradient_two_phase
    (tau alpha beta : ℝ) (htau : 0 < tau)
    (hab : Complex.exp ((alpha : ℂ) * Complex.I) ≠
      Complex.exp ((beta : ℂ) * Complex.I))
    (hlevel : smoothedPhaseDerivative tau (Complex.exp ((alpha : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((beta : ℂ) * Complex.I)))
    (U : ℝ → E →L[ℂ] E) (x : ℝ) (H : E →L[ℂ] E)
    (hunit : ∀ t, U t ∈ unitary (E →L[ℂ] E))
    (hU : HasDerivAt U (U x * (Complex.I • H)) x)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hrepr : U x = Complex.exp ((alpha : ℂ) * Complex.I) • 1 +
      (Complex.exp ((beta : ℂ) * Complex.I) -
        Complex.exp ((alpha : ℂ) * Complex.I)) • P) :
    HasDerivAt (fun t => smoothedUnitaryGradient tau (U t))
      ((smoothedPhaseCurvature tau alpha : ℂ) • ((1 - P) * H * (1 - P)) +
       (smoothedPhaseCurvature tau beta : ℂ) • (P * H * P)) x := by
  let a := Complex.exp ((alpha : ℂ) * Complex.I)
  let b := Complex.exp ((beta : ℂ) * Complex.I)
  have hfa : charbonnierPhaseExtension tau a = (smoothedPhaseDerivative tau a : ℂ) := by
    rw [smoothedPhaseDerivative_eq]
    exact charbonnierPhaseExtension_eq_of_norm_eq_one tau a
      (Complex.norm_exp_ofReal_mul_I alpha)
  have hfb : charbonnierPhaseExtension tau b = (smoothedPhaseDerivative tau a : ℂ) := by
    change charbonnierPhaseExtension tau b =
      (smoothedPhaseDerivative tau (Complex.exp ((alpha : ℂ) * Complex.I)) : ℂ)
    rw [hlevel]
    rw [smoothedPhaseDerivative_eq]
    exact charbonnierPhaseExtension_eq_of_norm_eq_one tau b
      (Complex.norm_exp_ofReal_mul_I beta)
  have hdphase (t : ℝ) := hasDerivAt_smoothedPhaseDerivative_exp tau t htau
  simp only [smoothedPhaseDerivative_eq] at hdphase
  have hd := hasDerivAt_cfc_unitary_tangent_of_affine_projection
    (charbonnierPhaseExtension tau) a b (smoothedPhaseDerivative tau a : ℂ)
    (smoothedPhaseCurvature tau alpha : ℂ) (smoothedPhaseCurvature tau beta : ℂ)
    hab hfa hfb (Metric.sphere (0 : ℂ) 1) (isCompact_sphere 0 1)
    (continuousOn_charbonnierPhaseExtension_circle tau htau)
    (differentiableAt_charbonnierPhaseExtension tau htau a
      (Complex.norm_exp_ofReal_mul_I alpha))
    (differentiableAt_charbonnierPhaseExtension tau htau b
      (Complex.norm_exp_ofReal_mul_I beta))
    (charbonnierPhaseExtension_deriv_mul_I_exp tau alpha _ htau (hdphase alpha))
    (charbonnierPhaseExtension_deriv_mul_I_exp tau beta _ htau (hdphase beta))
    U x H hU (fun t => isStarNormal_of_mem_unitary (hunit t))
    (fun t => spectrum.subset_circle_of_unitary (hunit t)) P hP hrepr
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    smoothedUnitaryGradient_eq_cfc_phaseExtension tau ⟨U t, hunit t⟩)

variable [FiniteDimensional ℂ E]

/-- The literal Charbonnier objective has the two-compression Hessian
at every two-phase constant-gradient unitary, including reflection blocks. -/
theorem hasDerivAt_deriv_smoothed_unitary_two_phase
    (tau alpha beta : ℝ) (htau : 0 < tau)
    (hab : Complex.exp ((alpha : ℂ) * Complex.I) ≠
      Complex.exp ((beta : ℂ) * Complex.I))
    (hlevel : smoothedPhaseDerivative tau (Complex.exp ((alpha : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((beta : ℂ) * Complex.I)))
    (U : unitary (E →L[ℂ] E)) (H P : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P)
    (hrepr : (U : E →L[ℂ] E) = Complex.exp ((alpha : ℂ) * Complex.I) • 1 +
      (Complex.exp ((beta : ℂ) * Complex.I) -
        Complex.exp ((alpha : ℂ) * Complex.I)) • P) :
    let C := fun t : ℝ => smoothedDisplacementCost tau
      ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))).toLinearMap
    HasDerivAt (deriv C)
      (smoothedPhaseCurvature tau alpha * (LinearMap.trace ℂ E
        (((1 - P) * H * (1 - P)).adjoint * ((1 - P) * H * (1 - P))).toLinearMap).re +
       smoothedPhaseCurvature tau beta *
        (LinearMap.trace ℂ E ((P * H * P).adjoint * (P * H * P)).toLinearMap).re) 0 := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  let V : ℝ → E →L[ℂ] E := fun t =>
    (U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))
  let C := fun t : ℝ => smoothedDisplacementCost tau (V t).toLinearMap
  let D : E →L[ℂ] E :=
    (smoothedPhaseCurvature tau alpha : ℂ) • ((1 - P) * H * (1 - P)) +
    (smoothedPhaseCurvature tau beta : ℂ) • (P * H * P)
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
  have hgrad : HasDerivAt (fun t => smoothedUnitaryGradient tau (V t)) D 0 :=
    hasDerivAt_smoothedUnitaryGradient_two_phase tau alpha beta htau hab hlevel
      V 0 H hunit hV P hP (hV0.trans hrepr)
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
    (tr (D * H)) 0 at hd
  rw [← hderiv] at hd
  apply hd.congr_deriv
  have hcomplex : LinearMap.trace ℂ E (D * H).toLinearMap =
      (smoothedPhaseCurvature tau alpha : ℂ) * LinearMap.trace ℂ E
        (((1 - P) * H * (1 - P)).adjoint * ((1 - P) * H * (1 - P))).toLinearMap +
      (smoothedPhaseCurvature tau beta : ℂ) *
        LinearMap.trace ℂ E ((P * H * P).adjoint * (P * H * P)).toLinearMap := by
    dsimp only [D]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc,
      _root_.ContinuousLinearMap.toLinearMap_add,
      _root_.ContinuousLinearMap.toLinearMap_smul, _root_.ContinuousLinearMap.toLinearMap_smul,
      map_add, map_smul, map_smul,
      ContinuousLinearMap.trace_compression_mul_eq_trace_adjoint_square H (1 - P) hH hP.one_sub,
      ContinuousLinearMap.trace_compression_mul_eq_trace_adjoint_square H P hH hP]
    simp only [smul_eq_mul]
  rw [htr, hcomplex, Complex.add_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
