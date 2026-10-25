/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenPhaseSymbol
public import ForTauCeti.Analysis.CStarAlgebra.TwoPointDerivative

/-!
# Schatten variations on a constant-gradient two-phase block

The complex phase-symbol extension and the two-point functional-calculus
derivative identify the derivative of the actual Schatten unitary gradient.
Only the two spectral compressions occur when their scalar gradient values
coincide. The operator space need not be finite dimensional for this step.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- At a two-phase unitary with equal scalar gradient values, the actual
gradient derivative is the sum of the two compressed tangent directions,
weighted by their real phase curvatures. -/
theorem hasDerivAt_schattenUnitaryGradient_two_phase
    (p alpha beta da db : ℝ) (hp : 1 < p)
    (hne_a : Complex.exp ((alpha : ℂ) * Complex.I) ≠ 1)
    (hne_b : Complex.exp ((beta : ℂ) * Complex.I) ≠ 1)
    (hab : Complex.exp ((alpha : ℂ) * Complex.I) ≠
      Complex.exp ((beta : ℂ) * Complex.I))
    (hlevel : schattenPhaseDerivative p (Complex.exp ((alpha : ℂ) * Complex.I)) =
      schattenPhaseDerivative p (Complex.exp ((beta : ℂ) * Complex.I)))
    (hda : HasDerivAt
      (fun t : ℝ => schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I))) da alpha)
    (hdb : HasDerivAt
      (fun t : ℝ => schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I))) db beta)
    (U : ℝ → E →L[ℂ] E) (x : ℝ) (H : E →L[ℂ] E)
    (hunit : ∀ t, U t ∈ unitary (E →L[ℂ] E))
    (hU : HasDerivAt U (U x * (Complex.I • H)) x)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hrepr : U x = Complex.exp ((alpha : ℂ) * Complex.I) • 1 +
      (Complex.exp ((beta : ℂ) * Complex.I) -
        Complex.exp ((alpha : ℂ) * Complex.I)) • P) :
    HasDerivAt (fun t => schattenUnitaryGradient p (U t))
      ((da : ℂ) • ((1 - P) * H * (1 - P)) + (db : ℂ) • (P * H * P)) x := by
  let a := Complex.exp ((alpha : ℂ) * Complex.I)
  let b := Complex.exp ((beta : ℂ) * Complex.I)
  change U x = a • 1 + (b - a) • P at hrepr
  have hfa : schattenPhaseExtension p a = (schattenPhaseDerivative p a : ℂ) :=
    schattenPhaseExtension_eq_of_norm_eq_one p a (Complex.norm_exp_ofReal_mul_I alpha)
  have hfb : schattenPhaseExtension p b = (schattenPhaseDerivative p a : ℂ) :=
    (schattenPhaseExtension_eq_of_norm_eq_one p b (Complex.norm_exp_ofReal_mul_I beta)).trans
      (congrArg Complex.ofReal hlevel.symm)
  have hd := hasDerivAt_cfc_unitary_tangent_of_affine_projection (schattenPhaseExtension p)
    a b (schattenPhaseDerivative p a : ℂ) (da : ℂ) (db : ℂ) hab hfa hfb (Metric.sphere (0 : ℂ) 1)
    (isCompact_sphere 0 1) (continuousOn_schattenPhaseExtension_circle p hp)
    (differentiableAt_schattenPhaseExtension p a (Complex.norm_exp_ofReal_mul_I alpha) hne_a)
    (differentiableAt_schattenPhaseExtension p b (Complex.norm_exp_ofReal_mul_I beta) hne_b)
    (schattenPhaseExtension_deriv_mul_I_exp p alpha da hne_a hda)
    (schattenPhaseExtension_deriv_mul_I_exp p beta db hne_b hdb)
    U x H hU (fun t => isStarNormal_of_mem_unitary (hunit t))
    (fun t => spectrum.subset_circle_of_unitary (hunit t)) P hP hrepr
  have hfun : (fun t => schattenUnitaryGradient p (U t)) =
      (fun t => cfc (schattenPhaseExtension p) (U t)) := by
    funext t
    exact schattenUnitaryGradient_eq_cfc_phaseExtension p ⟨U t, hunit t⟩
  rw [← hfun] at hd
  exact hd

variable [FiniteDimensional ℂ E]

/-- The actual Schatten displacement power has the two-compression
second variation at a nonidentity two-phase unitary with equal gradient
values. The squared compression norms are expressed by their finite traces. -/
theorem hasDerivAt_deriv_schatten_unitary_two_phase
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (alpha beta da db : ℝ)
    (hne_a : Complex.exp ((alpha : ℂ) * Complex.I) ≠ 1)
    (hne_b : Complex.exp ((beta : ℂ) * Complex.I) ≠ 1)
    (hab : Complex.exp ((alpha : ℂ) * Complex.I) ≠
      Complex.exp ((beta : ℂ) * Complex.I))
    (hlevel : schattenPhaseDerivative p.toReal (Complex.exp ((alpha : ℂ) * Complex.I)) =
      schattenPhaseDerivative p.toReal (Complex.exp ((beta : ℂ) * Complex.I)))
    (hda : HasDerivAt
      (fun t : ℝ => schattenPhaseDerivative p.toReal (Complex.exp ((t : ℂ) * Complex.I))) da alpha)
    (hdb : HasDerivAt
      (fun t : ℝ => schattenPhaseDerivative p.toReal (Complex.exp ((t : ℂ) * Complex.I))) db beta)
    (U : unitary (E →L[ℂ] E)) (H P : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P)
    (hrepr : (U : E →L[ℂ] E) = Complex.exp ((alpha : ℂ) * Complex.I) • 1 +
      (Complex.exp ((beta : ℂ) * Complex.I) -
        Complex.exp ((alpha : ℂ) * Complex.I)) • P) :
    let C := fun t : ℝ => UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - ((U : E →L[ℂ] E) *
        NormedSpace.exp (t • (Complex.I • H))).toLinearMap) ^ p.toReal
    HasDerivAt (deriv C)
      (da * (LinearMap.trace ℂ E
        (((1 - P) * H * (1 - P)).adjoint * ((1 - P) * H * (1 - P))).toLinearMap).re +
       db * (LinearMap.trace ℂ E ((P * H * P).adjoint * (P * H * P)).toLinearMap).re) 0 := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  let V : ℝ → E →L[ℂ] E := fun t =>
    (U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))
  let C := fun t : ℝ => UnitarilyInvariantSeminorm.schatten ℂ E E p
    (LinearMap.id - (V t).toLinearMap) ^ p.toReal
  let D : E →L[ℂ] E :=
    (da : ℂ) • ((1 - P) * H * (1 - P)) + (db : ℂ) • (P * H * P)
  have hunit (t : ℝ) : V t ∈ unitary (E →L[ℂ] E) := by
    apply mul_mem U.2
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  have hV0 : V 0 = (U : E →L[ℂ] E) := by simp only [V, zero_smul, NormedSpace.exp_zero, mul_one]
  have hV : HasDerivAt V (V 0 * (Complex.I • H)) 0 := by
    simpa only [V, zero_smul, NormedSpace.exp_zero, mul_one, one_mul] using
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • H) (0 : ℝ)).const_mul
        (U : E →L[ℂ] E)
  have hgrad : HasDerivAt (fun t => schattenUnitaryGradient p.toReal (V t)) D 0 :=
    hasDerivAt_schattenUnitaryGradient_two_phase p.toReal alpha beta da db hp1
      hne_a hne_b hab hlevel hda hdb V 0 H hunit hV P hP (hV0.trans hrepr)
  let tr : (E →L[ℂ] E) →L[ℝ] ℝ :=
    Complex.reCLM.comp ((traceCLM ℂ E).restrictScalars ℝ)
  have htr (T : E →L[ℂ] E) : tr T = (LinearMap.trace ℂ E T.toLinearMap).re := by
    simp only [tr, _root_.ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
    exact congrArg Complex.re (traceCLM_apply T)
  have hd := tr.hasFDerivAt.comp_hasDerivAt 0 (hgrad.mul_const H)
  have hderiv : deriv C = (fun t => tr (schattenUnitaryGradient p.toReal (V t) * H)) := by
    funext t
    rw [htr]
    exact (hasDerivAt_schatten_unitary_right_variation_at p hp hp1 U H hH t).deriv
  change HasDerivAt (fun t => tr (schattenUnitaryGradient p.toReal (V t) * H))
    (tr (D * H)) 0 at hd
  rw [← hderiv] at hd
  apply hd.congr_deriv
  have hcomplex : LinearMap.trace ℂ E (D * H).toLinearMap =
      (da : ℂ) * LinearMap.trace ℂ E
        (((1 - P) * H * (1 - P)).adjoint * ((1 - P) * H * (1 - P))).toLinearMap +
      (db : ℂ) * LinearMap.trace ℂ E ((P * H * P).adjoint * (P * H * P)).toLinearMap := by
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

end TauCeti
