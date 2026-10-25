/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientSpectrum
public import ForTauCeti.Analysis.InnerProductSpace.SchattenTwoPhaseVariation

/-!
# The actual Schatten second variation at balanced phase roots

The scalar amplitude derivatives instantiate the operator two-phase
Hessian. This is the analytic identity used before choosing the projection
overlap direction; it does not yet assemble the opposite blocks into an
ambient feasible descent.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal

private theorem re_exp_phase (t : ℝ) :
    (Complex.exp ((t : ℂ) * Complex.I)).re = Real.cos t := by
  rw [Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]

private theorem exp_phase_ne_one (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
    Complex.exp ((t : ℂ) * Complex.I) ≠ 1 := by
  have hcos : Real.cos t < 1 := by
    simpa only [Real.cos_zero] using Real.strictAntiOn_cos
      ⟨le_rfl, Real.pi_pos.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
  intro h
  have hre := congrArg Complex.re h
  rw [re_exp_phase, Complex.one_re] at hre
  exact hcos.ne hre

private theorem exp_phase_injective_positive
    (a b : ℝ) (ha : a ∈ Ioo 0 Real.pi) (hb : b ∈ Ioo 0 Real.pi) (hab : a ≠ b) :
    Complex.exp ((a : ℂ) * Complex.I) ≠ Complex.exp ((b : ℂ) * Complex.I) := by
  intro h
  have hre := congrArg Complex.re h
  rw [re_exp_phase, re_exp_phase] at hre
  exact hab (Real.strictAntiOn_cos.injOn ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ hre)

private theorem exp_neg_phase (t : ℝ) :
    Complex.exp (((-t : ℝ) : ℂ) * Complex.I) =
      (Complex.exp ((t : ℂ) * Complex.I))⁻¹ := by
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Balanced positive roots give the exact second derivative of the
actual Schatten displacement power, with their explicit amplitude curvatures. -/
theorem balanced_phase_second_variation
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (a b : ℝ) (ha : a ∈ Ioo 0 Real.pi) (hb : b ∈ Ioo 0 Real.pi) (hab : a ≠ b)
    (hbalance : phaseAmplitude p.toReal a = phaseAmplitude p.toReal b)
    (U : unitary (E →L[ℂ] E)) (H P : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P)
    (hrepr : (U : E →L[ℂ] E) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
      (Complex.exp ((b : ℂ) * Complex.I) -
        Complex.exp ((a : ℂ) * Complex.I)) • P) :
    let C := fun t : ℝ => UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - ((U : E →L[ℂ] E) *
        NormedSpace.exp (t • (Complex.I • H))).toLinearMap) ^ p.toReal
    HasDerivAt (deriv C)
      ((p.toReal * amplitudeDerivative p.toReal a) * (LinearMap.trace ℂ E
        (((1 - P) * H * (1 - P)).adjoint * ((1 - P) * H * (1 - P))).toLinearMap).re +
       (p.toReal * amplitudeDerivative p.toReal b) *
        (LinearMap.trace ℂ E ((P * H * P).adjoint * (P * H * P)).toLinearMap).re) 0 := by
  have hlevel : schattenPhaseDerivative p.toReal (Complex.exp ((a : ℂ) * Complex.I)) =
      schattenPhaseDerivative p.toReal (Complex.exp ((b : ℂ) * Complex.I)) := by
    rw [schattenPhaseDerivative_exp_eq_amplitude p.toReal a ha,
      schattenPhaseDerivative_exp_eq_amplitude p.toReal b hb, hbalance]
  exact hasDerivAt_deriv_schatten_unitary_two_phase p hp hp1 a b
    (p.toReal * amplitudeDerivative p.toReal a) (p.toReal * amplitudeDerivative p.toReal b)
    (exp_phase_ne_one a ha) (exp_phase_ne_one b hb)
    (exp_phase_injective_positive a b ha hb hab) hlevel
    (schattenPhaseDerivative_exp_hasDerivAt p.toReal a ha)
    (schattenPhaseDerivative_exp_hasDerivAt p.toReal b hb) U H P hH hP hrepr

/-- The opposite negative phase roots have the same scalar curvatures
and the same two-compression second-variation formula. -/
theorem balanced_negative_phase_second_variation
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (a b : ℝ) (ha : a ∈ Ioo 0 Real.pi) (hb : b ∈ Ioo 0 Real.pi) (hab : a ≠ b)
    (hbalance : phaseAmplitude p.toReal a = phaseAmplitude p.toReal b)
    (U : unitary (E →L[ℂ] E)) (H P : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P)
    (hrepr : (U : E →L[ℂ] E) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • P) :
    let C := fun t : ℝ => UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - ((U : E →L[ℂ] E) *
        NormedSpace.exp (t • (Complex.I • H))).toLinearMap) ^ p.toReal
    HasDerivAt (deriv C)
      ((p.toReal * amplitudeDerivative p.toReal a) * (LinearMap.trace ℂ E
        (((1 - P) * H * (1 - P)).adjoint * ((1 - P) * H * (1 - P))).toLinearMap).re +
       (p.toReal * amplitudeDerivative p.toReal b) *
        (LinearMap.trace ℂ E ((P * H * P).adjoint * (P * H * P)).toLinearMap).re) 0 := by
  have hne_a : Complex.exp (((-a : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    rw [exp_neg_phase]
    intro h
    apply exp_phase_ne_one a ha
    simpa only [inv_inv, inv_one] using congrArg (Inv.inv : ℂ → ℂ) h
  have hne_b : Complex.exp (((-b : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    rw [exp_neg_phase]
    intro h
    apply exp_phase_ne_one b hb
    simpa only [inv_inv, inv_one] using congrArg (Inv.inv : ℂ → ℂ) h
  have hne : Complex.exp (((-a : ℝ) : ℂ) * Complex.I) ≠
      Complex.exp (((-b : ℝ) : ℂ) * Complex.I) := by
    rw [exp_neg_phase, exp_neg_phase]
    exact fun h => exp_phase_injective_positive a b ha hb hab (inv_injective h)
  have hlevel : schattenPhaseDerivative p.toReal (Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) =
      schattenPhaseDerivative p.toReal (Complex.exp (((-b : ℝ) : ℂ) * Complex.I)) := by
    rw [schattenPhaseDerivative_exp_neg, schattenPhaseDerivative_exp_neg,
      schattenPhaseDerivative_exp_eq_amplitude p.toReal a ha,
      schattenPhaseDerivative_exp_eq_amplitude p.toReal b hb, hbalance]
  exact hasDerivAt_deriv_schatten_unitary_two_phase p hp hp1 (-a) (-b)
    (p.toReal * amplitudeDerivative p.toReal a) (p.toReal * amplitudeDerivative p.toReal b)
    hne_a hne_b hne hlevel
    (hasDerivAt_schattenPhaseDerivative_exp_neg p.toReal a _
      (schattenPhaseDerivative_exp_hasDerivAt p.toReal a ha))
    (hasDerivAt_schattenPhaseDerivative_exp_neg p.toReal b _
      (schattenPhaseDerivative_exp_hasDerivAt p.toReal b hb)) U H P hH hP hrepr

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
