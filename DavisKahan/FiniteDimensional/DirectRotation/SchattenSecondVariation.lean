/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientSpectrum
import ForTauCeti.Analysis.InnerProductSpace.SchattenTwoPhaseVariation

/-!
# The actual Schatten second variation at balanced phase roots

The scalar amplitude derivatives instantiate the operator two-phase
Hessian. This is the analytic identity used before choosing the projection
overlap direction; it does not yet assemble the opposite blocks into an
ambient feasible descent.
-/

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

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
