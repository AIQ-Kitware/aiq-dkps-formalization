/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedTwoPhaseVariation
public import TauCeti.Analysis.Calculus.DerivativeTest

/-!
# Ambient second-order restrictions on Charbonnier reflection minima

A constrained local minimum has nonnegative curvature along every
Hermitian direction commuting with the source operator. For an actual
reflection transporter this is an explicit inequality between the two
compressed Frobenius squares. Negative spectral subprojections commuting
with the source are excluded. No block decomposition is supplied.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every feasible Hermitian direction at an actual two-phase local
transport minimum satisfies the exact Hessian inequality. -/
theorem two_phase_second_variation_nonneg_of_isLocalMinOn_transports
    (tau alpha beta : ℝ) (htau : 0 < tau)
    (hab : Complex.exp ((alpha : ℂ) * Complex.I) ≠
      Complex.exp ((beta : ℂ) * Complex.I))
    (hlevel : smoothedPhaseDerivative tau (Complex.exp ((alpha : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((beta : ℂ) * Complex.I)))
    (P Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * P * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = Q}
      (U : E →L[ℂ] E))
    (A : E →L[ℂ] E) (hA : IsStarProjection A)
    (hrepr : (U : E →L[ℂ] E) = Complex.exp ((alpha : ℂ) * Complex.I) • 1 +
      (Complex.exp ((beta : ℂ) * Complex.I) -
        Complex.exp ((alpha : ℂ) * Complex.I)) • A)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (hHP : Commute H P) :
    0 ≤ smoothedPhaseCurvature tau alpha * (LinearMap.trace ℂ E
      (((1 - A) * H * (1 - A)).adjoint * ((1 - A) * H * (1 - A))).toLinearMap).re +
      smoothedPhaseCurvature tau beta *
        (LinearMap.trace ℂ E ((A * H * A).adjoint * (A * H * A)).toLinearMap).re := by
  have hcurve := isLocalMin_unitary_right_variation_of_isLocalMinOn_conjugacy
    (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
    P Q U htrans hmin H hH hHP
  have hcont := (hasDerivAt_smoothed_unitary_right_variation tau htau U H hH).continuousAt
  have hsecond := hasDerivAt_deriv_smoothed_unitary_two_phase tau alpha beta htau hab hlevel
    U H A hH hA hrepr
  have hn := TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hcurve
  rwa [hsecond.deriv] at hn

/-- At an actual reflecting local minimum, every feasible Hermitian
direction obeys the weighted compression inequality. In particular, the
positive identity curvature cannot be omitted from the reflection test. -/
theorem reflection_compression_bound_of_isLocalMinOn_transports
    (tau : ℝ) (htau : 0 < tau)
    (P Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * P * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = Q}
      (U : E →L[ℂ] E))
    (A : E →L[ℂ] E) (hA : IsStarProjection A)
    (hrepr : (U : E →L[ℂ] E) = 1 - (2 : ℂ) • A)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (hHP : Commute H P) :
    tau * (LinearMap.trace ℂ E ((A * H * A).adjoint * (A * H * A)).toLinearMap).re ≤
      Real.sqrt (tau ^ 2 + 4) * (LinearMap.trace ℂ E
        (((1 - A) * H * (1 - A)).adjoint * ((1 - A) * H * (1 - A))).toLinearMap).re := by
  have hz : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have hpi : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by
    rw [Complex.exp_ofReal_mul_I]
    simp
  have hab : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) ≠
      Complex.exp ((Real.pi : ℂ) * Complex.I) := by rw [hz, hpi]; norm_num
  have hlevel : smoothedPhaseDerivative tau (Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((Real.pi : ℂ) * Complex.I)) := by
    rw [smoothedPhaseDerivative_exp, smoothedPhaseDerivative_exp]
    simp
  have hrepr' : (U : E →L[ℂ] E) = Complex.exp (((0 : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp ((Real.pi : ℂ) * Complex.I) -
        Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) • A := by
    rw [hz, hpi, one_smul, show (-1 : ℂ) - 1 = -2 by norm_num, neg_smul]
    simpa only [sub_eq_add_neg] using hrepr
  have hn := two_phase_second_variation_nonneg_of_isLocalMinOn_transports
    tau 0 Real.pi htau hab hlevel P Q U htrans hmin A hA hrepr' H hH hHP
  rw [smoothedPhaseCurvature_zero tau htau, smoothedPhaseCurvature_pi] at hn
  let X := (LinearMap.trace ℂ E
    (((1 - A) * H * (1 - A)).adjoint * ((1 - A) * H * (1 - A))).toLinearMap).re
  let Y := (LinearMap.trace ℂ E ((A * H * A).adjoint * (A * H * A)).toLinearMap).re
  let r := Real.sqrt (tau ^ 2 + 4)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  change 0 ≤ tau⁻¹ * X + (-r⁻¹) * Y at hn
  change tau * Y ≤ r * X
  have hs := mul_nonneg (mul_nonneg htau.le hr.le) hn
  have heq : (tau * r) * (tau⁻¹ * X + (-r⁻¹) * Y) = r * X - tau * Y := by
    field_simp
    ring
  rw [heq] at hs
  linarith

/-- A feasible direction with zero compression to the positive reflection
space must also have zero compression to its negative space at a local
minimum. -/
theorem reflection_compression_eq_zero_of_isLocalMinOn_transports
    (tau : ℝ) (htau : 0 < tau)
    (P Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * P * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = Q}
      (U : E →L[ℂ] E))
    (A : E →L[ℂ] E) (hA : IsStarProjection A)
    (hrepr : (U : E →L[ℂ] E) = 1 - (2 : ℂ) • A)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (hHP : Commute H P)
    (hzero : (1 - A) * H * (1 - A) = 0) : A * H * A = 0 := by
  have h := reflection_compression_bound_of_isLocalMinOn_transports tau htau
    P Q U htrans hmin A hA hrepr H hH hHP
  simp only [hzero, map_zero, _root_.ContinuousLinearMap.toLinearMap_zero,
    Complex.zero_re, mul_zero] at h
  have hn := ContinuousLinearMap.re_trace_adjoint_mul_self_nonneg (A * H * A)
  have heq : (LinearMap.trace ℂ E ((A * H * A).adjoint * (A * H * A)).toLinearMap).re = 0 := by
    nlinarith
  exact ContinuousLinearMap.eq_zero_of_re_trace_adjoint_mul_self_eq_zero _ heq

/-- An actual reflection local minimum has no nonzero negative spectral
subprojection commuting with the source. The source and target operators
may be arbitrary; competitors range over the entire ambient unitary fiber. -/
theorem negative_subprojection_eq_zero_of_isLocalMinOn_reflection_transports
    (tau : ℝ) (htau : 0 < tau)
    (P Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * P * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = Q}
      (U : E →L[ℂ] E))
    (A : E →L[ℂ] E) (hA : IsStarProjection A)
    (hrepr : (U : E →L[ℂ] E) = 1 - (2 : ℂ) • A)
    (B : E →L[ℂ] E) (hB : IsStarProjection B)
    (hAB : A * B = B) (hBP : Commute B P) : B = 0 := by
  have hBA : B * A = B := by
    simpa only [star_mul, hA.isSelfAdjoint.star_eq, hB.isSelfAdjoint.star_eq] using
      congrArg star hAB
  have hzero : (1 - A) * B * (1 - A) = 0 := by
    rw [sub_mul, one_mul, hAB, sub_self, zero_mul]
  have hhigh : A * B * A = B := by rw [hAB, hBA]
  have h := reflection_compression_eq_zero_of_isLocalMinOn_transports tau htau
    P Q U htrans hmin A hA hrepr B hB.isSelfAdjoint hBP hzero
  rwa [hhigh] at h

omit [FiniteDimensional ℂ E] in
private theorem reflection_balancing_direction
    (P A : E →L[ℂ] E) (hP : IsStarProjection P) (hA : IsStarProjection A) :
    let H := P * A + A * P - A
    IsSelfAdjoint H ∧ Commute H P ∧ (1 - A) * H * (1 - A) = 0 ∧
      A * H * A = (2 : ℂ) • (A * P * A) - A := by
  let H := P * A + A * P - A
  have hH : IsSelfAdjoint H := by
    change star (P * A + A * P - A) = P * A + A * P - A
    simp only [star_sub, star_add, star_mul, hP.isSelfAdjoint.star_eq,
      hA.isSelfAdjoint.star_eq, add_comm]
  have hHP : Commute H P := by
    have hleft : P * H = P * A * P := by
      dsimp only [H]
      rw [mul_sub, mul_add, ← mul_assoc P P A, hP.isIdempotentElem.eq,
        ← mul_assoc P A P]
      abel
    have hright : H * P = P * A * P := by
      dsimp only [H]
      rw [sub_mul, add_mul, mul_assoc A P P, hP.isIdempotentElem.eq]
      abel
    exact hright.trans hleft.symm
  have hlow : (1 - A) * H * (1 - A) = 0 := by
    calc
      _ = (1 - A) * P * (A * (1 - A)) +
          ((1 - A) * A) * P * (1 - A) - ((1 - A) * A) * (1 - A) := by
        dsimp only [H]
        noncomm_ring
      _ = 0 := by
        rw [hA.isIdempotentElem.mul_one_sub_self, hA.isIdempotentElem.one_sub_mul_self]
        simp
  have hhigh : A * H * A = (2 : ℂ) • (A * P * A) - A := by
    calc
      _ = A * P * (A * A) + (A * A) * P * A - (A * A) * A := by
        dsimp only [H]
        noncomm_ring
      _ = _ := by simp only [hA.isIdempotentElem.eq, two_smul]
  exact ⟨hH, hHP, hlow, hhigh⟩

/-- At every actual reflecting local minimum, the negative eigenspace is
balanced across the source projection. The explicit feasible direction
`P*A+A*P-A` has zero positive-space compression, so the second-order test
forces `2*A*P*A=A` without choosing principal planes. -/
theorem reflection_balance_of_isLocalMinOn_transports_complex
    (tau : ℝ) (htau : 0 < tau)
    (P Q : E →L[ℂ] E) (hP : IsStarProjection P) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * P * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = Q}
      (U : E →L[ℂ] E))
    (A : E →L[ℂ] E) (hA : IsStarProjection A)
    (hrepr : (U : E →L[ℂ] E) = 1 - (2 : ℂ) • A) :
    (2 : ℂ) • (A * P * A) = A := by
  obtain ⟨hH, hHP, hlow, hhigh⟩ := reflection_balancing_direction P A hP hA
  let H := P * A + A * P - A
  have hz := reflection_compression_eq_zero_of_isLocalMinOn_transports tau htau
    P Q U htrans hmin A hA hrepr H hH hHP hlow
  rw [hhigh] at hz
  exact sub_eq_zero.mp hz

/-- Every unbalanced reflection has an explicit source-preserving
Hermitian direction with strictly negative actual second variation.
Thus it cannot be a constrained local minimum. -/
theorem reflection_balancing_direction_has_negative_second_variation_complex
    (tau : ℝ) (htau : 0 < tau)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (U : unitary (E →L[ℂ] E)) (A : E →L[ℂ] E) (hA : IsStarProjection A)
    (hrepr : (U : E →L[ℂ] E) = 1 - (2 : ℂ) • A)
    (hunbalanced : (2 : ℂ) • (A * P * A) ≠ A) :
    let H := P * A + A * P - A
    let D := (2 : ℂ) • (A * P * A) - A
    let d := -(Real.sqrt (tau ^ 2 + 4))⁻¹ *
      (LinearMap.trace ℂ E (D.adjoint * D).toLinearMap).re
    IsSelfAdjoint H ∧ Commute H P ∧ d < 0 ∧ HasDerivAt
        (deriv (fun t : ℝ => smoothedDisplacementCost tau
          ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))).toLinearMap)) d 0 := by
  let H := P * A + A * P - A
  let D := (2 : ℂ) • (A * P * A) - A
  obtain ⟨hH, hHP, hlow, hhigh⟩ := reflection_balancing_direction P A hP hA
  have hne : D ≠ 0 := sub_ne_zero.mpr hunbalanced
  have hpos := (ContinuousLinearMap.re_trace_adjoint_mul_self_pos_iff D).mpr hne
  have hcurv : -(Real.sqrt (tau ^ 2 + 4))⁻¹ < 0 := by
    apply neg_neg_of_pos
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hz : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have hpi : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  have hab : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) ≠
      Complex.exp ((Real.pi : ℂ) * Complex.I) := by rw [hz, hpi]; norm_num
  have hlevel : smoothedPhaseDerivative tau (Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((Real.pi : ℂ) * Complex.I)) := by
    rw [smoothedPhaseDerivative_exp, smoothedPhaseDerivative_exp]
    simp
  have hrepr' : (U : E →L[ℂ] E) = Complex.exp (((0 : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp ((Real.pi : ℂ) * Complex.I) -
        Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) • A := by
    rw [hz, hpi, one_smul, show (-1 : ℂ) - 1 = -2 by norm_num, neg_smul]
    simpa only [sub_eq_add_neg] using hrepr
  have hd := hasDerivAt_deriv_smoothed_unitary_two_phase tau 0 Real.pi htau hab hlevel
    U H A hH hA hrepr'
  change (1 - A) * H * (1 - A) = 0 at hlow
  change A * H * A = D at hhigh
  rw [hlow, hhigh] at hd
  refine ⟨hH, hHP, mul_neg_of_neg_of_pos hcurv hpos, ?_⟩
  simpa only [smoothedPhaseCurvature_pi, map_zero,
    _root_.ContinuousLinearMap.toLinearMap_zero, Complex.zero_re, mul_zero, zero_add] using hd

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
