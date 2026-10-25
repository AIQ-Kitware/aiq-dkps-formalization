/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedTwoPhaseVariation
public import ForTauCeti.Algebra.Star.ProjectionOverlap
public import TauCeti.Analysis.Calculus.DerivativeTest

/-!
# Overlap exclusion for paired Charbonnier-gradient blocks

For two actual blocks with opposite two-phase spectra, overlapping
negative-curvature phase projections give a decreasing second variation
of their coupled cost. The local-minimum conclusion concerns the stated
paired curve; extension to an arbitrary ambient constrained local minimum
requires identifying its reducing blocks and extending this direction.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Literal Charbonnier costs on two unitary blocks, varied by the same
Hermitian right direction. -/
@[expose] def pairedSmoothedCost (tau : ℝ) (U V : unitary (E →L[ℂ] E))
    (H : E →L[ℂ] E) (t : ℝ) : ℝ :=
  smoothedDisplacementCost tau ((U : E →L[ℂ] E) *
    NormedSpace.exp (t • (Complex.I • H))).toLinearMap +
  smoothedDisplacementCost tau ((V : E →L[ℂ] E) *
    NormedSpace.exp (t • (Complex.I • H))).toLinearMap

/-- Overlap of the negative-curvature projections forces a strictly
negative second derivative of the actual paired Charbonnier cost.
The balanced phases may include the identity and reflection endpoints. -/
theorem paired_phase_overlap_has_negative_second_variation
    (tau a b : ℝ) (htau : 0 < tau)
    (hab : Complex.exp ((a : ℂ) * Complex.I) ≠ Complex.exp ((b : ℂ) * Complex.I))
    (hbalance : smoothedPhaseDerivative tau (Complex.exp ((a : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((b : ℂ) * Complex.I)))
    (hnegative : Real.cos b < ((smoothingRadius tau)⁻¹) ^ 2)
    (U V : unitary (E →L[ℂ] E)) (A B : E →L[ℂ] E)
    (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hU : (U : E →L[ℂ] E) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A)
    (hV : (V : E →L[ℂ] E) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B)
    (hAB : A * B ≠ 0) :
    ∃ d < 0, HasDerivAt (deriv (pairedSmoothedCost tau U V (A * B + B * A))) d 0 := by
  let X := A * B + B * A
  let CU := fun t : ℝ => smoothedDisplacementCost tau
    ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • X))).toLinearMap
  let CV := fun t : ℝ => smoothedDisplacementCost tau
    ((V : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • X))).toLinearMap
  let TUA := (LinearMap.trace ℂ E ((A * X * A).adjoint * (A * X * A)).toLinearMap).re
  let TVB := (LinearMap.trace ℂ E ((B * X * B).adjoint * (B * X * B)).toLinearMap).re
  let cb := smoothedPhaseCurvature tau b
  have hX : IsSelfAdjoint X :=
    isSelfAdjoint_projection_overlap hA.isSelfAdjoint hB.isSelfAdjoint
  have hlowA : (1 - A) * X * (1 - A) = 0 :=
    projection_overlap_complement_compression hA.isIdempotentElem B
  have hlowB : (1 - B) * X * (1 - B) = 0 := by
    simpa only [X, add_comm] using
      projection_overlap_complement_compression hB.isIdempotentElem A
  have hhigh : A * X * A ≠ 0 := by
    change A * (A * B + B * A) * A ≠ 0
    rw [projection_overlap_compression hA.isIdempotentElem B]
    have hABA : A * B * A ≠ 0 := fun h =>
      hAB ((projection_compression_eq_zero_iff_mul_eq_zero hA hB).1 h)
    simpa only [two_nsmul, two_smul] using
      smul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hABA
  have hpos : 0 < TUA := (ContinuousLinearMap.re_trace_adjoint_mul_self_pos_iff _).2 hhigh
  have hnonneg : 0 ≤ TVB := ContinuousLinearMap.re_trace_adjoint_mul_self_nonneg _
  have hcb : cb < 0 := (smoothedPhaseCurvature_neg_iff tau b htau).2 hnegative
  have habneg : Complex.exp (((-a : ℝ) : ℂ) * Complex.I) ≠
      Complex.exp (((-b : ℝ) : ℂ) * Complex.I) := by
    simp only [Complex.ofReal_neg, neg_mul, Complex.exp_neg]
    exact fun h => hab (inv_injective h)
  have hbalneg : smoothedPhaseDerivative tau
        (Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp (((-b : ℝ) : ℂ) * Complex.I)) := by
    rw [smoothedPhaseDerivative_exp_neg, smoothedPhaseDerivative_exp_neg, hbalance]
  have hDU := hasDerivAt_deriv_smoothed_unitary_two_phase tau a b htau hab hbalance
    U X A hX hA hU
  have hDV := hasDerivAt_deriv_smoothed_unitary_two_phase tau (-a) (-b) htau habneg hbalneg
    V X B hX hB hV
  have hDU' : HasDerivAt (deriv CU) (cb * TUA) 0 := by
    simpa only [CU, cb, TUA, hlowA, map_zero, zero_mul,
      _root_.ContinuousLinearMap.toLinearMap_zero, Complex.zero_re, mul_zero, zero_add] using hDU
  have hDV' : HasDerivAt (deriv CV) (cb * TVB) 0 := by
    simpa only [CV, cb, TVB, smoothedPhaseCurvature_neg, hlowB, map_zero, zero_mul,
      _root_.ContinuousLinearMap.toLinearMap_zero, Complex.zero_re, mul_zero, zero_add] using hDV
  have hderiv : deriv (pairedSmoothedCost tau U V X) =
      (fun t => deriv CU t + deriv CV t) := by
    funext t
    exact deriv_add
      (hasDerivAt_smoothed_unitary_right_variation_at tau htau U X hX t).differentiableAt
      (hasDerivAt_smoothed_unitary_right_variation_at tau htau V X hX t).differentiableAt
  have hsum := hDU'.add hDV'
  change HasDerivAt (fun t => deriv CU t + deriv CV t) (cb * TUA + cb * TVB) 0 at hsum
  rw [← hderiv] at hsum
  exact ⟨cb * TUA + cb * TVB,
    add_neg_of_neg_of_nonpos (mul_neg_of_neg_of_pos hcb hpos)
      (mul_nonpos_of_nonpos_of_nonneg hcb.le hnonneg), hsum⟩

/-- A local minimum along the actual paired overlap curve has disjoint
negative-curvature phase projections. -/
theorem overlap_eq_zero_of_isLocalMin_paired_cost
    (tau a b : ℝ) (htau : 0 < tau)
    (hab : Complex.exp ((a : ℂ) * Complex.I) ≠ Complex.exp ((b : ℂ) * Complex.I))
    (hbalance : smoothedPhaseDerivative tau (Complex.exp ((a : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((b : ℂ) * Complex.I)))
    (hnegative : Real.cos b < ((smoothingRadius tau)⁻¹) ^ 2)
    (U V : unitary (E →L[ℂ] E)) (A B : E →L[ℂ] E)
    (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hU : (U : E →L[ℂ] E) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A)
    (hV : (V : E →L[ℂ] E) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B)
    (hmin : IsLocalMin (pairedSmoothedCost tau U V (A * B + B * A)) 0) : A * B = 0 := by
  by_contra hAB
  obtain ⟨d, hd, hsecond⟩ := paired_phase_overlap_has_negative_second_variation
    tau a b htau hab hbalance hnegative U V A B hA hB hU hV hAB
  have hX : IsSelfAdjoint (A * B + B * A) :=
    isSelfAdjoint_projection_overlap hA.isSelfAdjoint hB.isSelfAdjoint
  have hcont : ContinuousAt (pairedSmoothedCost tau U V (A * B + B * A)) 0 :=
    (hasDerivAt_smoothed_unitary_right_variation_at tau htau U _ hX 0).continuousAt.add
      (hasDerivAt_smoothed_unitary_right_variation_at tau htau V _ hX 0).continuousAt
  have hnonneg := TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hmin
  rw [hsecond.deriv] at hnonneg
  exact (not_lt_of_ge hnonneg) hd

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
