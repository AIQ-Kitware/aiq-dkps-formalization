/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenSecondVariation
import DavisKahan.FiniteDimensional.DirectRotation.SchattenOverlapDirection
import TauCeti.Analysis.Calculus.DerivativeTest
import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSchatten

/-!
# Overlap exclusion for paired Schatten-gradient blocks

The two actual Schatten displacement powers are varied by the same Hermitian
direction. For balanced positive and negative phase roots, overlap of the
large-phase projections gives a strictly negative second variation under
`X = A * B + B * A`.

This is the coupled-block form of the no-mixing argument. Identifying its
sum with the cost of an ambient transporter, while extending the feasible
variation by zero on the remaining blocks, is a separate assembly step.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The sum of the actual displacement powers on two unitary blocks,
under a common right exponential variation. -/
def pairedSchattenCost (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (U V : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (t : ℝ) : ℝ :=
  UnitarilyInvariantSeminorm.schatten ℂ E E p
    (LinearMap.id - ((U : E →L[ℂ] E) *
      NormedSpace.exp (t • (Complex.I • H))).toLinearMap) ^ p.toReal +
  UnitarilyInvariantSeminorm.schatten ℂ E E p
    (LinearMap.id - ((V : E →L[ℂ] E) *
      NormedSpace.exp (t • (Complex.I • H))).toLinearMap) ^ p.toReal

/-- The coupled cost is the actual Schatten displacement power of the
orthogonal product curve. -/
theorem pairedSchattenCost_eq_block_displacement
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (U V : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (t : ℝ) :
    pairedSchattenCost p U V H t =
      UnitarilyInvariantSeminorm.schatten ℂ (WithLp 2 (E × E)) (WithLp 2 (E × E)) p
        (LinearMap.id -
          ((((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))).withLpProdMap 2
            ((V : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H)))).toLinearMap)) ^ p.toReal := by
  exact (schatten_displacement_rpow_withLpProdMap _ _ p hp).symm

/-- Overlapping large-phase projections force a strictly negative
second derivative of the actual coupled Schatten cost. -/
theorem paired_phase_overlap_has_negative_second_variation
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (a b : ℝ) (ha : a ∈ Ioo 0 (criticalAngle p.toReal))
    (hb : b ∈ Ioo (criticalAngle p.toReal) Real.pi)
    (hbalance : phaseAmplitude p.toReal a = phaseAmplitude p.toReal b)
    (U V : unitary (E →L[ℂ] E)) (A B : E →L[ℂ] E)
    (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hU : (U : E →L[ℂ] E) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A)
    (hV : (V : E →L[ℂ] E) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B)
    (hAB : A * B ≠ 0) :
    ∃ d < 0, HasDerivAt (deriv (pairedSchattenCost p U V (A * B + B * A))) d 0 := by
  let X := A * B + B * A
  let CU := fun t : ℝ => UnitarilyInvariantSeminorm.schatten ℂ E E p
    (LinearMap.id - ((U : E →L[ℂ] E) *
      NormedSpace.exp (t • (Complex.I • X))).toLinearMap) ^ p.toReal
  let CV := fun t : ℝ => UnitarilyInvariantSeminorm.schatten ℂ E E p
    (LinearMap.id - ((V : E →L[ℂ] E) *
      NormedSpace.exp (t • (Complex.I • X))).toLinearMap) ^ p.toReal
  let TUA := (LinearMap.trace ℂ E ((A * X * A).adjoint * (A * X * A)).toLinearMap).re
  let TVB := (LinearMap.trace ℂ E ((B * X * B).adjoint * (B * X * B)).toLinearMap).re
  let cb := p.toReal * amplitudeDerivative p.toReal b
  have hc := criticalAngle_mem p.toReal hp1 hp2
  have hap : a ∈ Ioo 0 Real.pi := ⟨ha.1, by linarith [ha.2, hc.2, Real.pi_pos]⟩
  have hbp : b ∈ Ioo 0 Real.pi := ⟨by linarith [hb.1, hc.1], hb.2⟩
  have hab : a ≠ b := (lt_trans ha.2 hb.1).ne
  have hX : IsSelfAdjoint X := isSelfAdjoint_projection_overlap hA.isSelfAdjoint hB.isSelfAdjoint
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
  have hcb : cb < 0 := mul_neg_of_pos_of_neg (by linarith : 0 < p.toReal)
    (amplitudeDerivative_neg_of_criticalAngle_lt p.toReal b hp1 hp2 hb.1 hb.2)
  have hDU := balanced_phase_second_variation p hp hp1 a b hap hbp hab hbalance U X A hX hA hU
  have hDV := balanced_negative_phase_second_variation p hp hp1 a b hap hbp hab hbalance V X B hX hB hV
  have hDU' : HasDerivAt (deriv CU) (cb * TUA) 0 := by
    simpa only [CU, cb, TUA, hlowA, map_zero, zero_mul,
      _root_.ContinuousLinearMap.toLinearMap_zero, Complex.zero_re, mul_zero, zero_add] using hDU
  have hDV' : HasDerivAt (deriv CV) (cb * TVB) 0 := by
    simpa only [CV, cb, TVB, hlowB, map_zero, zero_mul,
      _root_.ContinuousLinearMap.toLinearMap_zero, Complex.zero_re, mul_zero, zero_add] using hDV
  have hderiv : deriv (pairedSchattenCost p U V X) =
      (fun t => deriv CU t + deriv CV t) := by
    funext t
    exact deriv_add
      (hasDerivAt_schatten_unitary_right_variation_at p hp hp1 U X hX t).differentiableAt
      (hasDerivAt_schatten_unitary_right_variation_at p hp hp1 V X hX t).differentiableAt
  have hsum := hDU'.add hDV'
  change HasDerivAt (fun t => deriv CU t + deriv CV t) (cb * TUA + cb * TVB) 0 at hsum
  rw [← hderiv] at hsum
  exact ⟨cb * TUA + cb * TVB,
    add_neg_of_neg_of_nonpos (mul_neg_of_neg_of_pos hcb hpos)
      (mul_nonpos_of_nonpos_of_nonneg hcb.le hnonneg), hsum⟩

/-- A local minimum of the actual coupled block cost has orthogonal
large-phase subspaces. The necessary second-derivative test is consumed
from the accepted Tau Ceti calculus API. -/
theorem overlap_eq_zero_of_isLocalMin_paired_cost
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (a b : ℝ) (ha : a ∈ Ioo 0 (criticalAngle p.toReal))
    (hb : b ∈ Ioo (criticalAngle p.toReal) Real.pi)
    (hbalance : phaseAmplitude p.toReal a = phaseAmplitude p.toReal b)
    (U V : unitary (E →L[ℂ] E)) (A B : E →L[ℂ] E)
    (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hU : (U : E →L[ℂ] E) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A)
    (hV : (V : E →L[ℂ] E) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B)
    (hmin : IsLocalMin (pairedSchattenCost p U V (A * B + B * A)) 0) : A * B = 0 := by
  by_contra hAB
  obtain ⟨d, hd, hsecond⟩ := paired_phase_overlap_has_negative_second_variation
    p hp hp1 hp2 a b ha hb hbalance U V A B hA hB hU hV hAB
  have hX : IsSelfAdjoint (A * B + B * A) :=
    isSelfAdjoint_projection_overlap hA.isSelfAdjoint hB.isSelfAdjoint
  have hcont : ContinuousAt (pairedSchattenCost p U V (A * B + B * A)) 0 :=
    (hasDerivAt_schatten_unitary_right_variation_at p hp hp1 U (A * B + B * A) hX 0).continuousAt.add
      (hasDerivAt_schatten_unitary_right_variation_at p hp hp1 V (A * B + B * A) hX 0).continuousAt
  have hnonneg := TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hmin
  rw [hsecond.deriv] at hnonneg
  exact (not_lt_of_ge hnonneg) hd

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
