/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenSecondVariation
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenOverlapDirection
public import TauCeti.Analysis.Calculus.DerivativeTest
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSchatten

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

public section

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
  have hc := criticalAngle_mem p.toReal hp1 hp2
  have hap : a ∈ Ioo 0 Real.pi := ⟨ha.1, by linarith [ha.2, hc.2, Real.pi_pos]⟩
  have hbp : b ∈ Ioo 0 Real.pi := ⟨by linarith [hb.1, hc.1], hb.2⟩
  have hab : a ≠ b := (lt_trans ha.2 hb.1).ne
  have hX : IsSelfAdjoint X := isSelfAdjoint_projection_overlap hA.isSelfAdjoint hB.isSelfAdjoint
  have hcb : p.toReal * amplitudeDerivative p.toReal b < 0 := mul_neg_of_pos_of_neg (by linarith : 0 < p.toReal)
    (amplitudeDerivative_neg_of_criticalAngle_lt p.toReal b hp1 hp2 hb.1 hb.2)
  have hDU := balanced_phase_second_variation p hp hp1 a b hap hbp hab hbalance U X A hX hA hU
  have hDV := balanced_negative_phase_second_variation p hp hp1 a b hap hbp hab hbalance V X B hX hB hV
  exact exists_negative_second_variation_of_projection_overlap CU CV
    (fun t => (hasDerivAt_schatten_unitary_right_variation_at p hp hp1 U X hX t).differentiableAt)
    (fun t => (hasDerivAt_schatten_unitary_right_variation_at p hp hp1 V X hX t).differentiableAt)
    A B hA hB (p.toReal * amplitudeDerivative p.toReal a)
    (p.toReal * amplitudeDerivative p.toReal b)
    (p.toReal * amplitudeDerivative p.toReal a) (p.toReal * amplitudeDerivative p.toReal b)
    hcb hcb.le hDU hDV hAB

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
