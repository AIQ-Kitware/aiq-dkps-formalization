/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.ApproximationNumber.LeadingSingularFamilies
import DavisKahan.DoubleAngle.TanTwoThetaKyFan

/-!
# The canonical double-angle tangent operator

For a strict contraction `X : E0 -> E1`, define

`Tan2(X) = 2 X (I - X*X)^(-1)`.

The central reusable theorem identifies every approximation number of this
operator with the scalar transform `2t/(1-t^2)` of the corresponding
approximation number of `X`.  This removes the finite-dimensional surrogate
hypothesis used by the existing Ky Fan theorem.
-/

namespace TauCeti
namespace FinishTanTwoTheta

open scoped ENNReal

universe u v

/-- Scalar tangent of the doubled angle in graph coordinates. -/
def doubleAngleTangentScalar (t : ℝ) : ℝ :=
  2 * t / (1 - t ^ 2)

@[simp] theorem doubleAngleTangentScalar_zero :
    doubleAngleTangentScalar 0 = 0 := by
  simp [doubleAngleTangentScalar]

/-- Positivity on the quarter-acute interval. -/
theorem doubleAngleTangentScalar_nonneg {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ doubleAngleTangentScalar t := by
  unfold doubleAngleTangentScalar
  positivity

/-- Strict monotonicity on `[0,1)`. -/
theorem doubleAngleTangentScalar_strictMonoOn :
    StrictMonoOn doubleAngleTangentScalar (Set.Ico 0 1) := by
  /- Differentiate `2t/(1-t^2)`; its derivative is
  `2(1+t^2)/(1-t^2)^2 > 0` on this interval. -/
  sorry

/-- Uniform linear domination on `[0,r]`, used to control omitted small
approximation numbers. -/
theorem doubleAngleTangentScalar_le_mul {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht0 : 0 ≤ t) (htr : t ≤ r) :
    doubleAngleTangentScalar t ≤ (2 / (1 - r ^ 2)) * t := by
  unfold doubleAngleTangentScalar
  have hdenr : 0 < 1 - r ^ 2 := by nlinarith
  have hdent : 0 < 1 - t ^ 2 := by nlinarith
  apply (div_le_iff₀ hdent).2
  apply (le_div_iff₀ hdenr).2
  nlinarith

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E0 : Type v} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- The positive denominator `I - X*X`. -/
def doubleAngleDenominator (X : E0 →L[𝕜] E1) : E0 →L[𝕜] E0 :=
  ContinuousLinearMap.id 𝕜 E0 - X.adjoint ∘L X

/-- A strict contraction has invertible double-angle denominator. -/
theorem isUnit_doubleAngleDenominator (X : E0 →L[𝕜] E1)
    (hX : ‖X‖ < 1) : IsUnit (doubleAngleDenominator X) := by
  /- Neumann series: `||X*X|| <= ||X||^2 < 1`. -/
  sorry

/-- Canonical graph-coordinate tangent of twice the angle. -/
noncomputable def doubleAngleTangentOperator
    (X : E0 →L[𝕜] E1) (_hX : ‖X‖ < 1) : E0 →L[𝕜] E1 :=
  (2 : 𝕜) • (X ∘L Ring.inverse (doubleAngleDenominator X))

/-- Polar/functional-calculus form of the canonical tangent operator. -/
theorem doubleAngleTangentOperator_eq_polar_functionalCalculus
    (X : E0 →L[𝕜] E1) (hX : ‖X‖ < 1) :
    ∃ (U : E0 →L[𝕜] E1) (P : E0 →L[𝕜] E0),
      X = U ∘L P ∧
      doubleAngleTangentOperator X hX =
        U ∘L ((2 : 𝕜) • (P ∘L Ring.inverse
          (ContinuousLinearMap.id 𝕜 E0 - P ∘L P))) := by
  /- Take `P=|X|` and `U` the canonical polar partial isometry.  The support
  projection causes no difficulty because the scalar transform vanishes at
  zero. -/
  sorry

/-- **Approximation numbers under double-angle functional calculus.**
For every bounded strict contraction, including noncompact operators,
approximation numbers transform by the increasing scalar function
`2t/(1-t^2)`. -/
theorem approximationNumber_doubleAngleTangentOperator
    (X : E0 →L[𝕜] E1) (hX : ‖X‖ < 1) (n : ℕ) :
    (doubleAngleTangentOperator X hX).approximationNumber n =
      doubleAngleTangentScalar (X.approximationNumber n) := by
  /-
  Proof plan:
  * use polar decomposition to reduce to the positive modulus `|X|`;
  * identify approximation numbers with the min--max values of `|X|`;
  * apply the min--max functional-calculus theorem for the continuous strictly
    increasing function `f(t)=2t/(1-t^2)` on `[0,||X||]`;
  * use invariance under the polar partial isometry on the support.
  The min--max argument handles the essential-spectrum plateau and therefore
  does not require compactness or exact singular vectors.
  -/
  sorry

/-- Ky Fan prefixes of the canonical tangent operator are exactly the sums of
the transformed approximation numbers. -/
theorem approximationNumberPrefix_doubleAngleTangentOperator
    (X : E0 →L[𝕜] E1) (hX : ‖X‖ < 1) (k : ℕ) :
    approximationNumberPrefix k (doubleAngleTangentOperator X hX) =
      ∑ n ∈ Finset.range k,
        doubleAngleTangentScalar (X.approximationNumber n) := by
  simp [approximationNumberPrefix, sequencePrefixSum,
    approximationNumberSequence,
    approximationNumber_doubleAngleTangentOperator X hX]

end FinishTanTwoTheta
end TauCeti
