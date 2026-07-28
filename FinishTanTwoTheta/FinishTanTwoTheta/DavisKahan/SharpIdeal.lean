/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.DavisKahan.SharpKyFan
import FinishTanTwoTheta.OperatorIdeal.StandardInstances

/-!
# Sharp `tan 2 Theta` in every standard symmetric ideal

The Ky Fan root implies weak submajorization of the scaled tangent operator by
the off-diagonal perturbation block.  General Fan dominance then gives
membership and the sharp ideal-gauge inequality for every standard symmetric
ideal.  No dominance theorem is assumed as a field.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

open scoped InnerProductSpace ENNReal
open DavisKahanExt DavisKahanTheory

universe u v

variable {E0 : Type v} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The scaled tangent operator is weakly submajorized by the perturbation
block.  This is the exact normalization that avoids division in `ℝ≥0∞`. -/
theorem scaled_doubleAngleTangent_prefix_le
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) (k : ℕ) :
    TauCeti.FinishTanTwoTheta.approximationNumberPrefix k
        (((d / 2 : ℝ) : ℂ) •
          TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
      TauCeti.FinishTanTwoTheta.approximationNumberPrefix k B.B01 := by
  have hsharp := sharp_doubleAngleTangentOperator_prefix
    B hd hA0 hA1 hX hcontractive k
  have hscale :
      TauCeti.FinishTanTwoTheta.approximationNumberPrefix k
        (((d / 2 : ℝ) : ℂ) •
          TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) =
      (d / 2) * TauCeti.FinishTanTwoTheta.approximationNumberPrefix k
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) := by
    simp [TauCeti.FinishTanTwoTheta.approximationNumberPrefix,
      TauCeti.FinishTanTwoTheta.sequencePrefixSum,
      TauCeti.FinishTanTwoTheta.approximationNumberSequence,
      Finset.mul_sum, abs_of_pos hd]
  rw [hscale]
  nlinarith

/-- **Fan-dominance endpoint for every standard symmetric ideal.** -/
theorem sharp_standardIdeal
    (N : TauCeti.FinishTanTwoTheta.StandardSymmetricIdealFamily.{0, v} ℂ)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hBmem : B.B01 ∈
      N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.carrier) :
    (((d / 2 : ℝ) : ℂ) •
        TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ∈
        N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.carrier ∧
      N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge
          (((d / 2 : ℝ) : ℂ) •
            TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
        N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge B.B01 := by
  apply N.fanDominance
  · exact hBmem
  · intro k
    exact scaled_doubleAngleTangent_prefix_le
      B hd hA0 hA1 hX hcontractive k

/-- Unscaled real-valued ideal-norm form for members. -/
theorem sharp_standardIdeal_toReal
    (N : TauCeti.FinishTanTwoTheta.StandardSymmetricIdealFamily.{0, v} ℂ)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hBmem : B.B01 ∈
      N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.carrier) :
    TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive ∈
        N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.carrier ∧
      d * (N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge
          (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive)).toReal ≤
        2 * (N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge
          B.B01).toReal := by
  exact unscale_positive_gauge_inequality
    (N := N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily)
    (c := d / 2) hd
    (sharp_standardIdeal N B hd hA0 hA1 hX hcontractive hBmem)


/-- Sharp operator-norm specialization. -/
theorem sharp_operatorNorm
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) :
    d * ‖TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive‖ ≤
      2 * ‖B.B01‖ := by
  have h := sharp_doubleAngleTangentOperator_prefix
    B hd hA0 hA1 hX hcontractive 1
  simpa [TauCeti.FinishTanTwoTheta.approximationNumberPrefix,
    TauCeti.FinishTanTwoTheta.sequencePrefixSum,
    TauCeti.FinishTanTwoTheta.approximationNumberSequence] using h

/-- Sharp fixed finite Ky Fan specialization. -/
theorem sharp_fixedKyFan
    (q : ℕ)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) :
    d * TauCeti.FinishTanTwoTheta.approximationNumberPrefix q
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
      2 * TauCeti.FinishTanTwoTheta.approximationNumberPrefix q B.B01 :=
  sharp_doubleAngleTangentOperator_prefix
    B hd hA0 hA1 hX hcontractive q

/-- Compact-operator-norm endpoint: compactness of the coupling block implies
compactness of the canonical tangent operator, with the sharp norm bound. -/
theorem sharp_compactOperatorNorm
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hcompact : B.B01 ∈
      (TauCeti.FinishTanTwoTheta.compactOperatorNormFamily
        (v := v) ℂ).toOperatorIdealFamily.carrier) :
    TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive ∈
        (TauCeti.FinishTanTwoTheta.compactOperatorNormFamily
          (v := v) ℂ).toOperatorIdealFamily.carrier ∧
      d * ‖TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive‖ ≤
        2 * ‖B.B01‖ := by
  have h := sharp_standardIdeal_toReal
    (TauCeti.FinishTanTwoTheta.standardCompactOperatorNormFamily
      (v := v) ℂ) B hd hA0 hA1 hX hcontractive hcompact
  simpa [TauCeti.FinishTanTwoTheta.standardCompactOperatorNormFamily,
    TauCeti.FinishTanTwoTheta.compactOperatorNormFamily,
    TauCeti.FinishTanTwoTheta.generatedIdealGauge,
    TauCeti.FinishTanTwoTheta.linfty_sequenceGauge_approximationNumbers_eq_enorm]
    using h

/-- Sharp Schatten-`p` specialization for every `p >= 1`. -/
theorem sharp_schatten
    (p : ℝ) (hp : 1 ≤ p)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : TauCeti.FinishTanTwoTheta.IsSchatten p hp B.B01) :
    TauCeti.FinishTanTwoTheta.IsSchatten p hp
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ∧
      d * (TauCeti.FinishTanTwoTheta.schattenGauge p hp
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive)).toReal ≤
      2 * (TauCeti.FinishTanTwoTheta.schattenGauge p hp B.B01).toReal := by
  simpa [TauCeti.FinishTanTwoTheta.IsSchatten,
    TauCeti.FinishTanTwoTheta.schattenGauge,
    TauCeti.FinishTanTwoTheta.standardSchattenIdealFamily,
    TauCeti.FinishTanTwoTheta.schattenIdealFamily] using
    sharp_standardIdeal_toReal
      (TauCeti.FinishTanTwoTheta.standardSchattenIdealFamily
        (v := v) ℂ p hp)
      B hd hA0 hA1 hX hcontractive hB

end FinishTanTwoTheta
end DavisKahan
end TauCeti
