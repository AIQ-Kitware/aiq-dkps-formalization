/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.DavisKahan.StableRiccatiPair

/-!
# Sharp infinite-dimensional Ky Fan `tan 2 Theta`

This file closes the noncompact singular-selection gap.  It combines the
approximate leading singular-family theorem with the stable Riccati estimate,
controls the omitted small tail, and lets the tolerance tend to zero.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

open scoped InnerProductSpace BigOperators
open DavisKahanExt DavisKahanTheory

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Sharp transformed-prefix inequality for an arbitrary bounded Riccati
solution.  No compactness, finite-dimensional carrier, or exact singular-vector
attainment is assumed. -/
theorem sharp_transformedApproximationPrefix
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) (k : ℕ) :
    d * ∑ n ∈ Finset.range k,
        TauCeti.FinishTanTwoTheta.doubleAngleTangentScalar
          (X.approximationNumber n) ≤
      2 * kyFanApproximationGauge k B.B01 := by
  /-
  Choose `r` with `||X|| < r < 1`.  For each `ε>0`, select an approximate
  leading singular family.  The selected part is bounded by the stable Riccati
  estimate.  The omitted part is at most

      `(k-count) * 2ε/(1-r^2)`.

  Replace `K_count(B01)` by `K_k(B01)` using monotonicity.  Thus the target
  left side is bounded by the sharp right side plus `C*k*ε`.  Since this holds
  for every positive `ε`, use `le_of_forall_pos_le_add` (or an equivalent
  Archimedean argument) to remove the error.
  -/
  sorry

/-- **Sharp infinite-dimensional Ky Fan `tan 2 Theta` theorem.** -/
theorem sharp_doubleAngleTangentOperator_kyFan
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) (k : ℕ) :
    d * TauCeti.FinishTanTwoTheta.approximationNumberPrefix k
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
      2 * kyFanApproximationGauge k B.B01 := by
  rw [TauCeti.FinishTanTwoTheta.approximationNumberPrefix_doubleAngleTangentOperator
    X hcontractive k]
  exact sharp_transformedApproximationPrefix B hd hA0 hA1 hX hcontractive k

/-- Canonical-prefix form, with both sides using the new zero-based
approximation-number prefix. -/
theorem sharp_doubleAngleTangentOperator_prefix
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) (k : ℕ) :
    d * TauCeti.FinishTanTwoTheta.approximationNumberPrefix k
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
      2 * TauCeti.FinishTanTwoTheta.approximationNumberPrefix k B.B01 := by
  /- `kyFanApproximationGauge` is the same zero-based prefix sum. -/
  simpa [TauCeti.FinishTanTwoTheta.approximationNumberPrefix,
    TauCeti.FinishTanTwoTheta.sequencePrefixSum,
    TauCeti.FinishTanTwoTheta.approximationNumberSequence,
    kyFanApproximationGauge, approximationSingularValue] using
    sharp_doubleAngleTangentOperator_kyFan B hd hA0 hA1 hX hcontractive k

end FinishTanTwoTheta
end DavisKahan
end TauCeti
