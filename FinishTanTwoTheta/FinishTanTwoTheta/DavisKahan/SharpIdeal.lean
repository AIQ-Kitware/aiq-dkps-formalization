/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.GroundedImports
import FinishTanTwoTheta.DavisKahan.SharpKyFan
import FinishTanTwoTheta.OperatorIdeal.StandardFanDominance

/-!
# Sharp standard-ideal `tan 2Theta`

Fan dominance is now applied as a theorem.  For both maximal and minimal
standard completions the clean common statement places the positive scalar
`d/2` on the tangent operator.  The maximal/Fatou specialization is then
unscaled using the repository's existing real-gauge theorem.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

open scoped InnerProductSpace
open DavisKahanExt
open Experimental.ExactSinTheta

noncomputable section

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Sharp endpoint for every standard symmetric completion, formulated in the
scale-invariant common form. -/
theorem sharp_standardSymmetricIdeal_scaled
    (I : TauCeti.FinishTanTwoTheta.StandardSymmetricIdeal)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : I.Mem B.B01) :
    I.Mem (((d / 2 : ℝ) : ℂ) •
        TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ∧
      I.gauge (((d / 2 : ℝ) : ℂ) •
          TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
        I.gauge B.B01 := by
  apply TauCeti.FinishTanTwoTheta.standard_fanDominance I hB
  intro k
  rw [kyFanApproximationGauge_smul,
    RCLike.norm_ofReal, abs_of_nonneg (by positivity : 0 ≤ d / 2)]
  have hsharp := sharp_doubleAngleTangentOperator_kyFan
    B hd.le hA0 hA1 hX hcontractive k
  nlinarith

/-- Maximal/Fatou source-norm endpoint in the paper's conventional scaling. -/
theorem sharp_paperUnitaryInvariantNorm
    (N : PaperUnitaryInvariantNorm)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : N.Mem B.B01) :
    N.Mem (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ∧
      d * N.gauge
          (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
        2 * N.gauge B.B01 := by
  have hfan : ∀ k : ℕ,
      (d / 2) * kyFanApproximationGauge k
          (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
        kyFanApproximationGauge k B.B01 := by
    intro k
    have hsharp := sharp_doubleAngleTangentOperator_kyFan
      B hd.le hA0 hA1 hX hcontractive k
    nlinarith
  have h := N.mul_gauge_le_of_all_mul_kyFan_le
    (c := d / 2) (by positivity) hB hfan
  refine ⟨h.1, ?_⟩
  nlinarith [h.2]

/-- Schatten-`p` maximal ideal endpoint for every `1 ≤ p`. -/
theorem sharp_schattenMaximal
    (p : ℝ) (hp : 1 ≤ p)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : (TauCeti.FinishTanTwoTheta.paperLpNorm p hp).Mem B.B01) :
    (TauCeti.FinishTanTwoTheta.paperLpNorm p hp).Mem
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ∧
      d * (TauCeti.FinishTanTwoTheta.paperLpNorm p hp).gauge
          (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
        2 * (TauCeti.FinishTanTwoTheta.paperLpNorm p hp).gauge B.B01 :=
  sharp_paperUnitaryInvariantNorm
    (TauCeti.FinishTanTwoTheta.paperLpNorm p hp)
    B hd hA0 hA1 hX hcontractive hB

/-- Trace/nuclear specialization. -/
theorem sharp_nuclear
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : paperNuclearNorm.Mem B.B01) :
    paperNuclearNorm.Mem
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ∧
      d * paperNuclearNorm.gauge
          (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
        2 * paperNuclearNorm.gauge B.B01 :=
  sharp_paperUnitaryInvariantNorm paperNuclearNorm
    B hd hA0 hA1 hX hcontractive hB

end

end FinishTanTwoTheta
end DavisKahan
end TauCeti
