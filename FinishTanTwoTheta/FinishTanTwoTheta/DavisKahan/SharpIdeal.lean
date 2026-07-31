/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SharpKyFan
import DavisKahan.Sources.DavisKahan1970.Ideals.StandardFanDominance

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

universe u

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type u} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The sharp Ky Fan estimate in the orientation needed by Fan dominance. -/
private theorem half_mul_kyFan_le_adjoint
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) (k : ℕ) :
    (d / 2) * kyFanApproximationGauge k
        (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
      kyFanApproximationGauge k B.B01.adjoint := by
  have hsharp := sharp_doubleAngleTangentOperator_kyFan
    B hd.le hA0 hA1 hX hcontractive k
  rw [kyFanApproximationGauge_adjoint]
  calc
    (d / 2) * kyFanApproximationGauge k
        (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) =
        (d * kyFanApproximationGauge k
          (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive)) / 2 := by
      ring
    _ ≤ kyFanApproximationGauge k B.B01 := by
      linarith

/-- Sharp endpoint for every standard symmetric completion, formulated in the
scale-invariant common form. -/
theorem sharp_standardSymmetricIdeal_scaled
    (I : TauCeti.SymmetricIdeal.StandardSymmetricIdeal)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : I.Mem B.B01) :
    I.Mem (((d / 2 : ℝ) : ℂ) •
        TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ∧
      I.gauge (((d / 2 : ℝ) : ℂ) •
          TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
        I.gauge B.B01 := by
  let T : E0 →L[ℂ] E1 :=
    TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive
  let S : E0 →L[ℂ] E1 := (((d / 2 : ℝ) : ℂ) • T)
  have hBadj : I.Mem B.B01.adjoint := I.mem_adjoint hB
  have hscalarNorm : ‖(((d / 2 : ℝ) : ℂ))‖ = d / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ d / 2)]
  have hdom : ∀ k : ℕ,
      kyFanApproximationGauge k S ≤
        kyFanApproximationGauge k B.B01.adjoint := by
    intro k
    simpa only [S, T, kyFanApproximationGauge_smul, hscalarNorm] using
      half_mul_kyFan_le_adjoint B hd hA0 hA1 hX hcontractive k
  have hfan : I.Mem S ∧ I.gauge S ≤ I.gauge B.B01.adjoint :=
    TauCeti.SymmetricIdeal.standard_fanDominance I hBadj hdom
  change I.Mem S ∧ I.gauge S ≤ I.gauge B.B01
  refine ⟨hfan.1, ?_⟩
  calc
    I.gauge S ≤ I.gauge B.B01.adjoint := hfan.2
    _ = I.gauge B.B01 := I.gauge_adjoint B.B01

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
    N.Mem (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ∧
      d * N.gauge
          (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
        2 * N.gauge B.B01 := by
  let T : E0 →L[ℂ] E1 :=
    TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive
  have hBadj : N.Mem B.B01.adjoint :=
    (N.mem_adjoint_iff B.B01).mpr hB
  have hfan : ∀ k : ℕ,
      (d / 2) * kyFanApproximationGauge k T ≤
        kyFanApproximationGauge k B.B01.adjoint := by
    intro k
    exact half_mul_kyFan_le_adjoint B hd hA0 hA1 hX hcontractive k
  have h : N.Mem T ∧ (d / 2) * N.gauge T ≤ N.gauge B.B01.adjoint :=
    N.mul_gauge_le_of_all_mul_kyFan_le
      (A := T) (B := B.B01.adjoint) (c := d / 2)
      (by positivity) hBadj hfan
  change N.Mem T ∧ d * N.gauge T ≤ 2 * N.gauge B.B01
  refine ⟨h.1, ?_⟩
  calc
    d * N.gauge T = 2 * ((d / 2) * N.gauge T) := by ring
    _ ≤ 2 * N.gauge B.B01.adjoint :=
      mul_le_mul_of_nonneg_left h.2 (by norm_num)
    _ = 2 * N.gauge B.B01 := by
      rw [N.gauge_adjoint]

/-- Schatten-`p` maximal ideal endpoint for every `1 ≤ p`. -/
theorem sharp_schattenMaximal
    (p : ℝ) (hp : 1 ≤ p)
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1)
    (hB : (TauCeti.SymmetricIdeal.paperLpNorm p hp).Mem B.B01) :
    (TauCeti.SymmetricIdeal.paperLpNorm p hp).Mem
        (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ∧
      d * (TauCeti.SymmetricIdeal.paperLpNorm p hp).gauge
          (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
        2 * (TauCeti.SymmetricIdeal.paperLpNorm p hp).gauge B.B01 :=
  sharp_paperUnitaryInvariantNorm
    (TauCeti.SymmetricIdeal.paperLpNorm p hp)
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
        (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ∧
      d * paperNuclearNorm.gauge
          (TauCeti.DavisKahan.doubleAngleTangentOperator X hcontractive) ≤
        2 * paperNuclearNorm.gauge B.B01 :=
  sharp_paperUnitaryInvariantNorm paperNuclearNorm
    B hd hA0 hA1 hX hcontractive hB

end

end FinishTanTwoTheta
end DavisKahan
end TauCeti
