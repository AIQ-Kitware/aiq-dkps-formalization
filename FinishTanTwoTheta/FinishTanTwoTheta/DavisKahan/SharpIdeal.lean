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

universe u

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type u} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Local adjoint invariance of maximal paper-ideal membership. -/
private theorem paperMem_adjoint_local
    (N : PaperUnitaryInvariantNorm) {A : E0 →L[ℂ] E1}
    (hA : N.Mem A) : N.Mem A.adjoint := by
  change N.extendedGauge A.adjoint ≠ ⊤
  rw [N.extendedGauge_adjoint]
  exact hA

/-- Local adjoint invariance of the real paper gauge. -/
private theorem paperGauge_adjoint_local
    (N : PaperUnitaryInvariantNorm) (A : E0 →L[ℂ] E1) :
    N.gauge A.adjoint = N.gauge A := by
  unfold PaperUnitaryInvariantNorm.gauge
  rw [N.extendedGauge_adjoint]

/-- A natural-number rank bound passes to the adjoint. -/
private theorem rank_adjoint_le_natCast_of_rank_le_local
    (R : E0 →L[ℂ] E1) {n : ℕ} (hR : R.rank ≤ (n : Cardinal)) :
    R.adjoint.rank ≤ (n : Cardinal) := by
  have hlt : R.rank < Cardinal.aleph0 :=
    hR.trans_lt Cardinal.natCast_lt_aleph0
  have hrank_eq : R.rank = (R.rank.toNat : Cardinal) := by
    exact (Cardinal.cast_toNat_of_lt_aleph0 hlt).symm
  letI : FiniteDimensional ℂ R.range :=
    Module.finite_of_rank_eq_nat hrank_eq
  letI : CompleteSpace R.range := FiniteDimensional.complete ℂ R.range
  have hadj : R.adjoint =
      R.rangeRestrict.adjoint ∘L R.range.subtypeL.adjoint := by
    rw [← ContinuousLinearMap.adjoint_comp]
    congr 1
  have hrestrict : R.rangeRestrict.adjoint.rank ≤ (n : Cardinal) :=
    Cardinal.lift_le_natCast.mp
      ((lift_rank_range_le R.rangeRestrict.adjoint.toLinearMap).trans
        (Cardinal.lift_le_natCast.mpr hR))
  rw [hadj]
  exact (rank_comp_le_left _ _).trans hrestrict

/-- Local adjoint invariance of the minimal finite-rank closure. -/
private theorem finiteRankApproximable_adjoint_local
    (N : PaperUnitaryInvariantNorm) {A : E0 →L[ℂ] E1}
    (hA : TauCeti.FinishTanTwoTheta.FiniteRankApproximable N A) :
    TauCeti.FinishTanTwoTheta.FiniteRankApproximable N A.adjoint := by
  refine ⟨paperMem_adjoint_local N hA.1, ?_⟩
  intro ε hε
  obtain ⟨R, hRrank, hRmem, hRsmall⟩ := hA.2 ε hε
  have hrank_eq : R.rank = (R.rank.toNat : Cardinal) := by
    exact (Cardinal.cast_toNat_of_lt_aleph0 hRrank).symm
  have hRadjRank : R.adjoint.rank < Cardinal.aleph0 :=
    (rank_adjoint_le_natCast_of_rank_le_local R hrank_eq.le).trans_lt
      Cardinal.natCast_lt_aleph0
  have hsub : A.adjoint - R.adjoint = (A - R).adjoint := by
    simpa only [map_sub]
  have hRadjMem : N.Mem (A.adjoint - R.adjoint) := by
    rw [hsub]
    exact paperMem_adjoint_local N hRmem
  have hRadjSmall : N.gauge (A.adjoint - R.adjoint) < ε := by
    rw [hsub, paperGauge_adjoint_local]
    exact hRsmall
  exact ⟨R.adjoint, hRadjRank, hRadjMem, hRadjSmall⟩

/-- Local adjoint invariance for either standard symmetric completion. -/
private theorem standardMem_adjoint_local
    (I : TauCeti.FinishTanTwoTheta.StandardSymmetricIdeal)
    {A : E0 →L[ℂ] E1} (hA : I.Mem A) : I.Mem A.adjoint := by
  cases I with
  | mk N completion =>
      cases completion with
      | maximal =>
          change N.Mem A at hA
          change N.Mem A.adjoint
          exact paperMem_adjoint_local N hA
      | minimal =>
          change TauCeti.FinishTanTwoTheta.FiniteRankApproximable N A at hA
          change TauCeti.FinishTanTwoTheta.FiniteRankApproximable N A.adjoint
          exact finiteRankApproximable_adjoint_local N hA

/-- Local adjoint invariance of the common standard-ideal gauge. -/
private theorem standardGauge_adjoint_local
    (I : TauCeti.FinishTanTwoTheta.StandardSymmetricIdeal)
    (A : E0 →L[ℂ] E1) : I.gauge A.adjoint = I.gauge A := by
  cases I with
  | mk N _ =>
      change N.gauge A.adjoint = N.gauge A
      exact paperGauge_adjoint_local N A

/-- The sharp Ky Fan estimate in the orientation needed by Fan dominance. -/
private theorem half_mul_kyFan_le_adjoint
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hcontractive : ‖X‖ < 1) (k : ℕ) :
    (d / 2) * kyFanApproximationGauge k
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) ≤
      kyFanApproximationGauge k B.B01.adjoint := by
  have hsharp := sharp_doubleAngleTangentOperator_kyFan
    B hd.le hA0 hA1 hX hcontractive k
  rw [kyFanApproximationGauge_adjoint]
  calc
    (d / 2) * kyFanApproximationGauge k
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive) =
        (d * kyFanApproximationGauge k
          (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive)) / 2 := by
      ring
    _ ≤ (2 * kyFanApproximationGauge k B.B01) / 2 :=
      (div_le_div_right (by norm_num : (0 : ℝ) < 2)).2 hsharp
    _ = kyFanApproximationGauge k B.B01 := by ring

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
  let T : E0 →L[ℂ] E1 :=
    TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive
  let S : E0 →L[ℂ] E1 := (((d / 2 : ℝ) : ℂ) • T)
  have hBadj : I.Mem B.B01.adjoint := standardMem_adjoint_local I hB
  have hdom : ∀ k : ℕ,
      kyFanApproximationGauge k S ≤
        kyFanApproximationGauge k B.B01.adjoint := by
    intro k
    rw [S, kyFanApproximationGauge_smul,
      RCLike.norm_ofReal, abs_of_nonneg (by positivity : 0 ≤ d / 2)]
    exact half_mul_kyFan_le_adjoint B hd hA0 hA1 hX hcontractive k
  have hfan : I.Mem S ∧ I.gauge S ≤ I.gauge B.B01.adjoint :=
    TauCeti.FinishTanTwoTheta.standard_fanDominance I hBadj hdom
  change I.Mem S ∧ I.gauge S ≤ I.gauge B.B01
  refine ⟨hfan.1, ?_⟩
  calc
    I.gauge S ≤ I.gauge B.B01.adjoint := hfan.2
    _ = I.gauge B.B01 := standardGauge_adjoint_local I B.B01

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
  let T : E0 →L[ℂ] E1 :=
    TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive
  have hBadj : N.Mem B.B01.adjoint :=
    paperMem_adjoint_local N hB
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
      rw [paperGauge_adjoint_local]

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
