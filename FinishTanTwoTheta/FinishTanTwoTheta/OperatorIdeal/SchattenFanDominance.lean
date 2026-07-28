/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.OperatorIdeal.GeneratedFamilies
import ForTauCeti.Analysis.Normed.FiniteLpGauge

/-!
# Schatten ideals and Fan dominance

This file specializes the standard symmetric-ideal construction to the finite
`ell^p` gauges.  The difficult analytic point is the Fatou passage: boundedness
of every finite `ell^p` prefix is equivalent to summability of the full
approximation-number sequence, and the supremum of prefix norms is the usual
Schatten norm.
-/

namespace TauCeti
namespace FinishTanTwoTheta

open scoped BigOperators ENNReal

universe u v

/-- The coherent finite `ell^p` symmetric norming function. -/
noncomputable def lpNormingFunction (p : ℝ) (hp : 1 ≤ p) :
    SymmetricNormingFunction where
  finiteGauge := fun n => FiniteVector.lpSymmetricGauge (n := n) p hp
  zeroPad := by
    intro n m x
    exact FiniteVector.lpGauge_zeroPadRight p x
  normalized := by
    simp [FiniteVector.lpSymmetricGauge, FiniteVector.lpGauge,
      Real.one_rpow]

/-- Extended approximation-number `ell^p` gauge.  It may be `∞`. -/
noncomputable def schattenGauge
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] F) : ℝ≥0∞ :=
  (lpNormingFunction p hp).sequenceGauge (approximationNumberSequence A)

/-- Membership in the approximation-number Schatten `p` class. -/
def IsSchatten
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] F) : Prop :=
  schattenGauge p hp A ≠ ∞

/-- Fatou identification of the prefix gauge with the usual infinite
`ell^p` norm.  This is the central analytic theorem of the Schatten lane. -/
theorem schattenGauge_eq_tsum_rpow
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] F) :
    schattenGauge p hp A =
      ENNReal.rpow
        (∑' n : ℕ, ENNReal.ofReal ((A.approximationNumber n) ^ p))
        (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  unfold schattenGauge SymmetricNormingFunction.sequenceGauge
    SymmetricNormingFunction.prefixGauge lpNormingFunction
  exact ENNReal.iSup_lpPrefix_eq_rpow_tsum
    (f := fun n => A.approximationNumber n) hp0
    (fun n => A.approximationNumber_nonneg n)

/-- Schatten membership is equivalent to summability of the `p`th powers of
approximation numbers. -/
theorem isSchatten_iff_summable_rpow
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] F) :
    IsSchatten p hp A ↔ Summable (fun n => (A.approximationNumber n) ^ p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [IsSchatten, schattenGauge_eq_tsum_rpow p hp A]
  rw [ENNReal.rpow_ne_top_iff_of_pos hp0]
  exact ENNReal.tsum_ofReal_ne_top_iff_summable
    (fun n => Real.rpow_nonneg (A.approximationNumber n) p)


/-- For finite `p`, the maximal `ell^p` space is order-continuous, so its
minimal and maximal standard completions coincide. -/
theorem lp_standardSequenceGauge_minimal_eq_maximal
    (p : ℝ) (hp : 1 ≤ p) (x : ℕ → ℝ) :
    (lpNormingFunction p hp).standardSequenceGauge
        SymmetricIdealCompletion.minimal x =
      (lpNormingFunction p hp).standardSequenceGauge
        SymmetricIdealCompletion.maximal x := by
  unfold SymmetricNormingFunction.standardSequenceGauge
  by_cases hfin : (lpNormingFunction p hp).sequenceGauge x = ∞
  · have hnot : ¬(lpNormingFunction p hp).IsMinimalSequence x := by
      intro hmin
      exact hfin ((lpNormingFunction p hp).sequenceGauge_ne_top_of_isMinimal hmin)
    simp [hfin, hnot]
  · have hmin : (lpNormingFunction p hp).IsMinimalSequence x :=
      lp_tail_sequenceGauge_tendsto_zero_of_sequenceGauge_ne_top p hp x hfin
    simp [hmin]

/-- The approximation-number Schatten gauge satisfies the complete operator
ideal laws. -/
noncomputable def schattenIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 ≤ p) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 :=
  generatedSymmetricIdealFamily (𝕜 := 𝕜) (lpNormingFunction p hp)
    SymmetricIdealCompletion.maximal

/-- Schatten ideals are standard symmetric ideals, hence Fan dominance is a
theorem rather than an assumed structure field. -/
noncomputable def standardSchattenIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 ≤ p) :
    StandardSymmetricIdealFamily.{u, v} 𝕜 :=
  generatedMaximalStandardIdeal (𝕜 := 𝕜) (v := v) (lpNormingFunction p hp)

/-- Fan dominance for every Schatten class `S^p`, `1 <= p < infinity`. -/
theorem schatten_fanDominance
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (p : ℝ) (hp : 1 ≤ p) (A B : E →L[𝕜] F)
    (hB : IsSchatten p hp B)
    (hprefix : ∀ k, approximationNumberPrefix k A ≤ approximationNumberPrefix k B) :
    IsSchatten p hp A ∧ schattenGauge p hp A ≤ schattenGauge p hp B := by
  simpa [IsSchatten, schattenGauge, standardSchattenIdealFamily,
    schattenIdealFamily] using
    (standardSchattenIdealFamily (v := v) 𝕜 p hp).fanDominance A B hB hprefix

/-- Trace class is the standard Schatten class at `p = 1`. -/
noncomputable def traceClassIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] : StandardSymmetricIdealFamily.{u, v} 𝕜 :=
  standardSchattenIdealFamily 𝕜 1 le_rfl

/-- Hilbert--Schmidt class is the standard Schatten class at `p = 2`. -/
noncomputable def hilbertSchmidtIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] : StandardSymmetricIdealFamily.{u, v} 𝕜 :=
  standardSchattenIdealFamily 𝕜 2 (by norm_num)

end FinishTanTwoTheta
end TauCeti
