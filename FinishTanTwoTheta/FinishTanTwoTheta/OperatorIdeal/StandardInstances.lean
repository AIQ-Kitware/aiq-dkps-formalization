/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.OperatorIdeal.SchattenFanDominance
import ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm

/-!
# Standard symmetric-ideal instances

This file records the standard examples needed by Davis--Kahan and verifies
that the maximal/minimal distinction is represented rather than erased.

* maximal `ell-infinity`: every bounded operator with operator norm;
* minimal `ell-infinity`: compact operators with operator norm;
* fixed finite Ky Fan norm, in maximal and minimal forms;
* Schatten, trace, and Hilbert--Schmidt are supplied by the preceding file.
-/

namespace TauCeti
namespace FinishTanTwoTheta

open scoped ENNReal Topology
open Filter

universe u v

/-- The coherent finite `ell-infinity` norming function. -/
noncomputable def linftyNormingFunction : SymmetricNormingFunction where
  finiteGauge := fun n => FiniteVector.linftySymmetricGauge (n := n)
  zeroPad := by
    intro n m x
    exact FiniteVector.linftyGauge_zeroPadRight x
  normalized := by simp [FiniteVector.linftySymmetricGauge,
    FiniteVector.linftyGauge]

/-- The maximal extension of finite `ell-infinity` gauges is the operator
norm. -/
theorem linfty_sequenceGauge_approximationNumbers_eq_enorm
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    linftyNormingFunction.sequenceGauge (approximationNumberSequence A) =
      ‖A‖ₑ := by
  rw [← ENNReal.ofReal_norm, ← A.approximationNumber_index_zero]
  exact linfty_sequenceGauge_of_antitone_nonneg_eq_first
    (approximationNumberSequence_antitone_nonneg A)

/-- The minimal `ell-infinity` condition is exactly convergence of
approximation numbers to zero, hence compactness on Hilbert spaces. -/
theorem linfty_isMinimalSequence_iff_tendsto_approximationNumber_zero
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    linftyNormingFunction.IsMinimalSequence (approximationNumberSequence A) ↔
      Tendsto (approximationNumberSequence A) atTop (𝓝 0) := by
  unfold SymmetricNormingFunction.IsMinimalSequence
  have htail : ∀ n, linftyNormingFunction.sequenceGauge
      (SymmetricNormingFunction.sequenceTail n
        (approximationNumberSequence A)) =
      ENNReal.ofReal (A.approximationNumber n) := by
    intro n
    exact linfty_sequenceGauge_antitone_tail_eq_first
      (approximationNumberSequence_antitone_nonneg A) n
  simp_rw [htail]
  exact ENNReal.tendsto_ofReal_zero_iff
    (fun n => A.approximationNumber_nonneg n)

/-- Maximal operator-norm family: all bounded operators. -/
noncomputable def standardOperatorNormFamily
    (𝕜 : Type u) [RCLike 𝕜] : StandardSymmetricIdealFamily.{u, v} 𝕜 where
  toSymmetricOperatorIdealFamily := operatorNormFamily 𝕜
  normingFunction := linftyNormingFunction
  completion := SymmetricIdealCompletion.maximal
  gauge_eq_standardSequenceGauge := by
    intro E F _ _ _ _ _ A
    change ‖A‖ₑ = linftyNormingFunction.sequenceGauge
      (approximationNumberSequence A)
    symm
    exact linfty_sequenceGauge_approximationNumbers_eq_enorm A

/-- Extended operator norm which is finite exactly when approximation numbers
tend to zero. -/
noncomputable def compactOperatorNormGauge
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : ℝ≥0∞ :=
  if Tendsto (approximationNumberSequence A) atTop (𝓝 0) then ‖A‖ₑ else ∞

/-- Minimal operator-norm ideal: compact operators with the operator norm. -/
noncomputable def compactOperatorNormFamily
    (𝕜 : Type u) [RCLike 𝕜] : SymmetricOperatorIdealFamily.{u, v} 𝕜 :=
  generatedSymmetricIdealFamily (𝕜 := 𝕜) linftyNormingFunction
    SymmetricIdealCompletion.minimal

/-- Compact operators with operator norm form the minimal standard
`ell-infinity` ideal. -/
noncomputable def standardCompactOperatorNormFamily
    (𝕜 : Type u) [RCLike 𝕜] : StandardSymmetricIdealFamily.{u, v} 𝕜 :=
  generatedMinimalStandardIdeal (𝕜 := 𝕜) (v := v) linftyNormingFunction

/-- Operator-norm Fan dominance. -/
theorem opNorm_le_of_approximationNumberPrefix_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A B : E →L[𝕜] F)
    (h : ∀ k, approximationNumberPrefix k A ≤ approximationNumberPrefix k B) :
    ‖A‖ ≤ ‖B‖ := by
  have h1 := h 1
  simpa [approximationNumberPrefix, sequencePrefixSum,
    approximationNumberSequence] using h1

/-- Fixed finite Ky Fan symmetric norming function: on a finite vector it is
the sum of the `q` largest absolute coordinates, padding with zero when the
ambient vector has fewer than `q` coordinates. -/
noncomputable def kyFanNormingFunction (q : ℕ) (hq : 0 < q) :
    SymmetricNormingFunction where
  finiteGauge := fun n => FiniteVector.kyFanSymmetricGauge q n
  zeroPad := by
    intro n m x
    exact FiniteVector.kyFanGauge_zeroPadRight q x
  normalized := by
    simpa [FiniteVector.kyFanSymmetricGauge, hq] using
      FiniteVector.kyFanGauge_singleton_one q hq

/-- The maximal fixed-Ky-Fan gauge is finite on all bounded operators and is
the usual first-`q` approximation-number sum. -/
theorem kyFan_standardSequenceGauge_maximal_eq_prefix
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (q : ℕ) (hq : 0 < q) (A : E →L[𝕜] F) :
    (kyFanNormingFunction q hq).standardSequenceGauge
        SymmetricIdealCompletion.maximal (approximationNumberSequence A) =
      ENNReal.ofReal (approximationNumberPrefix q A) := by
  unfold SymmetricNormingFunction.standardSequenceGauge
    SymmetricNormingFunction.sequenceGauge
  exact FiniteVector.iSup_kyFanPrefixGauge_eq_prefix q hq
    (approximationNumberSequence_antitone_nonneg A)

/-- Maximal fixed-Ky-Fan ideal: all bounded operators with the first-`q`
approximation-number sum. -/
noncomputable def boundedKyFanIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (q : ℕ) (hq : 0 < q) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 :=
  generatedSymmetricIdealFamily (𝕜 := 𝕜) (kyFanNormingFunction q hq)
    SymmetricIdealCompletion.maximal

/-- Maximal fixed-Ky-Fan family as a standard symmetric ideal. -/
noncomputable def standardBoundedKyFanIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (q : ℕ) (hq : 0 < q) :
    StandardSymmetricIdealFamily.{u, v} 𝕜 :=
  generatedMaximalStandardIdeal (𝕜 := 𝕜) (v := v)
    (kyFanNormingFunction q hq)

/-- The minimal fixed-Ky-Fan completion is again the compact operators, now
with the fixed Ky Fan norm. -/
noncomputable def compactKyFanIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (q : ℕ) (hq : 0 < q) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 :=
  generatedSymmetricIdealFamily (𝕜 := 𝕜) (kyFanNormingFunction q hq)
    SymmetricIdealCompletion.minimal

/-- Fixed Ky Fan compact ideal as a standard minimal ideal. -/
noncomputable def standardCompactKyFanIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (q : ℕ) (hq : 0 < q) :
    StandardSymmetricIdealFamily.{u, v} 𝕜 :=
  generatedMinimalStandardIdeal (𝕜 := 𝕜) (v := v)
    (kyFanNormingFunction q hq)

end FinishTanTwoTheta
end TauCeti
