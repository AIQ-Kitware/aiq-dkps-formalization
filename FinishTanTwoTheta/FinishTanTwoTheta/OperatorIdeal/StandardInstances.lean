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
  /- Every nonempty finite `ell-infinity` prefix equals `a_0(A)=||A||` by
  antitonicity; the empty prefix contributes zero. -/
  sorry

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
  /- The `ell-infinity` gauge of the tail is its first entry because the
  approximation-number sequence is decreasing. -/
  sorry

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
    (𝕜 : Type u) [RCLike 𝕜] : SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge := fun A => compactOperatorNormGauge A
  gauge_add_le := by
    /- Compactness is stable under addition and the operator norm is
    subadditive. -/
    sorry
  gauge_smul := by
    /- Handle zero scalar separately; nonzero scalar preserves compactness. -/
    sorry
  enorm_le_gauge := by
    intro E F _ _ _ _ A
    unfold compactOperatorNormGauge
    split_ifs <;> simp
  gauge_comp_le := by
    /- Approximation-number ideal inequalities preserve convergence to zero;
    then apply the operator-norm composition inequality. -/
    sorry
  gauge_adjoint := by
    /- Approximation numbers and operator norm are adjoint invariant. -/
    sorry

/-- Compact operators with operator norm form the minimal standard
`ell-infinity` ideal. -/
noncomputable def standardCompactOperatorNormFamily
    (𝕜 : Type u) [RCLike 𝕜] : StandardSymmetricIdealFamily.{u, v} 𝕜 where
  toSymmetricOperatorIdealFamily := compactOperatorNormFamily 𝕜
  normingFunction := linftyNormingFunction
  completion := SymmetricIdealCompletion.minimal
  gauge_eq_standardSequenceGauge := by
    intro E F _ _ _ _ _ A
    rw [linfty_isMinimalSequence_iff_tendsto_approximationNumber_zero A]
    unfold compactOperatorNormGauge SymmetricNormingFunction.standardSequenceGauge
    split_ifs with h
    · rw [linfty_sequenceGauge_approximationNumbers_eq_enorm A]
    · rfl

/-- Operator-norm Fan dominance. -/
theorem opNorm_le_of_approximationNumberPrefix_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A B : E →L[𝕜] F)
    (h : ∀ k, approximationNumberPrefix k A ≤ approximationNumberPrefix k B) :
    ‖A‖ ≤ ‖B‖ := by
  /- The `k=1` prefix is the operator norm. -/
  sorry

/-- Fixed finite Ky Fan symmetric norming function: on a finite vector it is
the sum of the `q` largest absolute coordinates, padding with zero when the
ambient vector has fewer than `q` coordinates. -/
noncomputable def kyFanNormingFunction (q : ℕ) (hq : 0 < q) :
    SymmetricNormingFunction := by
  /-
  Construct each finite gauge by decreasingly rearranging the absolute values
  and summing the first `min q n` entries.  Triangle inequality is finite Ky
  Fan dominance; permutation/sign invariance and zero-padding are immediate.
  -/
  sorry

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
  sorry

/-- Maximal fixed-Ky-Fan ideal: all bounded operators with the first-`q`
approximation-number sum. -/
noncomputable def boundedKyFanIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (q : ℕ) (hq : 0 < q) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 := by
  /- Package the ENNReal coercion of `approximationNumberPrefix q`; the parent
  repository already proves the Ky Fan triangle, homogeneity, adjoint, and
  two-sided ideal inequalities. -/
  sorry

/-- Maximal fixed-Ky-Fan family as a standard symmetric ideal. -/
noncomputable def standardBoundedKyFanIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (q : ℕ) (hq : 0 < q) :
    StandardSymmetricIdealFamily.{u, v} 𝕜 := by
  refine
    { toSymmetricOperatorIdealFamily := boundedKyFanIdealFamily 𝕜 q hq
      normingFunction := kyFanNormingFunction q hq
      completion := SymmetricIdealCompletion.maximal
      gauge_eq_standardSequenceGauge := ?_ }
  intro E F _ _ _ _ _ A
  /- Unfold the bounded Ky Fan gauge and use the preceding prefix theorem. -/
  sorry

/-- The minimal fixed-Ky-Fan completion is again the compact operators, now
with the fixed Ky Fan norm. -/
noncomputable def compactKyFanIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (q : ℕ) (hq : 0 < q) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 := by
  /- Define the extended gauge as the first-`q` approximation-number sum on
  compact operators and `∞` otherwise.  Use the Ky Fan triangle and ideal
  inequalities already present in the parent repository. -/
  sorry

/-- Fixed Ky Fan compact ideal as a standard minimal ideal. -/
noncomputable def standardCompactKyFanIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (q : ℕ) (hq : 0 < q) :
    StandardSymmetricIdealFamily.{u, v} 𝕜 := by
  /- Package `compactKyFanIdealFamily` with `kyFanNormingFunction`; the minimal
  tail condition is equivalent to compactness because every fixed positive Ky
  Fan norm is equivalent to the operator norm. -/
  sorry

end FinishTanTwoTheta
end TauCeti
