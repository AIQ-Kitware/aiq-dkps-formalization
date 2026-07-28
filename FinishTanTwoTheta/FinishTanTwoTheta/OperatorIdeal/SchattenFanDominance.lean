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
  /-
  Proof plan:
  * finite prefix gauges are increasing because zero padding and coordinatewise
    monotonicity identify the `(n+1)` prefix with the `n` prefix plus one term;
  * continuity of `rpow` converts the supremum of finite partial sums into the
    `tsum` in `ℝ≥0∞`;
  * `p >= 1` gives `p > 0`, so the outer `1/p` power is order-continuous;
  * both sides are `∞` exactly when the `p`-power series diverges.
  -/
  sorry

/-- Schatten membership is equivalent to summability of the `p`th powers of
approximation numbers. -/
theorem isSchatten_iff_summable_rpow
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] F) :
    IsSchatten p hp A ↔ Summable (fun n => (A.approximationNumber n) ^ p) := by
  /- Derive from `schattenGauge_eq_tsum_rpow` and the ENNReal finiteness
  criterion for a nonnegative series. -/
  sorry


/-- For finite `p`, the maximal `ell^p` space is order-continuous, so its
minimal and maximal standard completions coincide. -/
theorem lp_standardSequenceGauge_minimal_eq_maximal
    (p : ℝ) (hp : 1 ≤ p) (x : ℕ → ℝ) :
    (lpNormingFunction p hp).standardSequenceGauge
        SymmetricIdealCompletion.minimal x =
      (lpNormingFunction p hp).standardSequenceGauge
        SymmetricIdealCompletion.maximal x := by
  /- If the `p`-sum is finite, tails tend to zero by convergence of the
  nonnegative series.  If it is infinite, both extended gauges are `∞`. -/
  sorry

/-- The approximation-number Schatten gauge satisfies the complete operator
ideal laws. -/
noncomputable def schattenIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 ≤ p) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge := fun A => schattenGauge p hp A
  gauge_add_le := by
    /- Use approximation-number Ky Fan submajorization for `A+B`, finite
    Minkowski, and passage to the supremum. -/
    sorry
  gauge_smul := by
    /- Approximation numbers are absolutely homogeneous. -/
    sorry
  enorm_le_gauge := by
    /- The first approximation number is the operator norm and every finite
    `ell^p` gauge dominates its first coordinate. -/
    sorry
  gauge_comp_le := by
    /- Apply the two-sided approximation-number ideal inequality coordinatewise
    and finite `ell^p` homogeneity, then take the supremum. -/
    sorry
  gauge_adjoint := by
    /- Approximation numbers are invariant under adjoint. -/
    sorry

/-- Schatten ideals are standard symmetric ideals, hence Fan dominance is a
theorem rather than an assumed structure field. -/
noncomputable def standardSchattenIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 ≤ p) :
    StandardSymmetricIdealFamily.{u, v} 𝕜 where
  toSymmetricOperatorIdealFamily := schattenIdealFamily 𝕜 p hp
  normingFunction := lpNormingFunction p hp
  completion := SymmetricIdealCompletion.minimal
  gauge_eq_standardSequenceGauge := by
    intro E F _ _ _ _ _ A
    rw [lp_standardSequenceGauge_minimal_eq_maximal p hp]
    rfl

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
