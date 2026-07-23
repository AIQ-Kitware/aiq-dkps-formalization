/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import Mathlib

/-!
# Davis--Kahan 1970, Section 9: domain limitation example

The source displays a geometric trial sequence whose image under a diagonal
unbounded operator is the constant sequence, hence is not square summable.  It
then notes that an arbitrarily small modification repairs the domain issue.
Here the repair is made explicit by finite truncation.  The statements below
are sequence-level and avoid pretending that an undefined residual is a vector
of `ell^2`.
-/

namespace ForMathlib
namespace DavisKahan1970
namespace Section9

/-- The geometric trial sequence. -/
def rawTrialSequence (μ : ℝ) (n : ℕ) : ℝ := μ ^ n

/-- The diagonal multiplier used in the source example. -/
noncomputable def diagonalMultiplier (μ : ℝ) (n : ℕ) : ℝ := (μ ^ n)⁻¹

/-- The pointwise image of the geometric trial sequence. -/
noncomputable def rawDiagonalImage (μ : ℝ) (n : ℕ) : ℝ :=
  diagonalMultiplier μ n * rawTrialSequence μ n

lemma rawDiagonalImage_eq_one {μ : ℝ} (hμ : μ ≠ 0) (n : ℕ) :
    rawDiagonalImage μ n = 1 := by
  unfold rawDiagonalImage diagonalMultiplier rawTrialSequence
  exact inv_mul_cancel₀ (pow_ne_zero n hμ)

/-- Every length-`N` partial square energy of the raw image equals `N`; this is
the finite certificate of divergence used by the domain counterexample. -/
theorem rawDiagonalImage_partial_energy
    {μ : ℝ} (hμ : μ ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range N, rawDiagonalImage μ n ^ 2 = N := by
  simp [rawDiagonalImage_eq_one hμ]

/-- Finite truncation gives a concrete nearby sequence in the diagonal
operator's domain. -/
def truncatedTrialSequence (μ : ℝ) (N n : ℕ) : ℝ :=
  if n < N then μ ^ n else 0

/-- Image of the truncated trial sequence. -/
noncomputable def truncatedDiagonalImage (μ : ℝ) (N n : ℕ) : ℝ :=
  diagonalMultiplier μ n * truncatedTrialSequence μ N n

lemma truncatedTrialSequence_eq_raw {μ : ℝ} {N n : ℕ} (hn : n < N) :
    truncatedTrialSequence μ N n = rawTrialSequence μ n := by
  simp [truncatedTrialSequence, rawTrialSequence, hn]

lemma truncatedTrialSequence_eq_zero {μ : ℝ} {N n : ℕ} (hn : N ≤ n) :
    truncatedTrialSequence μ N n = 0 := by
  simp [truncatedTrialSequence, not_lt.mpr hn]

lemma truncatedDiagonalImage_eq_one
    {μ : ℝ} (hμ : μ ≠ 0) {N n : ℕ} (hn : n < N) :
    truncatedDiagonalImage μ N n = 1 := by
  simp [truncatedDiagonalImage, truncatedTrialSequence, diagonalMultiplier,
    hn, inv_mul_cancel₀ (pow_ne_zero n hμ)]

lemma truncatedDiagonalImage_eq_zero
    {μ : ℝ} {N n : ℕ} (hn : N ≤ n) :
    truncatedDiagonalImage μ N n = 0 := by
  simp [truncatedDiagonalImage, truncatedTrialSequence, not_lt.mpr hn]

/-- The corrected residual has exactly `N` units of square energy and finite
support. -/
theorem truncatedDiagonalImage_energy
    {μ : ℝ} (hμ : μ ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range N, truncatedDiagonalImage μ N n ^ 2 = N := by
  -- the rewrite is conditional on `n < N`, so it has to happen under the
  -- membership hypothesis rather than in a bare `simp` set
  have hterm : ∀ n ∈ Finset.range N, truncatedDiagonalImage μ N n ^ 2 = 1 := by
    intro n hn
    rw [truncatedDiagonalImage_eq_one hμ (Finset.mem_range.mp hn), one_pow]
  rw [Finset.sum_congr rfl hterm]
  simp

/-- Outside the truncation range the corrected image vanishes. -/
theorem truncatedDiagonalImage_support
    (μ : ℝ) (N n : ℕ) (hn : N ≤ n) :
    truncatedDiagonalImage μ N n = 0 :=
  truncatedDiagonalImage_eq_zero hn

/-- Truncation changes only the geometric tail. -/
theorem raw_sub_truncated
    (μ : ℝ) (N n : ℕ) :
    rawTrialSequence μ n - truncatedTrialSequence μ N n =
      if n < N then 0 else μ ^ n := by
  by_cases hn : n < N
  · simp [rawTrialSequence, truncatedTrialSequence, hn]
  · simp [rawTrialSequence, truncatedTrialSequence, hn]

/-- On every fixed initial segment, sufficiently long truncations agree exactly
with the original trial sequence. -/
theorem truncation_eventually_agrees_on_prefix
    (μ : ℝ) (K N : ℕ) (hKN : K ≤ N) :
    ∀ n < K, truncatedTrialSequence μ N n = rawTrialSequence μ n := by
  intro n hn
  exact truncatedTrialSequence_eq_raw (lt_of_lt_of_le hn hKN)

end Section9
end DavisKahan1970
end ForMathlib
