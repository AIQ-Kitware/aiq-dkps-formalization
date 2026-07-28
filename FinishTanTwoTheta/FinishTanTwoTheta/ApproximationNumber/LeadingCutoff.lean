/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.GroundedImports
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-!
# Leading approximation-number cutoff

This file isolates the elementary finite-prefix bookkeeping used by spectral
selection.  `leadingCount X k ε` is the first index below `k` at which the
approximation numbers fall to `ε`, or `k` if no such index exists.
-/

namespace TauCeti
namespace FinishTanTwoTheta

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [NormedSpace ℂ E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [NormedSpace ℂ E1]

/-- The length of the strict leading prefix `ε < a_i(X)` inside `Finset.range k`. -/
noncomputable def leadingCount (X : E0 →L[ℂ] E1) (k : ℕ) (ε : ℝ) : ℕ :=
  if h : ∃ n : ℕ, n < k ∧ X.approximationNumber n ≤ ε then Nat.find h else k

@[simp]
theorem leadingCount_le (X : E0 →L[ℂ] E1) (k : ℕ) (ε : ℝ) :
    leadingCount X k ε ≤ k := by
  classical
  unfold leadingCount
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- Every index before the cutoff has approximation number strictly larger than `ε`. -/
theorem approximationNumber_gt_of_lt_leadingCount
    (X : E0 →L[ℂ] E1) (k : ℕ) (ε : ℝ) {i : ℕ}
    (hi : i < leadingCount X k ε) :
    ε < X.approximationNumber i := by
  classical
  unfold leadingCount at hi
  split_ifs at hi with h
  · have hik : i < k := hi.trans (Nat.find_spec h).1
    by_contra hnot
    have hle : X.approximationNumber i ≤ ε := le_of_not_gt hnot
    exact (Nat.find_min h hi) ⟨hik, hle⟩
  · by_contra hnot
    have hle : X.approximationNumber i ≤ ε := le_of_not_gt hnot
    exact h ⟨i, hi, hle⟩

/-- At and after the cutoff, while still below `k`, approximation numbers are at most `ε`. -/
theorem approximationNumber_le_of_leadingCount_le
    (X : E0 →L[ℂ] E1) (k : ℕ) (ε : ℝ) {n : ℕ}
    (hcount : leadingCount X k ε ≤ n) (hnk : n < k) :
    X.approximationNumber n ≤ ε := by
  classical
  unfold leadingCount at hcount
  split_ifs at hcount with h
  · have hcut : X.approximationNumber (Nat.find h) ≤ ε := (Nat.find_spec h).2
    exact (X.approximationNumber_antitone hcount).trans hcut
  · exact False.elim ((not_lt_of_ge hcount) hnk)

end

end FinishTanTwoTheta
end TauCeti
