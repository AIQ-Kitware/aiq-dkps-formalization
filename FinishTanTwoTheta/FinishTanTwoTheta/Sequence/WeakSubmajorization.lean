/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.GroundedImports
import ForTauCeti.Analysis.Normed.FiniteLpGauge

/-!
# Infinite weak submajorization

This file lifts the existing finite weak-majorization theory to decreasing
nonnegative sequences.  The definition is intentionally prefix-based because
approximation numbers already arrive in decreasing nonnegative order.
-/

namespace TauCeti
namespace FinishTanTwoTheta

open scoped BigOperators

/-- Sum of the first `k` entries of a real sequence. -/
def sequencePrefixSum (k : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range k, x i

@[simp] theorem sequencePrefixSum_zero (k : ℕ) :
    sequencePrefixSum k (0 : ℕ → ℝ) = 0 := by
  simp [sequencePrefixSum]

@[simp] theorem sequencePrefixSum_add (k : ℕ) (x y : ℕ → ℝ) :
    sequencePrefixSum k (x + y) =
      sequencePrefixSum k x + sequencePrefixSum k y := by
  simp [sequencePrefixSum, Finset.sum_add_distrib]

@[simp] theorem sequencePrefixSum_smul (k : ℕ) (c : ℝ) (x : ℕ → ℝ) :
    sequencePrefixSum k (c • x) = c * sequencePrefixSum k x := by
  simp [sequencePrefixSum, Finset.mul_sum]

/-- Weak submajorization of decreasing nonnegative sequences. -/
structure WeaklySubmajorized (x y : ℕ → ℝ) : Prop where
  left_antitone : Antitone x
  right_antitone : Antitone y
  left_nonneg : ∀ n, 0 ≤ x n
  right_nonneg : ∀ n, 0 ≤ y n
  prefix_le : ∀ k, sequencePrefixSum k x ≤ sequencePrefixSum k y

local infix:50 " ≺w " => WeaklySubmajorized

namespace WeaklySubmajorized

/-- Reflexivity on decreasing nonnegative sequences. -/
theorem refl {x : ℕ → ℝ} (hanti : Antitone x) (h0 : ∀ n, 0 ≤ x n) :
    x ≺w x :=
  ⟨hanti, hanti, h0, h0, fun _ => le_rfl⟩

/-- Transitivity of weak submajorization. -/
theorem trans {x y z : ℕ → ℝ} (hxy : x ≺w y) (hyz : y ≺w z) :
    x ≺w z :=
  ⟨hxy.left_antitone, hyz.right_antitone,
    hxy.left_nonneg, hyz.right_nonneg,
    fun k => (hxy.prefix_le k).trans (hyz.prefix_le k)⟩

/-- Coordinatewise domination implies weak submajorization. -/
theorem of_pointwise {x y : ℕ → ℝ}
    (hxanti : Antitone x) (hyanti : Antitone y)
    (hx0 : ∀ n, 0 ≤ x n) (hy0 : ∀ n, 0 ≤ y n)
    (hxy : ∀ n, x n ≤ y n) : x ≺w y := by
  refine ⟨hxanti, hyanti, hx0, hy0, fun k => ?_⟩
  exact Finset.sum_le_sum fun i _ => hxy i

/-- Nonnegative scaling preserves weak submajorization. -/
theorem nonneg_smul {x y : ℕ → ℝ} (hxy : x ≺w y)
    {c : ℝ} (hc : 0 ≤ c) : c • x ≺w c • y := by
  refine ⟨?_, ?_, ?_, ?_, fun k => ?_⟩
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (hxy.left_antitone hij) hc
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (hxy.right_antitone hij) hc
  · intro i
    exact mul_nonneg hc (hxy.left_nonneg i)
  · intro i
    exact mul_nonneg hc (hxy.right_nonneg i)
  · rw [sequencePrefixSum_smul, sequencePrefixSum_smul]
    exact mul_le_mul_of_nonneg_left (hxy.prefix_le k) hc

end WeaklySubmajorized

/-- The first `n` entries of a sequence, as a vector indexed by `Fin n`. -/
def sequencePrefixVector (n : ℕ) (x : ℕ → ℝ) : Fin n → ℝ :=
  fun i => x i

/-- Prefix sums of `sequencePrefixVector` agree with sequence prefix sums up to
its length. -/
theorem finitePrefixSum_sequencePrefixVector
    (x : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n) :
    FiniteVector.prefixSum k (sequencePrefixVector n x) =
      sequencePrefixSum k x := by
  unfold FiniteVector.prefixSum sequencePrefixSum sequencePrefixVector
  have hfilter :
      Finset.univ.filter (fun i : Fin n => (i : ℕ) < k) =
        Finset.univ.map (Fin.castLEEmb n hk) := by
    ext i
    simp [Fin.castLEEmb, Fin.lt_iff_val_lt_val]
  rw [hfilter, Finset.sum_map]
  rfl

/-- Every finite prefix of weakly submajorized sequences is weakly majorized
in the existing finite-vector sense. -/
theorem finite_weaklyMajorized_of_weaklySubmajorized
    {x y : ℕ → ℝ} (hxy : x ≺w y) (n : ℕ) :
    FiniteVector.WeaklyMajorized
      (sequencePrefixVector n x)
      (sequencePrefixVector n y) := by
  refine ⟨?_, ?_, ?_, ?_, fun k => ?_⟩
  · intro i j hij
    exact hxy.left_antitone (by exact_mod_cast hij)
  · intro i j hij
    exact hxy.right_antitone (by exact_mod_cast hij)
  · intro i
    exact hxy.left_nonneg i
  · intro i
    exact hxy.right_nonneg i
  · by_cases hk : k ≤ n
    · rw [finitePrefixSum_sequencePrefixVector x n k hk,
        finitePrefixSum_sequencePrefixVector y n k hk]
      exact hxy.prefix_le k
    · have hnk : n ≤ k := Nat.le_of_not_ge hk
      rw [FiniteVector.prefixSum_eq_full_sum_of_le _ hnk,
        FiniteVector.prefixSum_eq_full_sum_of_le _ hnk]
      simpa [sequencePrefixVector, sequencePrefixSum,
        Fin.sum_univ_eq_sum_range] using hxy.prefix_le n

end FinishTanTwoTheta
end TauCeti
