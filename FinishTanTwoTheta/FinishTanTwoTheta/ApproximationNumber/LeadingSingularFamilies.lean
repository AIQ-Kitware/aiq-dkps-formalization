/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.OperatorIdeal.StandardInstances
import DavisKahan.Experimental.Scratch.Section7.InfiniteTanTwoThetaCore

/-!
# Approximate leading singular families

An arbitrary bounded operator need not attain its approximation numbers by
singular vectors.  Nevertheless, for every finite leading block and every
positive tolerance, all approximation numbers above the tolerance admit a
simultaneous orthonormal family of approximate left/right singular pairs.  The
remaining leading approximation numbers are themselves at most the tolerance.

This is the correct noncompact replacement for the exact singular-family
hypothesis used by the finite-dimensional proof.
-/

namespace TauCeti
namespace FinishTanTwoTheta

open scoped InnerProductSpace

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- A simultaneous approximate singular system for the initial segment of the
approximation-number sequence.

The selected values are the first `count` approximation numbers.  Antitonicity
then makes `tail_small` exactly the assertion that every omitted value among
the requested first `k` entries is negligible. -/
structure ApproximateLeadingSingularFamily
    (X : E0 →L[ℂ] E1) (k : ℕ) (ε : ℝ) where
  count : ℕ
  count_le : count ≤ k
  right : Fin count → E0
  left : Fin count → E1
  right_orthonormal : Orthonormal ℂ right
  left_orthonormal : Orthonormal ℂ left
  selected_large : ∀ i : Fin count, ε < X.approximationNumber i
  apply_residual : ∀ i : Fin count,
    ‖X (right i) - (X.approximationNumber i : ℂ) • left i‖ ≤ ε
  adjoint_residual : ∀ i : Fin count,
    ‖X.adjoint (left i) - (X.approximationNumber i : ℂ) • right i‖ ≤ ε
  tail_small : ∀ n, count ≤ n → n < k → X.approximationNumber n ≤ ε

namespace ApproximateLeadingSingularFamily

variable {X : E0 →L[ℂ] E1} {k : ℕ} {ε : ℝ}

@[simp] theorem norm_right (F : ApproximateLeadingSingularFamily X k ε)
    (i : Fin F.count) : ‖F.right i‖ = 1 :=
  F.right_orthonormal.norm_eq_one i

@[simp] theorem norm_left (F : ApproximateLeadingSingularFamily X k ε)
    (i : Fin F.count) : ‖F.left i‖ = 1 :=
  F.left_orthonormal.norm_eq_one i

/-- Negating the right family preserves orthonormality, as required by the
signed Ky Fan coefficient estimate. -/
theorem orthonormal_neg_right
    (F : ApproximateLeadingSingularFamily X k ε) :
    Orthonormal ℂ (fun i => -F.right i) := by
  rw [orthonormal_iff_ite] at F.right_orthonormal ⊢
  intro i j
  simpa using F.right_orthonormal i j

end ApproximateLeadingSingularFamily

/-- **Approximate leading singular-family theorem.**

For every bounded operator, finite leading segment, and positive tolerance,
there is a simultaneous orthonormal family satisfying both singular equations
up to that tolerance, with every omitted leading approximation number small.
-/
theorem exists_approximateLeadingSingularFamily
    (X : E0 →L[ℂ] E1) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (ApproximateLeadingSingularFamily X k ε) := by
  classical
  obtain ⟨count, hcount, right, left, hright, hleft, hlarge,
      hX, hXstar, htail⟩ :=
    X.exists_orthonormal_approximateSingularSystem_initialSegment k ε hε
  exact ⟨{
    count := count
    count_le := hcount
    right := right
    left := left
    right_orthonormal := hright
    left_orthonormal := hleft
    selected_large := hlarge
    apply_residual := hX
    adjoint_residual := hXstar
    tail_small := htail
  }⟩

/-- Selected values plus a uniformly small tail recover the transformed first
`k` approximation numbers up to the obvious tail error. -/
theorem sum_le_selected_sum_add_tail
    (X : E0 →L[ℂ] E1) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (f : ℝ → ℝ) (hf0 : 0 ≤ f ε)
    (hfmono : MonotoneOn f (Set.Icc 0 ε))
    (F : ApproximateLeadingSingularFamily X k ε) :
    (∑ n ∈ Finset.range k, f (X.approximationNumber n)) ≤
      (∑ i : Fin F.count, f (X.approximationNumber i)) +
        (k - F.count) * f ε := by
  classical
  have hsplit := Finset.sum_range_add_sum_Ico
    (f := fun n => f (X.approximationNumber n)) F.count F.count_le
  rw [← hsplit]
  have hhead :
      (∑ n ∈ Finset.range F.count, f (X.approximationNumber n)) =
        ∑ i : Fin F.count, f (X.approximationNumber i) := by
    simpa [Fin.sum_univ_eq_sum_range]
  rw [hhead]
  apply add_le_add_left
  calc
    (∑ n ∈ Finset.Ico F.count k, f (X.approximationNumber n))
        ≤ ∑ _n ∈ Finset.Ico F.count k, f ε := by
          apply Finset.sum_le_sum
          intro n hn
          have hnmem := Finset.mem_Ico.mp hn
          have han0 : 0 ≤ X.approximationNumber n :=
            X.approximationNumber_nonneg n
          have hane : X.approximationNumber n ≤ ε :=
            F.tail_small n hnmem.1 hnmem.2
          exact hfmono ⟨han0, hane⟩ ⟨hε, le_rfl⟩
    _ = (k - F.count) * f ε := by
          rw [Finset.sum_const, Finset.card_Ico]
          simp [nsmul_eq_mul, Nat.cast_sub F.count_le]
    _ ≤ (k - F.count) * f ε := le_rfl

end FinishTanTwoTheta
end TauCeti
