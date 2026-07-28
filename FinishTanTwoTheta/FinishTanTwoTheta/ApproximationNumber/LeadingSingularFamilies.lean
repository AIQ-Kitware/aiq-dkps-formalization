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
  /-
  Mathematical proof plan.

  1. Apply the spectral theorem to the positive operator `|X|`.
  2. Approximation numbers strictly above the essential norm are isolated
     eigenvalues of finite multiplicity; choose exact orthonormal eigenvectors.
  3. At the essential-norm plateau, recursively choose orthonormal approximate
     eigenvectors in spectral windows and orthogonal complements of the
     previously chosen finite span.
  4. Stop when the next leading approximation number is at most `ε`.
  5. Transport the selected right vectors through the polar partial isometry.
     The spectral residual for `|X|` gives both the `X` and `X*` residuals.
  6. If a selected singular value is close to zero, omit it instead; this is
     why the theorem asks only that omitted values be at most `ε`.

  The result is valid for compact and noncompact operators and does not assume
  separability of the ambient spaces: only a finite recursive selection is
  performed.
  -/
  sorry

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
  /- Split `range k` at `count`, identify the first block with `Fin count`,
  and use `tail_small`, nonnegativity, and monotonicity on the tail. -/
  sorry

end FinishTanTwoTheta
end TauCeti
