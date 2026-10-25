/-
# Empirical-Gram eigenvalue concentration (pending: loose n/n^2 constants)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/

module

public import Mathlib

/-!
## Comparator maintenance rule

The proof holes in this module are deliberate challenge placeholders. Do not
discharge them in this repository and do not count them as formalization debt.
Implementations belong in the project modules imported by the paired
`Leaderboard.lean`; Comparator verifies that those implementations match these
statements and use only the permitted kernel dependencies.
-/


public section

-- Comparator statement holes are intentional; see Challenge/README.md.
set_option warn.sorry false

open scoped Matrix

namespace TauCeti
open scoped Matrix ENNReal
open MeasureTheory

variable {Ω m n : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [Fintype m] [Fintype n]

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq n] [IsProbabilityMeasure μ]
  {S : Ω → Matrix n n 𝕜} {A : Matrix n n 𝕜} {v η : ℝ}

/-- Entrywise second moments give a simultaneous sorted-eigenvalue floor. -/
theorem one_sub_le_measure_forall_eigenvalues₀_sub_le
    (hS : ∀ ω, (S ω).IsHermitian) (hA : A.IsHermitian)
    (hint : ∀ k l, Integrable (fun ω ↦ ‖S ω k l - A k l‖ ^ 2) μ)
    (hmoment : ∀ k l, ∫ ω, ‖S ω k l - A k l‖ ^ 2 ∂μ ≤ v) (hη : 0 < η) :
    1 - ENNReal.ofReal (Fintype.card n ^ 2 * v / η ^ 2) ≤
      μ {ω | ∀ k, hA.eigenvalues₀ k - Fintype.card n * η ≤ (hS ω).eigenvalues₀ k} := by
  sorry

end TauCeti
