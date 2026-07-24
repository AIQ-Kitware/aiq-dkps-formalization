/-
# Empirical-Gram eigenvalue concentration (pending: loose n/n^2 constants)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/

import Mathlib

/-!
## Comparator maintenance rule

The proof holes in this module are deliberate challenge placeholders. Do not
discharge them in this repository and do not count them as formalization debt.
Implementations belong in the project modules imported by the paired
`Leaderboard.lean`; Comparator verifies that those implementations match these
statements and use only the permitted kernel dependencies.
-/


open scoped Matrix

namespace TauCeti.Matrix

variable {n : ℕ}

theorem opSym {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    (Matrix.toEuclideanLin B).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr hB

noncomputable def sortedEig {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    Fin n → ℝ :=
  (opSym hB).eigenvalues finrank_euclideanSpace_fin

end TauCeti.Matrix

namespace TauCeti
open scoped Matrix ENNReal
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- **Empirical-Gram eigenvalue lower-bound concentration** (entrywise Chebyshev + Weyl). -/
theorem measure_forall_sortedEig_ge_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hSherm : ∀ ω, (Shat ω).IsHermitian) (hAherm : A.IsHermitian)
    (hmeas : ∀ k l, Measurable (fun ω => Shat ω k l))
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k : Fin n,
        Matrix.sortedEig hAherm k - (n : ℝ) * η ≤ Matrix.sortedEig (hSherm ω) k}
      ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  sorry

end TauCeti