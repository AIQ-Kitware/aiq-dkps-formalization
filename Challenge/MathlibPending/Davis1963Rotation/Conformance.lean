/-
# Davis 1963 sharper total-rotation theorem (pending comparator challenge)
-/

/-!
## Comparator maintenance rule

The open proof below is a deliberate challenge placeholder. Do not fill it in
this repository and do not count it as formalization debt. The proof belongs to the
ordinary `ForMathlib` implementation imported by the paired leaderboard.
-/

import Mathlib

namespace ForMathlib

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {n : ℕ} {T S : E →ₗ[𝕜] E}

/-- Davis's 1963 Theorem 3.2: eigenvalue displacement and eigenvector rotation
share the same Frobenius perturbation budget. -/
theorem rotation_add_displacement_le_hilbertSchmidt
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {γ' : ℝ}
    (hsep : ∀ i j, i ≠ j →
      γ' ^ 2 + (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
        ≤ (hT.eigenvalues hn i - hS.eigenvalues hn j) ^ 2) :
    γ' ^ 2 * ∑ i,
        (1 - ‖⟪hS.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫_𝕜‖ ^ 2)
        + ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      ≤ ∑ i, ‖(S - T) (hT.eigenvectorBasis hn i)‖ ^ 2 := by
  sorry

end ForMathlib
