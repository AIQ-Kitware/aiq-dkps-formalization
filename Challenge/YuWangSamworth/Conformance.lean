/-
# Yu--Wang--Samworth population-gap sin-Theta theorem
  (pending comparator challenge)
-/

import Mathlib

/-!
## Comparator maintenance rule

The open proof below is a deliberate challenge placeholder. Do not fill it in
this repository and do not count it as formalization debt. The proof belongs to the
ordinary `YuWangSamworth2015.Core.Residual` implementation imported by the paired
leaderboard.
-/


namespace YuWangSamworth2015
open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {n : ℕ} {T S : E →ₗ[𝕜] E}

/-- Yu--Wang--Samworth's Frobenius sin-Theta bound using only the population
operator's eigengap. -/
theorem sqrt_sum_cross_le_of_population_gap
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n))
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ j ∈ s, ∀ k ∉ s,
      Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2)
      ≤ 2 * Real.sqrt
          (∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2) / Δ := by
  sorry

end YuWangSamworth2015
