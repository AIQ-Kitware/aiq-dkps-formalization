/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.Charbonnier
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenBlockSum

/-!
# Exact smoothed spectral-cost additivity in Hilbert space

For a positive smoothing scale, the extended Charbonnier cost is
additive on every bounded rectangular orthogonal block sum, over both
fields in arbitrary Hilbert dimensions. Finite costs have compact
Hilbert--Schmidt blocks; infinite cases follow from the exact native
Hilbert--Schmidt block identity and the correct penalty domain.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped ENNReal

universe u v

variable {𝕜 : Type u} {E F G H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Exact extended Charbonnier block-cost additivity.** No
compactness, finite-dimensional or finite-cost hypothesis is imposed
on the two rectangular Hilbert-space blocks. -/
theorem charbonnierCost_withLpProdMap
    (tau : ℝ) (hτ : 0 < tau) (A : E →L[𝕜] F) (B : G →L[𝕜] H) :
    (A.withLpProdMap 2 B).charbonnierCost tau =
      A.charbonnierCost tau + B.charbonnierCost tau := by
  have heqA := not_congr (charbonnierCost_ne_top_iff_schatten_two tau hτ A)
  have heqB := not_congr (charbonnierCost_ne_top_iff_schatten_two tau hτ B)
  have heqS := not_congr
    (charbonnierCost_ne_top_iff_schatten_two tau hτ (A.withLpProdMap 2 B))
  simp only [not_not] at heqA heqB heqS
  have htop (h : A.charbonnierCost tau = ∞ ∨ B.charbonnierCost tau = ∞) :
      (A.withLpProdMap 2 B).charbonnierCost tau = ∞ := by
    apply heqS.mpr
    apply (ENNReal.rpow_eq_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mp
    rw [TauCeti.OperatorIdealFamily.gauge_schatten_rpow_withLpProdMap 2 (by norm_num)]
    rcases h with h | h
    · rw [heqA.mp h, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2), top_add]
    · rw [heqB.mp h, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2), add_top]
  by_cases hA : A.charbonnierCost tau = ∞
  · rw [htop (Or.inl hA), hA, top_add]
  by_cases hB : B.charbonnierCost tau = ∞
  · rw [htop (Or.inr hB), hB, add_top]
  have hAc := TauCeti.OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2
    (by norm_num) A ((charbonnierCost_ne_top_iff_schatten_two tau hτ A).mp hA)
  have hBc := TauCeti.OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2
    (by norm_num) B ((charbonnierCost_ne_top_iff_schatten_two tau hτ B).mp hB)
  exact tsum_singularValue_penalty_withLpProdMap A B hAc hBc
    (fun s => ENNReal.ofReal (Real.sqrt (tau ^ 2 + (s : ℝ) ^ 2) - tau))
    (by simp [Real.sqrt_sq hτ.le])

end ContinuousLinearMap
