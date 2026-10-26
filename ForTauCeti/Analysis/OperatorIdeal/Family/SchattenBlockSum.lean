/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.CompactBlockTrace
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence
public import TauCeti.Analysis.OperatorIdeal.Family.BlockSum

/-!
# Exact Schatten powers of orthogonal block sums

The native Schatten `p`-power is additive on every bounded orthogonal
block sum, for finite `p>=1`, over both fields in arbitrary Hilbert
dimensions. Infinite costs are included. Finite-cost blocks are compact,
so spectral multiplicity counting applies; if either block has infinite
cost, accepted block compression dominance handles that case directly.
-/

public section

noncomputable section

namespace TauCeti.OperatorIdealFamily

open scoped ENNReal

universe u v

variable {𝕜 : Type u} {E F G H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Exact native Schatten block-power additivity**, with arbitrary
rectangular blocks, both fields and infinite values. No compactness or
finite-dimensional hypothesis is imposed. -/
theorem gauge_schatten_rpow_withLpProdMap
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] F) (B : G →L[𝕜] H) :
    (schatten 𝕜 p hp).gauge (A.withLpProdMap 2 B) ^ p =
      (schatten 𝕜 p hp).gauge A ^ p + (schatten 𝕜 p hp).gauge B ^ p := by
  let Φ := schatten 𝕜 p hp
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hleft : Φ.gauge A ≤ Φ.gauge (A.withLpProdMap 2 B) := by
    simpa only [Φ, schatten_def, SymmetricGauge.operatorIdealFamily_gauge] using
      (SymmetricGauge.lpGauge p hp).opGauge_le_opGauge_withLpProdMap_left (p := 2) A B
  have hright : Φ.gauge B ≤ Φ.gauge (A.withLpProdMap 2 B) := by
    simpa only [Φ, schatten_def, SymmetricGauge.operatorIdealFamily_gauge] using
      (SymmetricGauge.lpGauge p hp).opGauge_le_opGauge_withLpProdMap_right (p := 2) A B
  change Φ.gauge (A.withLpProdMap 2 B) ^ p = Φ.gauge A ^ p + Φ.gauge B ^ p
  by_cases hA : Φ.gauge A = ∞
  · have hblock : Φ.gauge (A.withLpProdMap 2 B) = ∞ := by
      rw [hA] at hleft
      exact top_unique hleft
    rw [hA, hblock, ENNReal.top_rpow_of_pos hp0, top_add]
  by_cases hB : Φ.gauge B = ∞
  · have hblock : Φ.gauge (A.withLpProdMap 2 B) = ∞ := by
      rw [hB] at hright
      exact top_unique hright
    rw [hB, hblock, ENNReal.top_rpow_of_pos hp0, add_top]
  have hAc := isCompactOperator_of_gauge_schatten_ne_top p hp A hA
  have hBc := isCompactOperator_of_gauge_schatten_ne_top p hp B hB
  dsimp only [Φ]
  rw [gauge_schatten_rpow, gauge_schatten_rpow, gauge_schatten_rpow]
  exact ContinuousLinearMap.tsum_singularValue_penalty_withLpProdMap A B hAc hBc
    (fun s => (s : ℝ≥0∞) ^ p) (ENNReal.zero_rpow_of_pos hp0)

end TauCeti.OperatorIdealFamily
