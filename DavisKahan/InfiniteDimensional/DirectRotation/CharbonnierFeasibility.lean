/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenFeasibility
public import ForTauCeti.Analysis.OperatorIdeal.Charbonnier

/-!
# Feasibility for the renormalized Charbonnier transport cost

The quadratic behavior at zero makes the Hilbert--Schmidt ideal the
correct domain. At every positive smoothing scale, finite transport
cost is equivalent to a Hilbert--Schmidt projection difference and
balanced finite crossed defects. Both fields and arbitrary Hilbert
dimensions are included; this is feasibility, not minimum attainment.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional

open scoped ENNReal

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- Finite Charbonnier transport cost is feasible precisely on balanced
Hilbert--Schmidt projection pairs, for every positive smoothing scale. -/
theorem charbonnier_transport_iff_schatten_two_and_defect_balance
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃ U : H ≃ₗᵢ[𝕜] H, K.map U.toLinearMap = L ∧
      (1 - (U : H →L[𝕜] H)).charbonnierCost tau ≠ ∞) ↔
    (OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞ ∧
      Module.finrank 𝕜 (halmosSourceDefect K L) =
        Module.finrank 𝕜 (halmosTargetDefect K L) := by
  simp_rw [ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ]
  exact schatten_transport_iff_projection_sub_ne_top_and_defect_balance 2 (by norm_num) K L

end TauCeti.DavisKahan.InfiniteDimensional
