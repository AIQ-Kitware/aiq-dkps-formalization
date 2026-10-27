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

/-- The complementary regime has no finite-cost transporter. This
includes both failure of Hilbert--Schmidt membership and an unbalanced
finite crossed-defect index. The assertion also allows an empty fiber. -/
theorem charbonnier_all_transport_costs_eq_top_iff
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∀ U : H ≃ₗᵢ[𝕜] H, K.map U.toLinearMap = L →
      (1 - (U : H →L[𝕜] H)).charbonnierCost tau = ∞) ↔
    (OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) = ∞ ∨
      Module.finrank 𝕜 (halmosSourceDefect K L) ≠
        Module.finrank 𝕜 (halmosTargetDefect K L) := by
  have h := charbonnier_transport_iff_schatten_two_and_defect_balance tau hτ K L
  classical
  constructor
  · intro htop
    by_contra hfail
    push Not at hfail
    obtain ⟨U, hmap, hfinite⟩ := h.mpr hfail
    exact hfinite (htop U hmap)
  · intro hfail U hmap
    by_contra hfinite
    have hgood := h.mp ⟨U, hmap, hfinite⟩
    exact hfail.elim hgood.1 (fun hne => hne hgood.2)

/-- If finite-cost feasibility fails, every feasible ambient transporter
is an extended-cost global minimizer. No stationarity conclusion follows
in this regime. This statement is valid over both scalar fields. -/
theorem charbonnier_minimal_of_infinite_cost_regime
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hfail : (OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge
        (K.starProjection - L.starProjection) = ∞ ∨
      Module.finrank 𝕜 (halmosSourceDefect K L) ≠
        Module.finrank 𝕜 (halmosTargetDefect K L))
    (U : H ≃ₗᵢ[𝕜] H) (hmap : K.map U.toLinearMap = L) :
    (1 - (U : H →L[𝕜] H)).charbonnierCost tau = ∞ ∧
    ∀ T : H ≃ₗᵢ[𝕜] H, K.map T.toLinearMap = L →
      (1 - (U : H →L[𝕜] H)).charbonnierCost tau ≤
        (1 - (T : H →L[𝕜] H)).charbonnierCost tau := by
  have htop := (charbonnier_all_transport_costs_eq_top_iff tau hτ K L).mpr hfail
  refine ⟨htop U hmap, ?_⟩
  intro T hT
  rw [htop U hmap, htop T hT]

end TauCeti.DavisKahan.InfiniteDimensional
