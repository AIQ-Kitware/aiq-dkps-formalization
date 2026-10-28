/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenFeasibility
public import ForTauCeti.Analysis.OperatorIdeal.SmoothedPower

/-!
# The common penalty family's finite-cost transport domain

Positive smoothing has the Hilbert--Schmidt domain; zero smoothing has the
native Schatten domain. In both cases the existing restricted-unitary
feasibility theorem supplies exactly the defect-balance condition. This
module reuses that theorem rather than introducing a second index argument.

The relative index and restricted-unitary feasibility ingredients are
classical; the precise primary-source comparisons are S6/S11 and T10 in
`dev/spectral-transport-unification.md`. These are feasibility statements,
not a real-field optimization reduction or claims of first priority.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPowerTransport

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **Positive-smoothing finite-cost feasibility over either field.**
Projection Hilbert--Schmidt membership and balanced crossed defects are
jointly necessary and sufficient, in arbitrary Hilbert dimension. -/
theorem transport_iff_schatten_two_and_defect_balance (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃ U : E ≃ₗᵢ[𝕜] E, K.map U.toLinearMap = L ∧
      (1 - (U : E →L[𝕜] E)).smoothedPowerCost p tau ≠ ∞) ↔
      (OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge
        (K.starProjection - L.starProjection) ≠ ∞ ∧
      Module.finrank 𝕜 (halmosSourceDefect K L) =
        Module.finrank 𝕜 (halmosTargetDefect K L) := by
  simp_rw [ContinuousLinearMap.smoothedPowerCost_ne_top_iff_schatten_two p tau
    (by linarith) hp2 htau]
  exact schatten_transport_iff_projection_sub_ne_top_and_defect_balance 2 (by norm_num) K L

/-- At zero smoothing the finite-cost domain is Schatten p, with the
same actual crossed-defect balance condition. -/
theorem zero_smoothing_transport_iff_schatten_and_defect_balance (p : ℝ) (hp : 1 ≤ p)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃ U : E ≃ₗᵢ[𝕜] E, K.map U.toLinearMap = L ∧
      (1 - (U : E →L[𝕜] E)).smoothedPowerCost p 0 ≠ ∞) ↔
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (K.starProjection - L.starProjection) ≠ ∞ ∧
      Module.finrank 𝕜 (halmosSourceDefect K L) =
        Module.finrank 𝕜 (halmosTargetDefect K L) := by
  simp_rw [ContinuousLinearMap.smoothedPowerCost_zero_smoothing p hp,
    not_congr (ENNReal.rpow_eq_top_iff_of_pos (by linarith : 0 < p))]
  exact schatten_transport_iff_projection_sub_ne_top_and_defect_balance p hp K L

/-- Canonical rotation has finite family cost exactly when the projection
difference has finite family cost. The established native-ideal equivalence
supplies both smoothing regimes; no new index argument is used. -/
theorem nonacuteDirectRotation_cost_ne_top_iff_projection_sub (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    (1 - nonacuteDirectRotation K L J).smoothedPowerCost p tau ≠ ∞ ↔
      (K.starProjection - L.starProjection).smoothedPowerCost p tau ≠ ∞ := by
  by_cases hz : tau = 0
  · subst tau
    simp_rw [ContinuousLinearMap.smoothedPowerCost_zero_smoothing p hp,
      not_congr (ENNReal.rpow_eq_top_iff_of_pos (by linarith : 0 < p))]
    exact gauge_nonacuteDirectRotation_ne_top_iff_projection_sub
      (OperatorIdealFamily.schatten 𝕜 p hp) K L J
  · simp_rw [ContinuousLinearMap.smoothedPowerCost_ne_top_iff_schatten_two p tau
      (by linarith) hp2 (lt_of_le_of_ne htau (Ne.symm hz))]
    exact gauge_nonacuteDirectRotation_ne_top_iff_projection_sub
      (OperatorIdealFamily.schatten 𝕜 2 (by norm_num)) K L J

/-- **A common feasibility statement for the full closed family.**
Finite projection penalty and balanced crossed defects are exactly the
conditions for a finite-cost ambient transporter over either field. -/
theorem transport_iff_projection_cost_and_defect_balance (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃ U : E ≃ₗᵢ[𝕜] E, K.map U.toLinearMap = L ∧
      (1 - (U : E →L[𝕜] E)).smoothedPowerCost p tau ≠ ∞) ↔
      (K.starProjection - L.starProjection).smoothedPowerCost p tau ≠ ∞ ∧
      Module.finrank 𝕜 (halmosSourceDefect K L) =
        Module.finrank 𝕜 (halmosTargetDefect K L) := by
  by_cases hz : tau = 0
  · subst tau
    simp_rw [ContinuousLinearMap.smoothedPowerCost_zero_smoothing p hp,
      not_congr (ENNReal.rpow_eq_top_iff_of_pos (by linarith : 0 < p))]
    exact schatten_transport_iff_projection_sub_ne_top_and_defect_balance p hp K L
  · simp_rw [ContinuousLinearMap.smoothedPowerCost_ne_top_iff_schatten_two p tau
      (by linarith) hp2 (lt_of_le_of_ne htau (Ne.symm hz))]
    exact schatten_transport_iff_projection_sub_ne_top_and_defect_balance 2 (by norm_num) K L

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPowerTransport
