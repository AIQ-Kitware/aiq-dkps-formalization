/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierOptimizerClassification
public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierInfiniteLocal

/-!
# No nonglobal finite-cost Hilbert Charbonnier local minima

Local stationarity, actual finite reducing restrictions and finite
landscape rigidity force canonical action on the entire inactive tail.
The complete finite-cutoff optimizer iff then proves global optimality
against every ambient competitor. Native finite cost is essential:
infinite-cost nonglobal local plateaus are proved separately.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **No finite-cost spurious local minima.** On any complete complex
Hilbert space, every finite-cost operator-norm local minimum of native
Charbonnier transport is globally minimizing over all ambient unitaries.
There is no separability, finite-rank, prescribed-block or index hypothesis.
Finite-cost feasibility itself supplies the ideal and index conditions. -/
theorem charbonnier_isMin_of_isLocalMinOn_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
      {T | K.map T.toLinearMap = L} U) :
    ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau := by
  obtain ⟨hD, hbalance⟩ :=
    (charbonnier_transport_iff_schatten_two_and_defect_balance tau hτ K L).mp ⟨U, hmap, hfinite⟩
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) (K.starProjection - L.starProjection) hD
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq
    K L hcompact hbalance
  let c := Real.sin (smoothedCriticalAngle tau) / 2
  have hangle := smoothedCriticalAngle_mem tau hτ
  have hsin : 0 < Real.sin (smoothedCriticalAngle tau) :=
    Real.sin_pos_of_pos_of_lt_pi hangle.1 (by linarith [hangle.2, Real.pi_pos])
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : c < 1 := by dsimp only [c]; linarith [Real.sin_le_one (smoothedCriticalAngle tau)]
  have hcrit : c ≤ Real.sin (smoothedCriticalAngle tau) := by dsimp only [c]; linarith
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  obtain ⟨hM, hK, _, _⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  have hUS := commute_sinAngleOperator_of_charbonnier_isLocalMinOn_complex
    tau hτ K L U hmap hfinite hmin
  have hUM : ∀ x ∈ M, U x ∈ M :=
    eigenSpan_invariant_of_commute (K.sinAngleOperator L) _ hUS _
  obtain ⟨V, hV, hVmap, _, hVmin⟩ := exists_charbonnier_locally_minimizing_finite_restriction
    tau hτ K L M U hmap hfinite hmin hK hUM
  have htail := apply_eq_nonacuteDirectRotation_on_inactive_tail_of_charbonnier_isLocalMinOn_complex
    tau hτ K L J hD c hc hc1 hcrit U hmap hfinite hmin
  exact (charbonnier_minimal_iff_canonical_tail_finite_minimal_complex
    tau hτ K L J hD c hc hc1 hcrit U hmap).mpr
      ⟨htail, V, hV, hVmap, smoothed_isMin_of_charbonnier_isLocalMinOn_complex
        tau hτ (K.comap M.subtype) (L.comap M.subtype) V hVmap hVmin⟩

/-- Native local and global optimality coincide exactly on the finite
cost part of the transport fiber, in operator-norm topology. -/
theorem charbonnier_isLocalMinOn_iff_isMinOn_of_finite_cost_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞) :
    IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
      {T | K.map T.toLinearMap = L} U ↔
    IsMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
      {T | K.map T.toLinearMap = L} U := by
  constructor
  · intro hmin
    exact fun T hT => charbonnier_isMin_of_isLocalMinOn_complex tau hτ K L U hmap hfinite hmin T hT
  · exact IsMinOn.isLocalMinOn

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
