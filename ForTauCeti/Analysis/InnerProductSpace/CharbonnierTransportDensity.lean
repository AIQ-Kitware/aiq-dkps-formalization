/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenTransportDensity
public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierInfiniteLocal
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport

/-!
# Finite-cost density in compact-displacement transport fibers

A compact-displacement transporter can be approximated in operator norm,
inside the exact transport fiber, by finite-rank updates of any finite-cost
reference. Consequently a compact-displacement local minimum has finite
cost whenever finite cost is feasible. No native trace continuity is used.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped ENNReal Topology TauCeti.LinearIsometryEquivOperatorNorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Exact finite-cost transporters are dense in the compact-displacement
part of any fiber admitting finite cost. Approximants are finite-rank
updates of the reference, with explicit finite rank bounds. Both fields
and arbitrary Hilbert dimensions are included. -/
theorem exists_charbonnier_transport_finite_update_sequence
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R U : E ≃ₗᵢ[𝕜] E) (hRmap : K.map R.toLinearMap = L)
    (hUmap : K.map U.toLinearMap = L)
    (hRfinite : (1 - (R : E →L[𝕜] E)).charbonnierCost tau ≠ ∞)
    (hUcompact : IsCompactOperator ((1 - (U : E →L[𝕜] E)) : E →L[𝕜] E)) :
    ∃ V : ℕ → E ≃ₗᵢ[𝕜] E, ∃ N : ℕ → ℕ,
      (∀ n, K.map (V n).toLinearMap = L) ∧
      (∀ n, (1 - (V n : E →L[𝕜] E)).charbonnierCost tau ≠ ∞) ∧
      (∀ n, ((R : E →L[𝕜] E) - (V n : E →L[𝕜] E)).rank ≤ N n) ∧
      Tendsto V atTop (𝓝 U) := by
  have hRhs := (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hRfinite
  have hRc := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) (1 - (R : E →L[𝕜] E)) hRhs
  have hUR : IsCompactOperator
      (((U : E →L[𝕜] E) - (R : E →L[𝕜] E)) : E →L[𝕜] E) := by
    have hfac : (U : E →L[𝕜] E) - (R : E →L[𝕜] E) =
        -(1 - (U : E →L[𝕜] E)) + (1 - (R : E →L[𝕜] E)) := by abel
    rw [hfac]
    exact hUcompact.neg.add hRc
  obtain ⟨V, N, hVP, hVfinite, hN, hlim⟩ :=
    exists_schatten_transport_finite_update_sequence_of_compact 2 (by norm_num)
      K.starProjection L.starProjection R U hRhs hUR
      ((K.map_eq_iff_conjugate_starProjection L R).mp hRmap)
      ((K.map_eq_iff_conjugate_starProjection L U).mp hUmap)
  refine ⟨V, N, fun n => (K.map_eq_iff_conjugate_starProjection L (V n)).mpr (hVP n),
    ?_, hN, ?_⟩
  · intro n
    apply (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mpr
    exact hVfinite n
  · exact hlim

/-- Within a fiber admitting finite native cost, a local minimum with
compact displacement necessarily has finite cost. A merely compact,
non-Hilbert--Schmidt displacement cannot be an infinite-cost local minimum. -/
theorem charbonnierCost_displacement_ne_top_of_isLocalMinOn_of_compact
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R U : E ≃ₗᵢ[𝕜] E) (hRmap : K.map R.toLinearMap = L)
    (hUmap : K.map U.toLinearMap = L)
    (hRfinite : (1 - (R : E →L[𝕜] E)).charbonnierCost tau ≠ ∞)
    (hUcompact : IsCompactOperator ((1 - (U : E →L[𝕜] E)) : E →L[𝕜] E))
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[𝕜] E => (1 - (T : E →L[𝕜] E)).charbonnierCost tau)
      {T | K.map T.toLinearMap = L} U) :
    (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≠ ∞ := by
  obtain ⟨V, _, hVmap, hVfinite, _, hlim⟩ :=
    exists_charbonnier_transport_finite_update_sequence tau hτ K L R U
      hRmap hUmap hRfinite hUcompact
  have hwithin : Tendsto V atTop (𝓝[{T | K.map T.toLinearMap = L}] U) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hVmap⟩
  have hbound : ∀ᶠ n in atTop,
      (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≤
        (1 - (V n : E →L[𝕜] E)).charbonnierCost tau := hwithin hmin
  obtain ⟨n, hn⟩ := hbound.exists
  exact ne_top_of_le_ne_top (hVfinite n) hn

end TauCeti
