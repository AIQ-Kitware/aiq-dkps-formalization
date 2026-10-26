/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.CompactTransportFinitePairs
public import DavisKahan.Geometry.Polar.DirectRotationIdeal
public import DavisKahan.Geometry.Halmos.CompactDefects
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite

/-!
# Schatten feasibility and the defect obstruction for finite-rank pairs

For finite-rank projection perturbations, the finite crossed-defect
balance is equivalent to feasibility in every finite Schatten restricted
unitary group. If balance fails, every ambient transporter has infinite
Schatten cost. Both fields and arbitrary Hilbert dimension are included.

This is the classical index obstruction specialized to finite-rank
projection differences, proved by compact approximation and a small-gap
target correction rather than by introducing a separate Fredholm index.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional

open scoped ENNReal

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- A general Schatten projection difference with balanced finite
crossed defects admits a Schatten-displacement unitary transport.
Unlike the finite-rank feasibility iff below, the projection difference
may have infinite rank. -/
theorem exists_schatten_transport_of_projection_sub_ne_top_of_defect_balance
    (p : ℝ) (hp : 1 ≤ p)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : (OperatorIdealFamily.schatten 𝕜 p hp).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (hbalance : Module.finrank 𝕜 (halmosSourceDefect K L) =
      Module.finrank 𝕜 (halmosTargetDefect K L)) :
    ∃ U : H ≃ₗᵢ[𝕜] H, K.map U.toLinearMap = L ∧
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : H →L[𝕜] H)) ≠ ∞ := by
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p hp
    (K.starProjection - L.starProjection) hD
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq K L hcompact hbalance
  let U := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (H →L[𝕜] H))
  refine ⟨U, ?_, (gauge_nonacuteDirectRotation_ne_top_iff_projection_sub
    (OperatorIdealFamily.schatten 𝕜 p hp) K L J).mpr hD⟩
  apply (Submodule.map_eq_iff_intertwines_reflection K L U).mpr
  exact nonacuteDirectRotation_reflection_intertwines K L J

/-- For a finite-rank projection pair, feasibility at any finite
Schatten exponent is exactly finite crossed-defect balance. In
particular the feasibility condition does not depend on that exponent. -/
theorem schatten_transport_iff_defect_balance_of_projection_sub_rank_le
    (p : ℝ) (hp : 1 ≤ p)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n) :
    (∃ U : H ≃ₗᵢ[𝕜] H, K.map U.toLinearMap = L ∧
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : H →L[𝕜] H)) ≠ ∞) ↔
    Module.finrank 𝕜 (halmosSourceDefect K L) =
      Module.finrank 𝕜 (halmosTargetDefect K L) := by
  constructor
  · rintro ⟨U, hmap, hU⟩
    let Φ := OperatorIdealFamily.schatten 𝕜 p hp
    have hU' : Φ.gauge ((U : H →L[𝕜] H) - 1) ≠ ∞ := by
      rw [← neg_sub 1 (U : H →L[𝕜] H), Φ.gauge_neg]
      exact hU
    have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p hp
      (((U : H →L[𝕜] H) - 1) : H →L[𝕜] H) hU'
    exact defect_balance_of_compact_transport_of_projection_sub_rank_le K L n hD U hmap hcompact
  · intro hbalance
    obtain ⟨R, hmap, hR⟩ :=
      exists_finite_rank_transport_of_projection_sub_rank_le_of_defect_balance K L n hD hbalance
    exact ⟨R, hmap, OperatorIdealFamily.gauge_schatten_ne_top_of_rank_le p hp
      (1 - (R : H →L[𝕜] H)) n hR⟩

/-- A defect imbalance forces infinite displacement cost for every
ambient transporter at every finite Schatten exponent. This includes
ambient unitary equivalence that cannot be realized near identity. -/
theorem schatten_transport_eq_top_of_defect_imbalance
    (p : ℝ) (hp : 1 ≤ p)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n)
    (himbalance : Module.finrank 𝕜 (halmosSourceDefect K L) ≠
      Module.finrank 𝕜 (halmosTargetDefect K L))
    (U : H ≃ₗᵢ[𝕜] H) (hmap : K.map U.toLinearMap = L) :
    (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : H →L[𝕜] H)) = ∞ := by
  by_contra hfinite
  exact himbalance ((schatten_transport_iff_defect_balance_of_projection_sub_rank_le
    p hp K L n hD).mp ⟨U, hmap, hfinite⟩)

end TauCeti.DavisKahan.InfiniteDimensional
