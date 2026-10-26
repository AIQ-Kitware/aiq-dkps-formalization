/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.DirectRotationIdeal
public import DavisKahan.Geometry.Halmos.CompactDefects
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence

/-!
# Schatten restricted-unitary feasibility and the defect obstruction

The projection difference belongs to the Schatten ideal and its finite
crossed defects are balanced exactly when a Schatten-displacement
unitary transport exists. If balance fails, every ambient transporter
has infinite Schatten cost. Both fields and arbitrary Hilbert dimension
are included, without a finite-rank assumption.

The necessity uses accepted Fredholm theory for the rectangular
projection; sufficiency uses the bounded canonical displacement factor.
This is the classical index obstruction, not an independent novelty claim.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional

open scoped ENNReal

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **General Schatten transport feasibility.** A Schatten-displacement
unitary transports the pair exactly when its projection difference is
in that same ideal and the finite crossed defects are balanced. Both
fields and arbitrary Hilbert dimensions are included. -/
theorem schatten_transport_iff_projection_sub_ne_top_and_defect_balance
    (p : ℝ) (hp : 1 ≤ p)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃ U : H ≃ₗᵢ[𝕜] H, K.map U.toLinearMap = L ∧
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : H →L[𝕜] H)) ≠ ∞) ↔
    (OperatorIdealFamily.schatten 𝕜 p hp).gauge (K.starProjection - L.starProjection) ≠ ∞ ∧
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
    refine ⟨ne_top_of_le_ne_top hU (Φ.gauge_projection_sub_le_unitary_displacement K L U hmap), ?_⟩
    have hbalance := (K.finite_crossedDefect_balance_of_compact_transport L U hmap hcompact).2.2
    change Module.finrank 𝕜 (K ⊓ Lᗮ : Submodule 𝕜 H) =
      Module.finrank 𝕜 (Kᗮ ⊓ L : Submodule 𝕜 H)
    rwa [inf_comm Kᗮ L]
  · rintro ⟨hD, hbalance⟩
    have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p hp
      (K.starProjection - L.starProjection) hD
    obtain ⟨J⟩ :=
      crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq K L hcompact hbalance
    let U := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
        unitary (H →L[𝕜] H))
    refine ⟨U, ?_, (gauge_nonacuteDirectRotation_ne_top_iff_projection_sub
      (OperatorIdealFamily.schatten 𝕜 p hp) K L J).mpr hD⟩
    apply (Submodule.map_eq_iff_intertwines_reflection K L U).mpr
    exact nonacuteDirectRotation_reflection_intertwines K L J

/-- A defect imbalance forces infinite displacement cost for every
ambient transporter at every finite Schatten exponent. This includes
ambient unitary equivalence that cannot be realized near identity. -/
theorem schatten_transport_eq_top_of_defect_imbalance
    (p : ℝ) (hp : 1 ≤ p)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (himbalance : Module.finrank 𝕜 (halmosSourceDefect K L) ≠
      Module.finrank 𝕜 (halmosTargetDefect K L))
    (U : H ≃ₗᵢ[𝕜] H) (hmap : K.map U.toLinearMap = L) :
    (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : H →L[𝕜] H)) = ∞ := by
  by_contra hfinite
  exact himbalance ((schatten_transport_iff_projection_sub_ne_top_and_defect_balance
    p hp K L).mp ⟨U, hmap, hfinite⟩).2

end TauCeti.DavisKahan.InfiniteDimensional
