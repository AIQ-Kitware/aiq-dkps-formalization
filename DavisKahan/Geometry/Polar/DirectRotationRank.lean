/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.PairedPhase
public import DavisKahan.Geometry.Halmos.CrossedDefectGap
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteTransportDefects
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Finite-rank direct rotations from finite-rank projection differences

A completed direct rotation fixes the kernel of the projection
difference. Factoring its displacement through that kernel quotient
therefore bounds its rank by the rank of the projection difference.
Balanced crossed defects then give a finite-rank feasible reference,
without assuming the subspaces themselves are finite-dimensional.

These are classical pair-of-projections consequences, used to state the
new optimization results directly in terms of the projection pair.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The displacement rank of any completed canonical rotation is at
most the rank of the projection difference, in arbitrary dimension. -/
theorem rank_one_sub_nonacuteDirectRotation_le_projection_sub
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    (1 - nonacuteDirectRotation K L J).rank ≤ (K.starProjection - L.starProjection).rank := by
  let A := (1 - nonacuteDirectRotation K L J).toLinearMap
  let D := (K.starProjection - L.starProjection).toLinearMap
  have hker : D.ker ≤ A.ker := by
    intro x hx
    change K.starProjection x - L.starProjection x = 0 at hx
    change x - nonacuteDirectRotation K L J x = 0
    rw [nonacuteDirectRotation_apply_eq_self_of_projections_eq K L J x (sub_eq_zero.mp hx),
      sub_self]
  let T := D.ker.liftQ A hker
  have hrange : T.range = A.range := D.ker.range_liftQ A hker
  calc
    A.rank = T.rank := by change Module.rank 𝕜 A.range = Module.rank 𝕜 T.range; rw [hrange]
    _ ≤ Module.rank 𝕜 (H ⧸ D.ker) := T.rank_le_domain
    _ = D.rank := D.quotKerEquivRange.rank_eq

/-- Finite-rank projection difference and a crossed-defect
identification supply an actual finite-rank ambient unitary transport. -/
theorem exists_finite_rank_transport_of_projection_sub_rank_le
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hdefect : CrossedDefectsEquivalent K L)
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n) :
    ∃ R : H ≃ₗᵢ[𝕜] H, K.map R.toLinearMap = L ∧ (1 - R.toLinearMap).rank ≤ n := by
  obtain ⟨J⟩ := hdefect
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (H →L[𝕜] H))
  refine ⟨R, ?_, ?_⟩
  · apply (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
    exact nonacuteDirectRotation_reflection_intertwines K L J
  · have hlin : 1 - R.toLinearMap = (1 - nonacuteDirectRotation K L J).toLinearMap := by
      ext x
      rfl
    rw [hlin]
    exact (rank_one_sub_nonacuteDirectRotation_le_projection_sub K L J).trans hD

omit [CompleteSpace H] in
/-- Both crossed defect spaces are finite-dimensional when the
projection difference has finite rank. No dimension of the ambient space
or the subspaces is assumed. -/
theorem finiteDimensional_crossedDefects_of_projection_sub_rank_le
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n) :
    FiniteDimensional 𝕜 (halmosSourceDefect K L) ∧
      FiniteDimensional 𝕜 (halmosTargetDefect K L) := by
  let D := (K.starProjection - L.starProjection).toLinearMap
  let : FiniteDimensional 𝕜 D.range := Module.rank_lt_aleph0_iff.mp
    (hD.trans_lt Cardinal.natCast_lt_aleph0)
  have hsource : halmosSourceDefect K L ≤ D.range := by
    intro x hx
    refine ⟨x, ?_⟩
    change K.starProjection x - L.starProjection x = x
    rw [K.starProjection_eq_self_iff.mpr hx.1,
      L.starProjection_apply_eq_zero_iff.mpr hx.2, sub_zero]
  have htarget : halmosTargetDefect K L ≤ D.range := by
    intro x hx
    refine ⟨-x, ?_⟩
    change K.starProjection (-x) - L.starProjection (-x) = x
    rw [map_neg, map_neg, K.starProjection_apply_eq_zero_iff.mpr hx.1,
      L.starProjection_eq_self_iff.mpr hx.2, neg_zero, zero_sub, neg_neg]
  exact ⟨Submodule.finiteDimensional_of_le hsource, Submodule.finiteDimensional_of_le htarget⟩

/-- Equal finite crossed-defect dimensions suffice for a finite-rank
unitary transport when the projection difference has finite rank. -/
theorem exists_finite_rank_transport_of_projection_sub_rank_le_of_defect_balance
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n)
    (hbalance : Module.finrank 𝕜 (halmosSourceDefect K L) =
      Module.finrank 𝕜 (halmosTargetDefect K L)) :
    ∃ R : H ≃ₗᵢ[𝕜] H, K.map R.toLinearMap = L ∧ (1 - R.toLinearMap).rank ≤ n := by
  obtain ⟨hsource, htarget⟩ := finiteDimensional_crossedDefects_of_projection_sub_rank_le K L n hD
  let : FiniteDimensional 𝕜 (halmosSourceDefect K L) := hsource
  let : FiniteDimensional 𝕜 (halmosTargetDefect K L) := htarget
  exact exists_finite_rank_transport_of_projection_sub_rank_le K L
    ((crossedDefectsEquivalent_iff_finrank_eq K L).mpr hbalance) n hD

/-- **Finite-rank transport feasibility.** A pair is in one orbit of the
finite-rank restricted unitary group exactly when its projection
difference has finite rank and its finite crossed defects are balanced.
Both scalar fields and arbitrary ambient Hilbert dimensions are allowed. -/
theorem finite_rank_transport_iff_projection_sub_finite_rank_and_defect_balance
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃ R : H ≃ₗᵢ[𝕜] H, K.map R.toLinearMap = L ∧
      ∃ n : ℕ, (1 - R.toLinearMap).rank ≤ n) ↔
    (∃ n : ℕ, (K.starProjection - L.starProjection).rank ≤ n) ∧
      Module.finrank 𝕜 (halmosSourceDefect K L) =
        Module.finrank 𝕜 (halmosTargetDefect K L) := by
  constructor
  · rintro ⟨R, hmap, n, hR⟩
    obtain ⟨hD, _, _, hbalance⟩ :=
      K.finite_crossedDefect_balance_of_finite_rank_transport L R hmap n hR
    refine ⟨hD, ?_⟩
    change Module.finrank 𝕜 (K ⊓ Lᗮ : Submodule 𝕜 H) =
      Module.finrank 𝕜 (Kᗮ ⊓ L : Submodule 𝕜 H)
    rwa [inf_comm Kᗮ L]
  · rintro ⟨⟨n, hD⟩, hbalance⟩
    obtain ⟨R, hmap, hR⟩ :=
      exists_finite_rank_transport_of_projection_sub_rank_le_of_defect_balance K L n hD hbalance
    exact ⟨R, hmap, n, hR⟩

end TauCeti.DavisKahan
