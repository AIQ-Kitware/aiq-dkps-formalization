/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.DirectRotationRank
public import ForTauCeti.Analysis.InnerProductSpace.CompactUnitaryApproximation

/-!
# Compact transport of finite-rank projection pairs

Approximate a compact-displacement transporter by a finite-rank unitary.
Its target is close to the original target, and their projection
difference has finite rank. A small-gap completed rotation corrects the
target with finite-rank displacement. Thus compact feasibility of a
finite-rank pair already implies finite-rank feasibility.

This is classical restricted-unitary geometry. It is the obstruction
step in the infinite-dimensional Schatten optimization theorem, not a
separate historical novelty claim.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open Filter
open scoped Topology

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- Compact-displacement feasibility for a finite-rank projection pair
already supplies a finite-rank-displacement transporter. No separability
or finite rank of the subspaces is assumed. -/
theorem exists_finite_rank_transport_of_compact_transport_of_projection_sub_rank_le
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n)
    (U : H ≃ₗᵢ[𝕜] H) (hmap : K.map U.toLinearMap = L)
    (hU : IsCompactOperator (((U : H →L[𝕜] H) - 1) : H →L[𝕜] H)) :
    ∃ R : H ≃ₗᵢ[𝕜] H, K.map R.toLinearMap = L ∧
      ∃ m : ℕ, (1 - R.toLinearMap).rank ≤ m := by
  obtain ⟨V, N, hN, hlim, _, _, _⟩ := exists_finite_unitary_approximation_sequence U hU
  have hprojlim := (hlim.mul_const K.starProjection).mul hlim.star
  rw [(K.map_eq_iff_conjugate_starProjection L U).mp hmap] at hprojlim
  have hnorm := (hprojlim.sub_const L.starProjection).norm
  simp only [sub_self, norm_zero] at hnorm
  obtain ⟨i, hi⟩ := (hnorm.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
  let L' := K.map (V i).toLinearMap
  have hproj : L'.starProjection =
      (V i : H →L[𝕜] H) * K.starProjection * star (V i : H →L[𝕜] H) :=
    ((K.map_eq_iff_conjugate_starProjection L' (V i)).mp rfl).symm
  have hsmall : L'.projectionGap L < 1 := by
    rw [Submodule.projectionGap_def, hproj]
    exact hi
  obtain ⟨m, hm⟩ :=
    (K.finite_crossedDefect_balance_of_finite_rank_transport L' (V i) rfl (N i) (hN i)).1
  have hdiff : (L'.starProjection - L.starProjection).rank ≤ (m + n : ℕ) := by
    have hfac : (L'.starProjection - L.starProjection).toLinearMap =
        -((K.starProjection - L'.starProjection).toLinearMap) +
          (K.starProjection - L.starProjection).toLinearMap := by
      ext x
      change L'.starProjection x - L.starProjection x =
        -(K.starProjection x - L'.starProjection x) + (K.starProjection x - L.starProjection x)
      abel
    change (L'.starProjection - L.starProjection).toLinearMap.rank ≤ _
    rw [hfac]
    apply (LinearMap.rank_add_le _ _).trans
    have hneg : (-((K.starProjection - L'.starProjection).toLinearMap)).rank =
        (K.starProjection - L'.starProjection).rank := by
      exact congrArg (fun S : Submodule 𝕜 H => Module.rank 𝕜 S)
        (LinearMap.range_neg (K.starProjection - L'.starProjection).toLinearMap)
    rw [hneg]
    simpa only [Nat.cast_add] using add_le_add hm hD
  obtain ⟨T, hTmap, hT⟩ := exists_finite_rank_transport_of_projection_sub_rank_le L' L
    (crossedDefectsEquivalent_of_isAcute L' L (isAcute_of_projectionGap_lt_one hsmall))
    (m + n) hdiff
  let R := (V i).trans T
  refine ⟨R, ?_, (m + n) + N i, ?_⟩
  · change K.map (T.toLinearMap.comp (V i).toLinearMap) = L
    rw [Submodule.map_comp]
    exact hTmap
  · have hfac : 1 - R.toLinearMap = (1 - T.toLinearMap) +
        T.toLinearMap.comp (1 - (V i).toLinearMap) := by
      ext x
      change x - T (V i x) = (x - T x) + T (x - V i x)
      rw [map_sub]
      abel
    rw [hfac]
    apply (LinearMap.rank_add_le _ _).trans
    have hcomp := (LinearMap.rank_comp_le_right (1 - (V i).toLinearMap) T.toLinearMap).trans (hN i)
    simpa only [Nat.cast_add] using add_le_add hT hcomp

/-- A compact-displacement transport of a finite-rank projection pair
forces equality of the finite crossed-defect dimensions. -/
theorem defect_balance_of_compact_transport_of_projection_sub_rank_le
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n)
    (U : H ≃ₗᵢ[𝕜] H) (hmap : K.map U.toLinearMap = L)
    (hU : IsCompactOperator (((U : H →L[𝕜] H) - 1) : H →L[𝕜] H)) :
    Module.finrank 𝕜 (halmosSourceDefect K L) = Module.finrank 𝕜 (halmosTargetDefect K L) := by
  have hfinite := exists_finite_rank_transport_of_compact_transport_of_projection_sub_rank_le
    K L n hD U hmap hU
  exact ((finite_rank_transport_iff_projection_sub_finite_rank_and_defect_balance K L).mp hfinite).2

/-- For a finite-rank projection pair, compact-displacement transport
is feasible exactly when the finite crossed defects are balanced. -/
theorem compact_transport_iff_defect_balance_of_projection_sub_rank_le
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (n : ℕ) (hD : (K.starProjection - L.starProjection).rank ≤ n) :
    (∃ U : H ≃ₗᵢ[𝕜] H, K.map U.toLinearMap = L ∧
      IsCompactOperator (((U : H →L[𝕜] H) - 1) : H →L[𝕜] H)) ↔
    Module.finrank 𝕜 (halmosSourceDefect K L) =
      Module.finrank 𝕜 (halmosTargetDefect K L) := by
  constructor
  · rintro ⟨U, hmap, hU⟩
    exact defect_balance_of_compact_transport_of_projection_sub_rank_le K L n hD U hmap hU
  · intro hbalance
    obtain ⟨R, hmap, hR⟩ :=
      exists_finite_rank_transport_of_projection_sub_rank_le_of_defect_balance K L n hD hbalance
    let : FiniteDimensional 𝕜 (1 - (R : H →L[𝕜] H)).range :=
      Module.rank_lt_aleph0_iff.mp (hR.trans_lt Cardinal.natCast_lt_aleph0)
    have hcompact : IsCompactOperator ((1 - (R : H →L[𝕜] H)) : H →L[𝕜] H) :=
      LinearMap.HasFiniteRange.isCompactOperator (Module.Finite.iff_fg.mp inferInstance)
    refine ⟨R, hmap, ?_⟩
    rw [← neg_sub 1 (R : H →L[𝕜] H)]
    exact hcompact.neg

end TauCeti.DavisKahan
