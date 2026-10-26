/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteTransport
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Finite-rank transport forces finite balanced crossed defects

Localize the transporter to a finite reducing section. The two global
crossed defects lie in that section and identify with its actual crossed
defects. Finite-dimensional projection rank-nullity then proves balance.
This is valid over both fields with no ambient completeness assumption.
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- On an invariant carrier, taking the orthogonal complement of an
intersection agrees with intersecting the ambient orthogonal complement. -/
theorem orthogonal_comap_subtype_eq_comap_orthogonal_of_invariant
    (L M : Submodule 𝕜 E) [L.HasOrthogonalProjection]
    [(L.comap M.subtype).HasOrthogonalProjection]
    (hL : ∀ x ∈ M, L.starProjection x ∈ M) :
    (L.comap M.subtype)ᗮ = Lᗮ.comap M.subtype := by
  ext x
  change x ∈ (L.comap M.subtype)ᗮ ↔ (x : E) ∈ Lᗮ
  rw [← (L.comap M.subtype).starProjection_apply_eq_zero_iff,
    ← L.starProjection_apply_eq_zero_iff]
  have hproj := L.starProjection_comap_subtype_apply_of_invariant M hL x
  constructor
  · intro hx
    have h := congrArg (fun y : M => (y : E)) hx
    change (((L.comap M.subtype).starProjection x : M) : E) = 0 at h
    rwa [hproj] at h
  · intro hx
    apply Subtype.ext
    change (((L.comap M.subtype).starProjection x : M) : E) = 0
    rw [hproj, hx]

/-- The full range of a projection difference lies in any common
reducing core off which the two projections agree. -/
theorem range_projection_sub_le_of_reducing_core
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection]
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hL : M.IsReducing L.starProjection.toLinearMap)
    (heq : ∀ x ∈ Mᗮ, K.starProjection x = L.starProjection x) :
    (K.starProjection - L.starProjection).range ≤ M := by
  rintro _ ⟨x, rfl⟩
  let D := K.starProjection - L.starProjection
  have hzero : D (Mᗮ.starProjection x) = 0 :=
    sub_eq_zero.mpr (heq _ (Mᗮ.starProjection_apply_mem x))
  have hfac : D x = D (M.starProjection x) := by
    calc
      _ = D (M.starProjection x + Mᗮ.starProjection x) :=
        congrArg D (M.starProjection_add_starProjection_orthogonal x).symm
      _ = D (M.starProjection x) + D (Mᗮ.starProjection x) := map_add D _ _
      _ = _ := by rw [hzero, add_zero]
  change D x ∈ M
  rw [hfac]
  exact M.sub_mem (hK.mem_invtSubmodule (M.starProjection_apply_mem x))
    (hL.mem_invtSubmodule (M.starProjection_apply_mem x))

/-- A finite-rank unitary subspace transporter forces a finite-rank
projection difference and finite, equal-dimensional crossed defects.
The subspaces themselves may have infinite rank and corank. -/
theorem finite_crossedDefect_balance_of_finite_rank_transport
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (n : ℕ) (hU : (1 - U.toLinearMap).rank ≤ n) :
    (∃ m : ℕ, (K.starProjection - L.starProjection).rank ≤ m) ∧
      FiniteDimensional 𝕜 (K ⊓ Lᗮ : Submodule 𝕜 E) ∧
      FiniteDimensional 𝕜 (L ⊓ Kᗮ : Submodule 𝕜 E) ∧
      Module.finrank 𝕜 (K ⊓ Lᗮ : Submodule 𝕜 E) =
        Module.finrank 𝕜 (L ⊓ Kᗮ : Submodule 𝕜 E) := by
  obtain ⟨M, hM, _, V, _, hlocal, hK, hL, heq, _⟩ :=
    K.exists_finite_transport_section L ⊥ U hmap n hU
  let : FiniteDimensional 𝕜 M := hM
  have hrange := range_projection_sub_le_of_reducing_core K L M hK hL heq
  have hsource : (K ⊓ Lᗮ : Submodule 𝕜 E) ≤ M := by
    intro x hx
    apply hrange
    refine ⟨x, ?_⟩
    change K.starProjection x - L.starProjection x = x
    rw [K.starProjection_eq_self_iff.mpr hx.1,
      L.starProjection_apply_eq_zero_iff.mpr hx.2, sub_zero]
  have htarget : (L ⊓ Kᗮ : Submodule 𝕜 E) ≤ M := by
    intro x hx
    apply hrange
    refine ⟨-x, ?_⟩
    change K.starProjection (-x) - L.starProjection (-x) = x
    rw [map_neg, map_neg, K.starProjection_apply_eq_zero_iff.mpr hx.2,
      L.starProjection_eq_self_iff.mpr hx.1, neg_zero, zero_sub, neg_neg]
  refine ⟨⟨Module.finrank 𝕜 M, ?_⟩, finiteDimensional_of_le hsource,
    finiteDimensional_of_le htarget, ?_⟩
  · exact (Submodule.rank_mono hrange).trans_eq (Module.finrank_eq_rank (R := 𝕜) M).symm
  · let K₀ := K.comap M.subtype
    let L₀ := L.comap M.subtype
    have hdim := V.toLinearEquiv.finrank_map_eq K₀
    rw [hlocal] at hdim
    have hbalance := K₀.finrank_inf_orthogonal_comm L₀ hdim.symm
    have hsourceEq : K₀ ⊓ L₀ᗮ = (K ⊓ Lᗮ).comap M.subtype := by
      rw [orthogonal_comap_subtype_eq_comap_orthogonal_of_invariant L M hL.mem_invtSubmodule,
        comap_inf]
    have htargetEq : L₀ ⊓ K₀ᗮ = (L ⊓ Kᗮ).comap M.subtype := by
      rw [orthogonal_comap_subtype_eq_comap_orthogonal_of_invariant K M hK.mem_invtSubmodule,
        comap_inf]
    calc
      _ = Module.finrank 𝕜 ((K ⊓ Lᗮ).comap M.subtype) :=
        (comapSubtypeEquivOfLe hsource).finrank_eq.symm
      _ = Module.finrank 𝕜 (K₀ ⊓ L₀ᗮ : Submodule 𝕜 M) :=
        congrArg (fun S : Submodule 𝕜 M => Module.finrank 𝕜 S) hsourceEq.symm
      _ = Module.finrank 𝕜 (L₀ ⊓ K₀ᗮ : Submodule 𝕜 M) := hbalance
      _ = Module.finrank 𝕜 ((L ⊓ Kᗮ).comap M.subtype) :=
        congrArg (fun S : Submodule 𝕜 M => Module.finrank 𝕜 S) htargetEq
      _ = _ := (comapSubtypeEquivOfLe htarget).finrank_eq

end Submodule
