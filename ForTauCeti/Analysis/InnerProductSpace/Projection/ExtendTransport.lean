/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction
public import ForTauCeti.Analysis.InnerProductSpace.Projection.InvariantSubspace
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport
public import ForTauCeti.Analysis.OperatorIdeal.OrthogonalExtension

/-!
# Extending a subspace transport by identity

A unitary transport on a common reducing block extends by identity to
an ambient transport when the projections agree on the complement.
The displacement is exactly its orthogonal zero extension. The block
and ambient spaces may both be infinite-dimensional.
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Extend a transporter by identity on a complementary block where
the source and target projections agree. This preserves its complete
displacement spectrum by orthogonal zero extension. -/
theorem exists_transport_extension_by_identity
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection]
    [(K.comap M.subtype).HasOrthogonalProjection]
    [(L.comap M.subtype).HasOrthogonalProjection]
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hL : M.IsReducing L.starProjection.toLinearMap)
    (heq : ∀ x ∈ Mᗮ, K.starProjection x = L.starProjection x)
    (V : M ≃ₗᵢ[𝕜] M)
    (hV : (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype) :
    ∃ U : E ≃ₗᵢ[𝕜] E, K.map U.toLinearMap = L ∧
      (∀ x : M, U x = (V x : E)) ∧ (∀ x ∈ Mᗮ, U x = x) ∧
      1 - (U : E →L[𝕜] E) = M.subtypeL ∘L
        (1 - (V : M →L[𝕜] M)) ∘L M.orthogonalProjectionOnto := by
  obtain ⟨U, hUM, hUperp⟩ :=
    M.exists_unitary_orthogonal_sum V (LinearIsometryEquiv.refl 𝕜 Mᗮ)
  have hfix (x : E) (hx : x ∈ Mᗮ) : U x = x := hUperp ⟨x, hx⟩
  have hlocal (x : M) : V ((K.comap M.subtype).starProjection x) =
      (L.comap M.subtype).starProjection (V x) := by
    have h := starProjection_map_apply V (K.comap M.subtype) (V x)
    simpa only [hV, V.symm_apply_apply] using h.symm
  have hinterM (x : E) (hx : x ∈ M) : U (K.starProjection x) = L.starProjection (U x) := by
    let y : M := ⟨x, hx⟩
    calc
      _ = U (((K.comap M.subtype).starProjection y : M) : E) := by
        rw [K.starProjection_comap_subtype_apply_of_invariant M hK.mem_invtSubmodule]
      _ = (V ((K.comap M.subtype).starProjection y) : E) := hUM _
      _ = (((L.comap M.subtype).starProjection (V y) : M) : E) :=
        congrArg Subtype.val (hlocal y)
      _ = L.starProjection (V y : E) :=
        L.starProjection_comap_subtype_apply_of_invariant M hL.mem_invtSubmodule _
      _ = _ := congrArg L.starProjection (hUM y).symm
  have hinterPerp (x : E) (hx : x ∈ Mᗮ) :
      U (K.starProjection x) = L.starProjection (U x) := by
    rw [hfix x hx]
    exact (hfix (K.starProjection x) (hK.orthogonal_mem_invtSubmodule hx)).trans (heq x hx)
  have hinter (x : E) : U (K.starProjection x) = L.starProjection (U x) := by
    calc
      _ = U (K.starProjection (M.starProjection x + Mᗮ.starProjection x)) := by
        rw [M.starProjection_add_starProjection_orthogonal]
      _ = L.starProjection (U (M.starProjection x)) +
          L.starProjection (U (Mᗮ.starProjection x)) := by
        rw [map_add, map_add, hinterM _ (M.starProjection_apply_mem x),
          hinterPerp _ (Mᗮ.starProjection_apply_mem x)]
      _ = _ := by rw [← map_add, ← map_add, M.starProjection_add_starProjection_orthogonal]
  refine ⟨U, ?_, hUM, hfix, ?_⟩
  · apply (map_eq_iff_intertwines_reflection K L U).mpr
    intro x
    rw [K.reflection_apply, L.reflection_apply, map_sub, map_nsmul, hinter]
  · apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
    constructor
    · intro x
      change (x : E) - U x = (x : E) - (V x : E)
      rw [hUM]
    · intro x hx
      change x - U x = 0
      rw [hfix x hx, sub_self]

end Submodule
