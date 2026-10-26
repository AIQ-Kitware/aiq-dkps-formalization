/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.ExtendTransport
public import ForTauCeti.Analysis.InnerProductSpace.ReducingUnitaryRestriction

/-!
# Replacing a finite block of an ambient unitary transport

On a finite source-reducing block invariant under a given transporter,
replace its action by any transporter of the actual restricted pair.
The ambient transport constraint remains exact, the complementary
action is unchanged, and the update rank is at most the block dimension.
No compactness or displacement-ideal assumption is needed.
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Replace an arbitrary reducing block of an ambient transport,
keeping its complete complementary action. Both blocks may be infinite. -/
theorem exists_transport_replacing_reducing_block
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] [CompleteSpace M]
    [(K.comap M.subtype).HasOrthogonalProjection]
    [(L.comap M.subtype).HasOrthogonalProjection]
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (R : E ≃ₗᵢ[𝕜] E) (hRmap : K.map R.toLinearMap = L)
    (hRM : M.IsReducing R.toLinearMap)
    (W : M ≃ₗᵢ[𝕜] M)
    (hW : (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype) :
    ∃ U : E ≃ₗᵢ[𝕜] E, K.map U.toLinearMap = L ∧
      (∀ x : M, U x = (W x : E)) ∧ (∀ x ∈ Mᗮ, U x = R x) := by
  obtain ⟨V, hV, _⟩ := R.exists_restriction_of_reducing M hRM
  have hVmap := K.map_comap_subtype_of_isometry_restriction L M R V hRmap hV
  let B := W.trans V.symm
  have hBmap : (K.comap M.subtype).map B.toLinearMap = K.comap M.subtype := by
    apply (map_eq_iff_intertwines_reflection _ _ B).mpr
    exact relative_transport_commutes_reflection _ _ W V hW hVmap
  obtain ⟨C, hCmap, hCM, hCperp, hdisp⟩ :=
    K.exists_transport_extension_by_identity K M hK hK (fun _ _ => rfl) B hBmap
  let U := C.trans R
  have hUmap : K.map U.toLinearMap = L := by
    change K.map (R.toLinearMap.comp C.toLinearMap) = L
    rw [map_comp, hCmap]
    exact hRmap
  have hUM (x : M) : U x = (W x : E) := by
    change R (C x) = (W x : E)
    rw [hCM, ← hV]
    change (V (V.symm (W x)) : E) = (W x : E)
    rw [V.apply_symm_apply]
  exact ⟨U, hUmap, hUM, fun x hx => congrArg R (hCperp x hx)⟩

/-- Any finite-block transport can replace the corresponding action of
an ambient transporter, keeping its entire complementary action and
bounding the actual update rank by the finite block dimension. -/
theorem exists_transport_replacing_finite_block
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 M]
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (R : E ≃ₗᵢ[𝕜] E) (hRmap : K.map R.toLinearMap = L)
    (hRM : ∀ x ∈ M, R x ∈ M)
    (W : M ≃ₗᵢ[𝕜] M)
    (hW : (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype) :
    ∃ U : E ≃ₗᵢ[𝕜] E, K.map U.toLinearMap = L ∧
      (∀ x : M, U x = (W x : E)) ∧ (∀ x ∈ Mᗮ, U x = R x) ∧
      (R.toLinearMap - U.toLinearMap).rank ≤ Module.finrank 𝕜 M := by
  obtain ⟨_, _, _, hredR⟩ := R.exists_restriction_of_finite_invariant M hRM
  obtain ⟨U, hUmap, hUM, htail⟩ :=
    K.exists_transport_replacing_reducing_block L M hK R hRmap hredR W hW
  refine ⟨U, hUmap, hUM, htail, ?_⟩
  have hsupport : R.toLinearMap - U.toLinearMap =
      (R.toLinearMap - U.toLinearMap).comp M.starProjection.toLinearMap := by
    apply LinearMap.ext
    intro x
    change R x - U x = R (M.starProjection x) - U (M.starProjection x)
    calc
      _ = R (M.starProjection x + Mᗮ.starProjection x) -
          U (M.starProjection x + Mᗮ.starProjection x) := by
        rw [M.starProjection_add_starProjection_orthogonal]
      _ = _ := by
        rw [map_add, map_add, htail _ (Mᗮ.starProjection_apply_mem x)]
        abel
  rw [hsupport]
  exact (LinearMap.rank_comp_le_right _ _).trans (by
    change Module.rank 𝕜 (LinearMap.range M.starProjection.toLinearMap) ≤ _
    rw [Submodule.range_starProjection, Module.finrank_eq_rank])

end Submodule
