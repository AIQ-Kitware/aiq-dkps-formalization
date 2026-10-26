/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.FiniteTransportSupport
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteCore

/-!
# Finite sections of finite-rank subspace transports

An arbitrary finite-rank unitary perturbation transporting two subspaces
restricts to an actual finite-dimensional unitary transport. Outside the
section the two projections agree, and the ambient displacement is the
orthogonal zero extension of the restricted displacement.
-/

public section

noncomputable section

namespace Submodule

open TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A transporter fixing a complementary reducing block forces the
source and target projections to agree on that block. -/
theorem starProjection_eq_on_orthogonal_of_transport
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hfix : ∀ x ∈ Mᗮ, U x = x) :
    ∀ x ∈ Mᗮ, K.starProjection x = L.starProjection x := by
  intro x hx
  have hinv : U.symm x = x := by
    apply U.injective
    rw [U.apply_symm_apply, hfix _ hx]
  have hproj : L.starProjection x = U (K.starProjection (U.symm x)) := by
    simpa only [hmap] using starProjection_map_apply U K x
  rw [hproj, hinv]
  exact (hfix (K.starProjection x) (hK.orthogonal_mem_invtSubmodule hx)).symm

/-- Truncating a unitary on a common reducing finite subspace truncates
the transported directed sine by the same orthogonal projection. -/
theorem sinThetaMap_map_truncation_eq_comp_starProjection
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 M]
    (U V : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hUM : ∀ x ∈ M, U x ∈ M)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hL : M.IsReducing L.starProjection.toLinearMap)
    (hV : ∀ x ∈ M, V x = U x) (hfix : ∀ x ∈ Mᗮ, V x = x) :
    K.sinThetaMap (K.map V.toLinearMap) = (K.sinThetaMap L) ∘L M.starProjection := by
  let L' := K.map V.toLinearMap
  obtain ⟨W, hW, _, _⟩ := U.exists_restriction_of_finite_invariant M hUM
  have hWV (x : M) : (W x : E) = V x := (hW x).trans (hV x x.property).symm
  have hlocal := K.map_comap_subtype_of_isometry_restriction L M U W hmap hW
  have hlocal' := K.map_comap_subtype_of_isometry_restriction L' M V W rfl hWV
  have hpair : L'.comap M.subtype = L.comap M.subtype := hlocal'.symm.trans hlocal
  have hL' : M.IsReducing L'.starProjection.toLinearMap := by
    apply (L'.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule M).mpr
    intro x hx
    exact K.starProjection_map_mem_of_isometry_restriction M V W hWV
      hK.mem_invtSubmodule x hx
  have heq := K.starProjection_eq_on_orthogonal_of_transport L' M V rfl hK hfix
  have hext := K.sinThetaMap_eq_orthogonal_extension L' M hK hL' heq
  have hrestricted : (K.comap M.subtype).sinThetaMap (L'.comap M.subtype) =
      (K.comap M.subtype).sinThetaMap (L.comap M.subtype) := by simp only [hpair]
  rw [hrestricted] at hext
  rw [hext]
  symm
  apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
  constructor
  · intro x
    change K.sinThetaMap L (M.starProjection (x : E)) = _
    rw [M.starProjection_eq_self_iff.mpr x.property]
    exact (K.sinThetaMap_comap_subtype_apply_of_invariant L M
      hK.mem_invtSubmodule hL.mem_invtSubmodule x).symm
  · intro x hx
    change K.sinThetaMap L (M.starProjection x) = 0
    rw [M.starProjection_apply_eq_zero_iff.mpr hx, map_zero]

/-- Every finite-rank unitary subspace transport has a finite-dimensional
section containing any prescribed finite core. The section carries the
actual restricted transport and the full ambient displacement spectrum. -/
theorem exists_finite_transport_section
    (K L F : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 F] (U : E ≃ₗᵢ[𝕜] E)
    (hmap : K.map U.toLinearMap = L) (n : ℕ) (hU : (1 - U.toLinearMap).rank ≤ n) :
    ∃ M : Submodule 𝕜 E, ∃ _ : FiniteDimensional 𝕜 M, F ≤ M ∧
      ∃ V : M ≃ₗᵢ[𝕜] M,
        (∀ x : M, (V x : E) = U x) ∧
        (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
        M.IsReducing K.starProjection.toLinearMap ∧
        M.IsReducing L.starProjection.toLinearMap ∧
        (∀ x ∈ Mᗮ, K.starProjection x = L.starProjection x) ∧
        1 - (U : E →L[𝕜] E) = M.subtypeL ∘L
          (1 - (V : M →L[𝕜] M)) ∘L M.orthogonalProjectionOnto := by
  obtain ⟨M, hM, hFM, hKM, hUM, _, hfix⟩ :=
    exists_finite_transport_support K F U n hU
  let : FiniteDimensional 𝕜 M := hM
  obtain ⟨V, hV, _, _⟩ := U.exists_restriction_of_finite_invariant M hUM.mem_invtSubmodule
  have hlocal := map_comap_subtype_of_isometry_restriction K L M U V hmap hV
  have hLinv : ∀ x ∈ M, L.starProjection x ∈ M := by
    simpa only [hmap] using
      starProjection_map_mem_of_isometry_restriction K M U V hV hKM.mem_invtSubmodule
  refine ⟨M, hM, hFM, V, hV, hlocal, hKM,
    (L.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule M).mpr hLinv,
    starProjection_eq_on_orthogonal_of_transport K L M U hmap hKM hfix, ?_⟩
  apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
  constructor
  · intro x
    change (x : E) - U x = (x : E) - (V x : E)
    rw [hV]
  · intro x hx
    change x - U x = 0
    rw [hfix _ hx, sub_self]

end Submodule
