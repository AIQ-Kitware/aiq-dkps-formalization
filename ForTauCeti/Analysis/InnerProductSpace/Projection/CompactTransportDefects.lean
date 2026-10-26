/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness

/-!
# Compact unitary transport forces finite balanced crossed defects

The rectangular projection `P_L|K : K -> L` is a compact perturbation
of the actual unitary restriction `U|K`. It is Fredholm of index zero.
Its kernel and adjoint kernel are the two crossed intersections, so the
accepted Fredholm index formula gives their finite-dimensional balance.

This is the classical projection-index obstruction. No finite rank of
the projection difference or separability is assumed.
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- Compact displacement of a unitary transporter forces a compact
projection difference. This is the exact intertwining commutator identity. -/
theorem isCompactOperator_projection_sub_of_compact_transport
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hU : IsCompactOperator (((U : E →L[𝕜] E) - 1) : E →L[𝕜] E)) :
    IsCompactOperator ((K.starProjection - L.starProjection) : E →L[𝕜] E) := by
  have hinter (x : E) : U (K.starProjection x) = L.starProjection (U x) := by
    have h := starProjection_map_apply U K (U x)
    simpa only [hmap, U.symm_apply_apply] using h.symm
  have hfac : K.starProjection - L.starProjection =
      L.starProjection ∘L ((U : E →L[𝕜] E) - 1) -
        ((U : E →L[𝕜] E) - 1) ∘L K.starProjection := by
    ext x
    change K.starProjection x - L.starProjection x =
      L.starProjection (U x - x) - (U (K.starProjection x) - K.starProjection x)
    rw [map_sub, hinter]
    abel
  rw [hfac]
  exact (hU.clm_comp L.starProjection).sub (hU.comp_clm K.starProjection)

omit [CompleteSpace E] in
private theorem ker_projection_restriction
    (K L : Submodule 𝕜 E) [L.HasOrthogonalProjection] :
    (L.orthogonalProjectionOnto ∘L K.subtypeL).ker = (K ⊓ Lᗮ).comap K.subtype := by
  ext x
  change L.orthogonalProjectionOnto (x : E) = 0 ↔ (x : E) ∈ K ⊓ Lᗮ
  rw [orthogonalProjectionOnto_eq_zero_iff]
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

/-- Compact-displacement unitary transport forces both crossed defects
to be finite-dimensional and have equal dimension. The projection
difference may have infinite rank and the ambient space may be
nonseparable. -/
theorem finite_crossedDefect_balance_of_compact_transport
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hU : IsCompactOperator (((U : E →L[𝕜] E) - 1) : E →L[𝕜] E)) :
    FiniteDimensional 𝕜 (K ⊓ Lᗮ : Submodule 𝕜 E) ∧
      FiniteDimensional 𝕜 (L ⊓ Kᗮ : Submodule 𝕜 E) ∧
      Module.finrank 𝕜 (K ⊓ Lᗮ : Submodule 𝕜 E) =
        Module.finrank 𝕜 (L ⊓ Kᗮ : Submodule 𝕜 E) := by
  let : CompleteSpace K := (isComplete_coe_of_hasOrthogonalProjection K).completeSpace_coe
  let : CompleteSpace L := (isComplete_coe_of_hasOrthogonalProjection L).completeSpace_coe
  let X := (LinearIsometryEquiv.submoduleMap K U).trans (LinearIsometryEquiv.ofEq _ L hmap)
  have hX (x : K) : (X x : E) = U x := rfl
  let B := L.orthogonalProjectionOnto ∘L K.subtypeL
  let C := B - (X : K →L[𝕜] L)
  have hCfactor : C = L.orthogonalProjectionOnto ∘L
      (1 - (U : E →L[𝕜] E)) ∘L K.subtypeL := by
    ext x
    change L.starProjection x - (X x : E) = L.starProjection ((x : E) - U x)
    have hUX : U x ∈ L := by rw [← hX]; exact (X x).property
    rw [hX, map_sub, L.starProjection_eq_self_iff.mpr hUX]
  have hcompact : IsCompactOperator C := by
    rw [hCfactor]
    have hneg : IsCompactOperator ((1 - (U : E →L[𝕜] E)) : E →L[𝕜] E) := by
      rw [← neg_sub (U : E →L[𝕜] E) 1]
      exact hU.neg
    exact (hneg.comp_clm K.subtypeL).clm_comp L.orthogonalProjectionOnto
  have hXC : (X : K →L[𝕜] L) + C = B := by dsimp only [C]; abel
  have hXfred : ContinuousLinearMap.IsFredholm (X : K →L[𝕜] L) :=
    X.toContinuousLinearEquiv.isFredholm
  have hFred : ContinuousLinearMap.IsFredholm B := by
    simpa only [hXC] using hXfred.add_of_isCompactOperator hcompact
  have hindex : ContinuousLinearMap.index B = 0 := by
    have h := ContinuousLinearMap.index_add_of_isCompactOperator hXfred hcompact
    rw [hXC] at h
    exact h.trans X.toContinuousLinearEquiv.index_eq_zero
  have hBadj : B.adjoint = K.orthogonalProjectionOnto ∘L L.subtypeL := by
    dsimp only [B]
    rw [ContinuousLinearMap.adjoint_comp, K.adjoint_subtypeL, L.adjoint_orthogonalProjectionOnto]
  have hker : B.ker = (K ⊓ Lᗮ).comap K.subtype := ker_projection_restriction K L
  have hkerAdj : B.adjoint.ker = (L ⊓ Kᗮ).comap L.subtype := by
    rw [hBadj]
    exact ker_projection_restriction L K
  let : FiniteDimensional 𝕜 B.ker := hFred.finite_ker
  let : FiniteDimensional 𝕜 (L ⧸ B.range) := hFred.finite_coker
  let : FiniteDimensional 𝕜 B.adjoint.ker :=
    (B.cokerEquivKerAdjoint hFred.isClosed_range).toLinearEquiv.finiteDimensional
  have hsource : FiniteDimensional 𝕜 (K ⊓ Lᗮ : Submodule 𝕜 E) := by
    let : FiniteDimensional 𝕜 ((K ⊓ Lᗮ).comap K.subtype) := by rw [← hker]; infer_instance
    exact (comapSubtypeEquivOfLe (inf_le_left : K ⊓ Lᗮ ≤ K)).finiteDimensional
  have htarget : FiniteDimensional 𝕜 (L ⊓ Kᗮ : Submodule 𝕜 E) := by
    let : FiniteDimensional 𝕜 ((L ⊓ Kᗮ).comap L.subtype) := by rw [← hkerAdj]; infer_instance
    exact (comapSubtypeEquivOfLe (inf_le_left : L ⊓ Kᗮ ≤ L)).finiteDimensional
  refine ⟨hsource, htarget, ?_⟩
  have hkerDim : Module.finrank 𝕜 B.ker = Module.finrank 𝕜 (K ⊓ Lᗮ : Submodule 𝕜 E) := by
    rw [hker]
    exact (comapSubtypeEquivOfLe (inf_le_left : K ⊓ Lᗮ ≤ K)).finrank_eq
  have hkerAdjDim : Module.finrank 𝕜 B.adjoint.ker = Module.finrank 𝕜 (L ⊓ Kᗮ : Submodule 𝕜 E) := by
    rw [hkerAdj]
    exact (comapSubtypeEquivOfLe (inf_le_left : L ⊓ Kᗮ ≤ L)).finrank_eq
  have hcokerDim := (B.cokerEquivKerAdjoint hFred.isClosed_range).toLinearEquiv.finrank_eq
  rw [ContinuousLinearMap.index_eq_finrank_sub, hkerDim, hcokerDim, hkerAdjDim] at hindex
  omega

end Submodule
