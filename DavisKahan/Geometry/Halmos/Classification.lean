/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
import DavisKahan.Geometry.Halmos.UnitaryEquivalence
import DavisKahan.Geometry.Halmos.GenericRotationPredicates

/-!
# Operator-level Halmos two-projection classification

This module builds the constructive spine of Davis--Kahan 1970 Theorem 3.1: two
ordered pairs of subspaces `(U₁, V₁)` and `(U₂, V₂)` are unitarily equivalent as
pairs iff their four elementary Halmos summands are linearly isometric and their
generic cosine-square operators are unitarily equivalent.

The forward direction is proved here in full: a pair-equivalence
`e : H₁ ≃ₗᵢ[ℂ] H₂` restricts to isometric equivalences of the four elementary
summands and, on the generic remainder, intertwines the cosine-square operator.

The results live under `Experimental.MathAhead`; the frontier statement
`twoProjection_operator_classification` in `Frontier/Section3` is grounded by
`:=` on top of these lemmas so there is a single source of truth.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open SpectraBridge Frontier

universe u v

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]

/-! ## Conjugation of orthogonal projections by an isometric equivalence -/

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- An isometric equivalence intertwines the orthogonal projections onto a
subspace and its image. -/
theorem isometryEquiv_intertwines_projection (e : H₁ ≃ₗᵢ[ℂ] H₂)
    {K : Submodule ℂ H₁} {K' : Submodule ℂ H₂} [K.HasOrthogonalProjection]
    [K'.HasOrthogonalProjection]
    (hmap : K.map (e.toLinearEquiv : H₁ →ₗ[ℂ] H₂) = K') (x : H₁) :
    e (projection K x) = projection K' (e x) := by
  subst hmap
  have h := Submodule.starProjection_map_apply e K (e x)
  rw [e.symm_apply_apply] at h
  exact h.symm

/-! ## Restriction of an isometric equivalence to a matched subspace pair -/

/-- An isometric equivalence taking `K` onto `K'` restricts to an isometric
equivalence `K ≃ₗᵢ K'`. -/
noncomputable def summandEquiv (e : H₁ ≃ₗᵢ[ℂ] H₂) (K : Submodule ℂ H₁)
    {K' : Submodule ℂ H₂} (hmap : K.map e.toLinearMap = K') : K ≃ₗᵢ[ℂ] K' :=
  (e.submoduleMap K).trans (LinearIsometryEquiv.ofEq _ _ hmap)

omit [CompleteSpace H₁] [CompleteSpace H₂] in
@[simp] theorem coe_summandEquiv (e : H₁ ≃ₗᵢ[ℂ] H₂) (K : Submodule ℂ H₁)
    {K' : Submodule ℂ H₂} (hmap : K.map e.toLinearMap = K') (x : K) :
    (summandEquiv e K hmap x : H₂) = e (x : H₁) := rfl

/-! ## Forward direction: a pair-equivalence induces the operator invariant -/

variable (U₁ V₁ : Submodule ℂ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- A pair-equivalence intertwines the Halmos cosine-square operators. -/
theorem intertwines_halmosCosineSq (e : H₁ ≃ₗᵢ[ℂ] H₂)
    (hU : U₁.map e.toLinearMap = U₂) (hV : V₁.map e.toLinearMap = V₂) (v : H₁) :
    e (halmosCosineSq U₁ V₁ v) = halmosCosineSq U₂ V₂ (e v) := by
  have hUc : U₁ᗮ.map e.toLinearMap = U₂ᗮ := by
    rw [Submodule.map_orthogonal_equiv, hU]
  have hVc : V₁ᗮ.map e.toLinearMap = V₂ᗮ := by
    rw [Submodule.map_orthogonal_equiv, hV]
  have hpU := isometryEquiv_intertwines_projection e hU
  have hpV := isometryEquiv_intertwines_projection e hV
  have hpUc := isometryEquiv_intertwines_projection e hUc
  have hpVc := isometryEquiv_intertwines_projection e hVc
  simp only [halmosCosineSq, add_apply,
    mul_apply_eq_comp, map_add]
  rw [hpU, hpV, hpU, hpUc, hpVc, hpUc]

/-- **Forward direction of the operator-level Halmos classification.**  A
unitary equivalence of the ordered pairs induces isometric equivalences of the
four elementary Halmos summands together with a unitary intertwining of the
generic cosine-square operators. -/
theorem sameHalmosInvariant_of_pairEquiv
    (h : PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂) :
    (Nonempty (halmosCommonPart U₁ V₁ ≃ₗᵢ[ℂ] halmosCommonPart U₂ V₂)) ∧
    (Nonempty (halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosSourceDefect U₂ V₂)) ∧
    (Nonempty (halmosTargetDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosTargetDefect U₂ V₂)) ∧
    (Nonempty (halmosExteriorPart U₁ V₁ ≃ₗᵢ[ℂ] halmosExteriorPart U₂ V₂)) ∧
    BoundedOperatorsUnitaryEquivalent
      (genericHalmosCosineSq U₁ V₁) (genericHalmosCosineSq U₂ V₂) := by
  obtain ⟨e, hU, hV⟩ := h
  have hinj : Function.Injective (e.toLinearMap : H₁ → H₂) := by simpa using e.injective
  have hUc : U₁ᗮ.map e.toLinearMap = U₂ᗮ := by rw [Submodule.map_orthogonal_equiv, hU]
  have hVc : V₁ᗮ.map e.toLinearMap = V₂ᗮ := by rw [Submodule.map_orthogonal_equiv, hV]
  -- the four elementary summands map correctly
  have hCommon : (halmosCommonPart U₁ V₁).map e.toLinearMap = halmosCommonPart U₂ V₂ := by
    rw [halmosCommonPart, Submodule.map_inf _ hinj, hU, hV]
  have hSource : (halmosSourceDefect U₁ V₁).map e.toLinearMap = halmosSourceDefect U₂ V₂ := by
    rw [halmosSourceDefect, Submodule.map_inf _ hinj, hU, hVc]
  have hTarget : (halmosTargetDefect U₁ V₁).map e.toLinearMap = halmosTargetDefect U₂ V₂ := by
    rw [halmosTargetDefect, Submodule.map_inf _ hinj, hUc, hV]
  have hExterior : (halmosExteriorPart U₁ V₁).map e.toLinearMap = halmosExteriorPart U₂ V₂ := by
    rw [halmosExteriorPart, Submodule.map_inf _ hinj, hUc, hVc]
  -- the trivial and generic parts map correctly
  have hTrivial : (halmosTrivialPart U₁ V₁).map e.toLinearMap = halmosTrivialPart U₂ V₂ := by
    rw [halmosTrivialPart, Submodule.map_sup, Submodule.map_sup, Submodule.map_sup,
      hCommon, hSource, hTarget, hExterior]
  have hGen : (halmosGenericPart U₁ V₁).map e.toLinearMap = halmosGenericPart U₂ V₂ := by
    rw [halmosGenericPart, Submodule.map_orthogonal_equiv, hTrivial]
  refine ⟨⟨summandEquiv e _ hCommon⟩, ⟨summandEquiv e _ hSource⟩,
    ⟨summandEquiv e _ hTarget⟩, ⟨summandEquiv e _ hExterior⟩, summandEquiv e _ hGen, ?_⟩
  intro x
  apply Subtype.ext
  simp only [coe_summandEquiv, genericHalmosCosineSq, DavisKahanExt.compressOperator,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.coe_orthogonalProjectionOnto_apply]
  calc e ((halmosGenericPart U₁ V₁).starProjection (halmosCosineSq U₁ V₁ (x : H₁)))
      = (halmosGenericPart U₂ V₂).starProjection (e (halmosCosineSq U₁ V₁ (x : H₁))) :=
        isometryEquiv_intertwines_projection e hGen _
    _ = (halmosGenericPart U₂ V₂).starProjection (halmosCosineSq U₂ V₂ (e (x : H₁))) := by
        rw [intertwines_halmosCosineSq U₁ V₁ U₂ V₂ e hU hV]

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti