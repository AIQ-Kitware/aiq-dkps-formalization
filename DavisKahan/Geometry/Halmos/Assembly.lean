/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Geometry.Halmos.Classification
import ForTauCeti.Analysis.InnerProductSpace.OrthogonalGluing

/-!
# Assembling a pair-equivalence from matched Halmos summands

The converse of `twoProjection_operator_classification` has to *produce* a
unitary `H₁ ≃ₗᵢ H₂` carrying `U₁, V₁` to `U₂, V₂` out of an invariant that only
says the pieces match.  This module is the assembly half of that — brick (2) in
the frontier module's terminology.

`halmosTrivialPart U V` is `(common ⊔ source) ⊔ (target ⊔ exterior)` and
`halmosGenericPart U V` is its orthogonal complement, so the assembly is three
applications of `TauCeti.orthogonalSupGlue` followed by one of
`TauCeti.orthogonalGlue`.  What makes it work is that the four elementary
summands are *mutually orthogonal* (`halmosCommon_le_sourceDefect_orthogonal`
and its five siblings), which is exactly the side condition those lemmas want.

The remaining brick is the generic model: an isometry of the generic parts that
intertwines the two cosine-square operators has to be upgraded to one that
intertwines both projections.  That is the input `eg` here, and it is where the
mathematics still missing lives.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open Frontier

universe u v

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]

section OrthogonalPairs

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A join is orthogonal to a join when each of the four pairs is. -/
theorem sup_le_orthogonal_sup {K L M N : Submodule ℂ H} (h₁ : K ≤ Mᗮ)
    (h₂ : K ≤ Nᗮ) (h₃ : L ≤ Mᗮ) (h₄ : L ≤ Nᗮ) : K ⊔ L ≤ (M ⊔ N)ᗮ := by
  have hmem : ∀ {P : Submodule ℂ H}, P ≤ Mᗮ → P ≤ Nᗮ → P ≤ (M ⊔ N)ᗮ := by
    intro P hM hN x hx
    rw [Submodule.mem_orthogonal]
    rintro u hu
    obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hu
    rw [inner_add_left, (Submodule.mem_orthogonal _ _).mp (hM hx) m hm,
      (Submodule.mem_orthogonal _ _).mp (hN hx) n hn, add_zero]
  exact sup_le (hmem h₁ h₂) (hmem h₃ h₄)

end OrthogonalPairs

variable (U₁ V₁ : Submodule ℂ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- The common part and the source defect are jointly complemented. -/
noncomputable instance instHasOrthogonalProjectionCommonSupSource :
    (halmosCommonPart U₁ V₁ ⊔ halmosSourceDefect U₁ V₁).HasOrthogonalProjection :=
  hasOrthogonalProjection_sup_of_le_orthogonal _ _
    (halmosCommon_le_sourceDefect_orthogonal U₁ V₁)

/-- The target defect and the exterior part are jointly complemented. -/
noncomputable instance instHasOrthogonalProjectionTargetSupExterior :
    (halmosTargetDefect U₁ V₁ ⊔ halmosExteriorPart U₁ V₁).HasOrthogonalProjection :=
  hasOrthogonalProjection_sup_of_le_orthogonal _ _
    (halmosTargetDefect_le_exterior_orthogonal U₁ V₁)

/-- The two halves of the trivial part are orthogonal. -/
theorem commonSupSource_le_orthogonal_targetSupExterior :
    halmosCommonPart U₁ V₁ ⊔ halmosSourceDefect U₁ V₁ ≤
      (halmosTargetDefect U₁ V₁ ⊔ halmosExteriorPart U₁ V₁)ᗮ :=
  sup_le_orthogonal_sup (halmosCommon_le_targetDefect_orthogonal U₁ V₁)
    (halmosCommon_le_exterior_orthogonal U₁ V₁)
    (halmosSourceDefect_le_targetDefect_orthogonal U₁ V₁)
    (halmosSourceDefect_le_exterior_orthogonal U₁ V₁)

/-- **The trivial-part isometry**, glued from the four elementary ones. -/
noncomputable def halmosTrivialEquiv
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[ℂ] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[ℂ] halmosExteriorPart U₂ V₂) :
    halmosTrivialPart U₁ V₁ ≃ₗᵢ[ℂ] halmosTrivialPart U₂ V₂ :=
  TauCeti.orthogonalSupGlue
    (commonSupSource_le_orthogonal_targetSupExterior U₁ V₁)
    (commonSupSource_le_orthogonal_targetSupExterior U₂ V₂)
    (TauCeti.orthogonalSupGlue (halmosCommon_le_sourceDefect_orthogonal U₁ V₁)
      (halmosCommon_le_sourceDefect_orthogonal U₂ V₂) ec es)
    (TauCeti.orthogonalSupGlue (halmosTargetDefect_le_exterior_orthogonal U₁ V₁)
      (halmosTargetDefect_le_exterior_orthogonal U₂ V₂) et ee)

/-- **The global isometry**, glued from the trivial part and the generic
remainder.  `halmosGenericPart` is by definition the orthogonal complement of
`halmosTrivialPart`, so this is exactly the ambient-complement glue. -/
noncomputable def halmosGlobalEquiv
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[ℂ] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[ℂ] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[ℂ] halmosGenericPart U₂ V₂) :
    H₁ ≃ₗᵢ[ℂ] H₂ :=
  TauCeti.orthogonalGlue (halmosTrivialEquiv U₁ V₁ U₂ V₂ ec es et ee) eg

/-- On the trivial part the global isometry is the trivial-part one. -/
theorem halmosGlobalEquiv_apply_of_mem_trivial
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[ℂ] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[ℂ] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[ℂ] halmosGenericPart U₂ V₂)
    {x : H₁} (hx : x ∈ halmosTrivialPart U₁ V₁) :
    halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg x =
      (halmosTrivialEquiv U₁ V₁ U₂ V₂ ec es et ee ⟨x, hx⟩ : H₂) :=
  TauCeti.orthogonalGlue_apply_of_mem _ _ hx

/-- On the generic part the global isometry is the generic one. -/
theorem halmosGlobalEquiv_apply_of_mem_generic
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[ℂ] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[ℂ] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[ℂ] halmosGenericPart U₂ V₂)
    {x : H₁} (hx : x ∈ halmosGenericPart U₁ V₁) :
    halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg x = (eg ⟨x, hx⟩ : H₂) :=
  TauCeti.orthogonalGlue_apply_of_mem_orthogonal _ _ hx

/-- The global isometry carries the trivial part onto the trivial part. -/
theorem map_halmosGlobalEquiv_trivial
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[ℂ] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[ℂ] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[ℂ] halmosGenericPart U₂ V₂) :
    (halmosTrivialPart U₁ V₁).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      halmosTrivialPart U₂ V₂ :=
  TauCeti.map_orthogonalGlue _ _

/-- The global isometry carries the generic part onto the generic part. -/
theorem map_halmosGlobalEquiv_generic
    (ec : halmosCommonPart U₁ V₁ ≃ₗᵢ[ℂ] halmosCommonPart U₂ V₂)
    (es : halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosSourceDefect U₂ V₂)
    (et : halmosTargetDefect U₁ V₁ ≃ₗᵢ[ℂ] halmosTargetDefect U₂ V₂)
    (ee : halmosExteriorPart U₁ V₁ ≃ₗᵢ[ℂ] halmosExteriorPart U₂ V₂)
    (eg : halmosGenericPart U₁ V₁ ≃ₗᵢ[ℂ] halmosGenericPart U₂ V₂) :
    (halmosGenericPart U₁ V₁).map
        (halmosGlobalEquiv U₁ V₁ U₂ V₂ ec es et ee eg).toLinearMap =
      halmosGenericPart U₂ V₂ :=
  TauCeti.map_orthogonalGlue_orthogonal _ _

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
