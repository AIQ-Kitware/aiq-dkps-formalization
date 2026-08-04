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

/-! ## How `U` and `V` sit across the trivial/generic split

To show an assembled isometry carries `U₁` to `U₂` one has to split a vector of
`U₁` into a trivial and a generic piece *that are themselves in `U₁`*, and know
what the trivial piece looks like.  Both facts are recorded here; neither was in
`TwoProjections.lean`, which carries the dual statements (the projections
preserve the summands) but not these.
-/

section Structure

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- The trivial part reduces the source projection. -/
theorem starProjection_left_reduces_halmosTrivialPart :
    U.starProjection.Reduces (halmosTrivialPart U V) :=
  ContinuousLinearMap.IsSymmetric.reduces_of_invariant
    U.starProjection_isSymmetric
    fun y hy => projection_mem_halmosTrivialPart_left U V (x := y) hy

omit [CompleteSpace H] in
/-- The trivial part reduces the target projection. -/
theorem starProjection_right_reduces_halmosTrivialPart :
    V.starProjection.Reduces (halmosTrivialPart U V) :=
  ContinuousLinearMap.IsSymmetric.reduces_of_invariant
    V.starProjection_isSymmetric
    fun y hy => projection_mem_halmosTrivialPart_right U V (x := y) hy

/-- **`U` is split by the trivial/generic decomposition.**  The trivial-part
projector maps `U` into itself, so a vector of `U` decomposes into a trivial and
a generic piece each still in `U`. -/
theorem starProjection_trivial_mem_left {x : H} (hx : x ∈ U) :
    (halmosTrivialPart U V).starProjection x ∈ U := by
  have h := ContinuousLinearMap.starProjection_apply_comm_of_reduces
    U.starProjection (halmosTrivialPart U V)
    (starProjection_left_reduces_halmosTrivialPart U V) x
  rw [Submodule.starProjection_eq_self_iff.mpr hx] at h
  exact h ▸ U.starProjection_apply_mem _

/-- The same for `V`. -/
theorem starProjection_trivial_mem_right {x : H} (hx : x ∈ V) :
    (halmosTrivialPart U V).starProjection x ∈ V := by
  have h := ContinuousLinearMap.starProjection_apply_comm_of_reduces
    V.starProjection (halmosTrivialPart U V)
    (starProjection_right_reduces_halmosTrivialPart U V) x
  rw [Submodule.starProjection_eq_self_iff.mpr hx] at h
  exact h ▸ V.starProjection_apply_mem _

omit [CompleteSpace H] in
/-- A vector in both `U` and `Uᗮ` is zero. -/
private theorem eq_zero_of_mem_of_mem_orthogonal {K : Submodule ℂ H} {x : H}
    (h₁ : x ∈ K) (h₂ : x ∈ Kᗮ) : x = 0 :=
  inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp h₂ x h₁)

omit [CompleteSpace H] in
/-- **The part of `U` inside the trivial summand is `common ⊔ source`.**  The
other two elementary summands lie in `Uᗮ`, so they contribute nothing. -/
theorem inf_halmosTrivialPart_left :
    U ⊓ halmosTrivialPart U V =
      halmosCommonPart U V ⊔ halmosSourceDefect U V := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxU, hxT⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hxT
    -- `p` already lies in `U`; hence so does `q`, which also lies in `Uᗮ`.
    have hcsU : halmosCommonPart U V ⊔ halmosSourceDefect U V ≤ U :=
      sup_le inf_le_left inf_le_left
    have hteUc : halmosTargetDefect U V ⊔ halmosExteriorPart U V ≤ Uᗮ :=
      sup_le inf_le_left inf_le_left
    have hpU : p ∈ U := hcsU hp
    have hqU : q ∈ U := by
      have hq' : q = p + q - p := by abel
      rw [hq']
      exact U.sub_mem hxU hpU
    have hqUc : q ∈ Uᗮ := hteUc hq
    rw [eq_zero_of_mem_of_mem_orthogonal hqU hqUc, add_zero]
    exact hp
  · exact sup_le (le_inf inf_le_left (halmosCommonPart_le_trivial U V))
      (le_inf inf_le_left (halmosSourceDefect_le_trivial U V))

omit [CompleteSpace H] in
/-- **The part of `V` inside the trivial summand is `common ⊔ target`.** -/
theorem inf_halmosTrivialPart_right :
    V ⊓ halmosTrivialPart U V =
      halmosCommonPart U V ⊔ halmosTargetDefect U V := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxV, hxT⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hxT
    -- Here the `V`-part is split across the two halves, so regroup by hand.
    obtain ⟨c, hc, s, hs, rfl⟩ := Submodule.mem_sup.mp hp
    obtain ⟨t, ht, e, he, rfl⟩ := Submodule.mem_sup.mp hq
    have hcV : c ∈ V := hc.2
    have htV : t ∈ V := ht.2
    have hsVc : s ∈ Vᗮ := hs.2
    have heVc : e ∈ Vᗮ := he.2
    have hrest : s + e ∈ V := by
      have : s + e = c + s + (t + e) - (c + t) := by abel
      rw [this]
      exact V.sub_mem hxV (V.add_mem hcV htV)
    have hrestc : s + e ∈ Vᗮ := Vᗮ.add_mem hsVc heVc
    have hse : s + e = 0 := eq_zero_of_mem_of_mem_orthogonal hrest hrestc
    have hsplit : c + s + (t + e) = c + t + (s + e) := by abel
    rw [hsplit, hse, add_zero]
    exact Submodule.mem_sup.mpr ⟨c, hc, t, ht, rfl⟩
  · exact sup_le (le_inf inf_le_right (halmosCommonPart_le_trivial U V))
      (le_inf inf_le_right (halmosTargetDefect_le_trivial U V))

end Structure

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
