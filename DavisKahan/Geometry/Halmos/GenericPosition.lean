/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Geometry.Halmos.Assembly

/-!
# The generic Halmos summand is in generic position

`halmosGenericPart U V` is what is left after the four elementary summands are
removed, and the point of removing them is that on the remainder the two
projections are in *generic position*: none of the four intersections
`U ∩ V`, `U ∩ Vᗮ`, `Uᗮ ∩ V`, `Uᗮ ∩ Vᗮ` meets it.  That is the hypothesis the
Halmos `2 × 2` model needs, and this module records it together with the
splitting of the generic part along `U`.

Both facts are prerequisites for brick (1) of the converse of
`twoProjection_operator_classification`: the reconstruction of a pair-compatible
unitary of the generic parts from a unitary equivalence of the generic
cosine-square operators.  With `Assembly.lean` supplying brick (2), that
reconstruction is the last thing standing between the repository and Davis--Kahan
Theorem 3.1's constructive spine.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open Frontier

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-! ## Generic position

Each of the four elementary intersections meets the generic part only at zero.
These are immediate from `halmosGenericPart_inf_eq_bot_of_le_trivial`, but they
are the statements a reader of Section 3 wants to cite, phrased in terms of `U`
and `V` rather than of the summand names.
-/

omit [CompleteSpace H] in
/-- No vector of the generic part lies in both `U` and `V`. -/
theorem halmosGenericPart_inf_inf_eq_bot_left_right :
    halmosGenericPart U V ⊓ (U ⊓ V) = ⊥ :=
  halmosGenericPart_inf_eq_bot_of_le_trivial U V _ (halmosCommonPart_le_trivial U V)

omit [CompleteSpace H] in
/-- No vector of the generic part lies in `U` and is orthogonal to `V`. -/
theorem halmosGenericPart_inf_inf_eq_bot_left_rightCompl :
    halmosGenericPart U V ⊓ (U ⊓ Vᗮ) = ⊥ :=
  halmosGenericPart_inf_eq_bot_of_le_trivial U V _
    (halmosSourceDefect_le_trivial U V)

omit [CompleteSpace H] in
/-- No vector of the generic part is orthogonal to `U` and lies in `V`. -/
theorem halmosGenericPart_inf_inf_eq_bot_leftCompl_right :
    halmosGenericPart U V ⊓ (Uᗮ ⊓ V) = ⊥ :=
  halmosGenericPart_inf_eq_bot_of_le_trivial U V _
    (halmosTargetDefect_le_trivial U V)

omit [CompleteSpace H] in
/-- No vector of the generic part is orthogonal to both. -/
theorem halmosGenericPart_inf_inf_eq_bot_leftCompl_rightCompl :
    halmosGenericPart U V ⊓ (Uᗮ ⊓ Vᗮ) = ⊥ :=
  halmosGenericPart_inf_eq_bot_of_le_trivial U V _
    (halmosExteriorPart_le_trivial U V)

/-! ## Splitting the generic part along `U`

The generic part reduces both projections, so it splits along either one.  This
is the `K ⊕ K` coordinatization the Halmos model is written in, before the two
halves are identified with each other.
-/

/-- **The generic part splits along `U`.**  Its `U`-part and its `Uᗮ`-part are
the two halves of the Halmos model. -/
theorem halmosGenericPart_eq_sup_inf_left :
    halmosGenericPart U V =
      (U ⊓ halmosGenericPart U V) ⊔ (Uᗮ ⊓ halmosGenericPart U V) := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_right inf_le_right)
  refine Submodule.mem_sup.mpr
    ⟨U.starProjection x,
      ⟨U.starProjection_apply_mem x,
        projection_mem_halmosGenericPart_left U V hx⟩,
      x - U.starProjection x,
      ⟨U.sub_starProjection_mem_orthogonal x, ?_⟩, by abel⟩
  exact (halmosGenericPart U V).sub_mem hx
    (projection_mem_halmosGenericPart_left U V hx)

/-- **The generic part splits along `V`** as well. -/
theorem halmosGenericPart_eq_sup_inf_right :
    halmosGenericPart U V =
      (V ⊓ halmosGenericPart U V) ⊔ (Vᗮ ⊓ halmosGenericPart U V) := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_right inf_le_right)
  refine Submodule.mem_sup.mpr
    ⟨V.starProjection x,
      ⟨V.starProjection_apply_mem x,
        projection_mem_halmosGenericPart_right U V hx⟩,
      x - V.starProjection x,
      ⟨V.sub_starProjection_mem_orthogonal x, ?_⟩, by abel⟩
  exact (halmosGenericPart U V).sub_mem hx
    (projection_mem_halmosGenericPart_right U V hx)

/-! ## What generic position says about the halves

In generic position the `U`-half of the generic part contains no vector of `V`
and no vector of `Vᗮ`.  Equivalently: on that half, `P_V` has trivial kernel and
`1 - P_V` has trivial kernel, which is exactly the condition that makes the
cosine operator's spectrum avoid both endpoints — the analytic content of "the
angles are strictly between `0` and `π/2`".
-/

omit [CompleteSpace H] in
/-- On the `U`-half of the generic part, `P_V` has trivial kernel: a vector
there orthogonal to `V` is zero. -/
theorem eq_zero_of_mem_inf_generic_left_of_mem_orthogonal_right
    {x : H} (hx : x ∈ U ⊓ halmosGenericPart U V) (hxV : x ∈ Vᗮ) : x = 0 := by
  have : x ∈ halmosGenericPart U V ⊓ (U ⊓ Vᗮ) := ⟨hx.2, hx.1, hxV⟩
  simpa [halmosGenericPart_inf_inf_eq_bot_left_rightCompl U V] using this

omit [CompleteSpace H] in
/-- On the `U`-half of the generic part, `1 - P_V` has trivial kernel: a vector
there lying in `V` is zero. -/
theorem eq_zero_of_mem_inf_generic_left_of_mem_right
    {x : H} (hx : x ∈ U ⊓ halmosGenericPart U V) (hxV : x ∈ V) : x = 0 := by
  have : x ∈ halmosGenericPart U V ⊓ (U ⊓ V) := ⟨hx.2, hx.1, hxV⟩
  simpa [halmosGenericPart_inf_inf_eq_bot_left_right U V] using this

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
