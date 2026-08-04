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

/-! ## The cosine block

In the `M ⊕ N` coordinates of `halmosGenericPart_eq_sup_inf_left`, the second
projection has a self-adjoint block matrix whose upper-left corner is the
compression of `P_V` to `M`.  That corner is Halmos's `cos²Θ`: its quadratic
form is `‖P_V m‖²`, so generic position says exactly that it and `1 - cos²Θ`
have trivial kernel — the spectrum avoids both endpoints, which is the analytic
form of "every angle is strictly between `0` and `π/2`".
-/

/-- The `U`-half of the generic part. -/
noncomputable abbrev genericLeftHalf : Submodule ℂ H := U ⊓ halmosGenericPart U V

/-- The `Uᗮ`-half of the generic part. -/
noncomputable abbrev genericRightHalf : Submodule ℂ H :=
  Uᗮ ⊓ halmosGenericPart U V

/-- The quadratic form of an orthogonal projector is the squared norm of the
projection. -/
theorem inner_starProjection_self (W : Submodule ℂ H)
    [W.HasOrthogonalProjection] (x : H) :
    ⟪W.starProjection x, x⟫_ℂ = ((‖W.starProjection x‖ : ℝ) : ℂ) ^ 2 := by
  have hmem := W.starProjection_apply_mem x
  have hperp := W.sub_starProjection_mem_orthogonal x
  have hsplit : W.starProjection x + (x - W.starProjection x) = x := by abel
  calc ⟪W.starProjection x, x⟫_ℂ
      = ⟪W.starProjection x,
          W.starProjection x + (x - W.starProjection x)⟫_ℂ := by rw [hsplit]
    _ = ⟪W.starProjection x, W.starProjection x⟫_ℂ +
          ⟪W.starProjection x, x - W.starProjection x⟫_ℂ := inner_add_right _ _ _
    _ = ((‖W.starProjection x‖ : ℝ) : ℂ) ^ 2 := by
        rw [Submodule.inner_right_of_mem_orthogonal hmem hperp, add_zero,
          inner_self_eq_norm_sq_to_K]
        norm_cast

/-- Pythagoras across a projector. -/
theorem norm_sq_eq_starProjection_add_orthogonal (W : Submodule ℂ H)
    [W.HasOrthogonalProjection] (x : H) :
    ‖x‖ ^ 2 = ‖W.starProjection x‖ ^ 2 + ‖x - W.starProjection x‖ ^ 2 := by
  have hperp : ⟪W.starProjection x, x - W.starProjection x⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (W.starProjection_apply_mem x)
      (W.sub_starProjection_mem_orthogonal x)
  have hsplit : W.starProjection x + (x - W.starProjection x) = x := by abel
  have hpy := @norm_add_sq ℂ _ _ _ _ (W.starProjection x)
    (x - W.starProjection x)
  rw [hsplit, hperp] at hpy
  simp only [map_zero, mul_zero, add_zero] at hpy
  linarith

/-- **Halmos's `cos²Θ`** on the `U`-half of the generic part: the compression of
`P_V`. -/
noncomputable def genericCosineBlock :
    genericLeftHalf U V →L[ℂ] genericLeftHalf U V :=
  DavisKahanExt.compressOperator (genericLeftHalf U V) V.starProjection

/-- **The quadratic form of the cosine block is `‖P_V m‖²`.**  Everything below
is read off this identity. -/
theorem re_inner_genericCosineBlock (m : genericLeftHalf U V) :
    RCLike.re ⟪genericCosineBlock U V m, m⟫_ℂ =
      ‖V.starProjection (m : H)‖ ^ 2 := by
  have hcoe : ((genericCosineBlock U V m : genericLeftHalf U V) : H) =
      (genericLeftHalf U V).starProjection (V.starProjection (m : H)) := by
    simp [genericCosineBlock, DavisKahanExt.compressOperator]
  have h1 : ⟪genericCosineBlock U V m, m⟫_ℂ =
      ⟪V.starProjection (m : H), (m : H)⟫_ℂ := by
    calc ⟪genericCosineBlock U V m, m⟫_ℂ
        = ⟪((genericCosineBlock U V m : genericLeftHalf U V) : H), (m : H)⟫_ℂ :=
          rfl
      _ = ⟪(genericLeftHalf U V).starProjection (V.starProjection (m : H)),
            (m : H)⟫_ℂ := by rw [hcoe]
      _ = ⟪V.starProjection (m : H),
            (genericLeftHalf U V).starProjection (m : H)⟫_ℂ :=
          (genericLeftHalf U V).inner_starProjection_left_eq_right _ _
      _ = ⟪V.starProjection (m : H), (m : H)⟫_ℂ := by
          rw [Submodule.starProjection_eq_self_iff.mpr m.2]
  rw [h1, inner_starProjection_self]
  norm_cast

/-- **The cosine block is strictly positive.**  Its quadratic form vanishes only
at `0`, because a vector of the `U`-half orthogonal to `V` is zero. -/
theorem re_inner_genericCosineBlock_pos {m : genericLeftHalf U V} (hm : m ≠ 0) :
    0 < RCLike.re ⟪genericCosineBlock U V m, m⟫_ℂ := by
  rw [re_inner_genericCosineBlock]
  have hne : V.starProjection (m : H) ≠ 0 := by
    intro hzero
    have hmV : (m : H) ∈ Vᗮ := by
      rwa [Submodule.starProjection_apply_eq_zero_iff] at hzero
    exact hm (Subtype.ext
      (eq_zero_of_mem_inf_generic_left_of_mem_orthogonal_right U V m.2 hmV))
  have hpos : 0 < ‖V.starProjection (m : H)‖ := norm_pos_iff.mpr hne
  positivity

/-- **The cosine block never reaches `1`.**  A vector of the `U`-half lying in
`V` is zero, so the complementary component is always nonzero. -/
theorem re_inner_genericCosineBlock_lt {m : genericLeftHalf U V} (hm : m ≠ 0) :
    RCLike.re ⟪genericCosineBlock U V m, m⟫_ℂ < ‖m‖ ^ 2 := by
  rw [re_inner_genericCosineBlock]
  have hne : (m : H) - V.starProjection (m : H) ≠ 0 := by
    intro hzero
    have heq : (m : H) = V.starProjection (m : H) := by
      rw [← sub_eq_zero]; exact hzero
    exact hm (Subtype.ext (eq_zero_of_mem_inf_generic_left_of_mem_right U V m.2
      (heq ▸ V.starProjection_apply_mem (m : H))))
  have hpos : 0 < ‖(m : H) - V.starProjection (m : H)‖ := norm_pos_iff.mpr hne
  have hpy := norm_sq_eq_starProjection_add_orthogonal V (m : H)
  have hcoe : ‖(m : H)‖ = ‖m‖ := Submodule.norm_coe m
  rw [hcoe] at hpy
  nlinarith

/-! ## The cross block

The off-diagonal block `B = P_N P_V |_M` is the one that identifies the two
halves with each other.  Its kernel is trivial — and the argument needs no
functional calculus at all, only generic position twice: if `B m = 0` then
`P_V m` lies in `M`, hence in `M ⊓ V = ⊥`, so `m ⊥ V`, so `m = 0`.
-/

/-- On the generic part, projecting onto the `U`-half is projecting onto `U`. -/
theorem starProjection_genericLeftHalf_of_mem_generic {g : H}
    (hg : g ∈ halmosGenericPart U V) :
    (genericLeftHalf U V).starProjection g = U.starProjection g := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ⟨U.starProjection_apply_mem g,
      projection_mem_halmosGenericPart_left U V hg⟩ ?_
  intro w hw
  exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp
    (U.sub_starProjection_mem_orthogonal g) w hw.1)

/-- The complementary component of a generic vector lands in the `Uᗮ`-half. -/
theorem sub_starProjection_mem_genericRightHalf {g : H}
    (hg : g ∈ halmosGenericPart U V) :
    g - U.starProjection g ∈ genericRightHalf U V :=
  ⟨U.sub_starProjection_mem_orthogonal g,
    (halmosGenericPart U V).sub_mem hg
      (projection_mem_halmosGenericPart_left U V hg)⟩

/-- **The Halmos cross block** `B = P_N P_V |_M`. -/
noncomputable def genericCrossBlock :
    genericLeftHalf U V →L[ℂ] genericRightHalf U V :=
  (genericRightHalf U V).orthogonalProjectionOnto ∘L V.starProjection ∘L
    (genericLeftHalf U V).subtypeL

/-- **`P_V` splits into the two blocks on the `U`-half.**  This is the statement
that `A` and `B` really are the two entries of `P_V`'s first column. -/
theorem starProjection_eq_cosineBlock_add_crossBlock (m : genericLeftHalf U V) :
    V.starProjection (m : H) =
      ((genericCosineBlock U V m : genericLeftHalf U V) : H) +
        ((genericCrossBlock U V m : genericRightHalf U V) : H) := by
  have hgen : V.starProjection (m : H) ∈ halmosGenericPart U V :=
    projection_mem_halmosGenericPart_right U V m.2.2
  have hM : ((genericCosineBlock U V m : genericLeftHalf U V) : H) =
      U.starProjection (V.starProjection (m : H)) := by
    have h : ((genericCosineBlock U V m : genericLeftHalf U V) : H) =
        (genericLeftHalf U V).starProjection (V.starProjection (m : H)) := by
      simp [genericCosineBlock, DavisKahanExt.compressOperator]
    rw [h, starProjection_genericLeftHalf_of_mem_generic U V hgen]
  have hN : ((genericCrossBlock U V m : genericRightHalf U V) : H) =
      (genericRightHalf U V).starProjection (V.starProjection (m : H)) := by
    simp [genericCrossBlock]
  rw [hM, hN]
  -- The `N`-component of a generic vector is what is left after `P_U`.
  have hsplit : (genericRightHalf U V).starProjection
      (V.starProjection (m : H)) =
      V.starProjection (m : H) - U.starProjection (V.starProjection (m : H)) := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (sub_starProjection_mem_genericRightHalf U V hgen) ?_
    intro w hw
    have hcancel : V.starProjection (m : H) -
        (V.starProjection (m : H) - U.starProjection (V.starProjection (m : H)))
        = U.starProjection (V.starProjection (m : H)) := by abel
    rw [hcancel]
    exact (Submodule.mem_orthogonal _ _).mp hw.1 _
      (U.starProjection_apply_mem _)
  rw [hsplit]
  abel

/-- **The cross block has trivial kernel.**  Generic position twice: if
`B m = 0` then `P_V m` lies in `M`, hence in `M ⊓ V = ⊥`, so `m ⊥ V`, so
`m = 0`.  No functional calculus. -/
theorem genericCrossBlock_eq_zero_iff (m : genericLeftHalf U V) :
    genericCrossBlock U V m = 0 ↔ m = 0 := by
  refine ⟨fun hB => ?_, fun hm => by rw [hm, map_zero]⟩
  -- With the cross component gone, `P_V m` is the cosine component, so it is in `M`.
  have hsplit := starProjection_eq_cosineBlock_add_crossBlock U V m
  rw [hB] at hsplit
  simp only [Submodule.coe_zero, add_zero] at hsplit
  have hmemM : V.starProjection (m : H) ∈ genericLeftHalf U V :=
    hsplit ▸ (genericCosineBlock U V m).2
  -- It is also in `V`, and `M ⊓ V = ⊥` by generic position.
  have hzero : V.starProjection (m : H) = 0 :=
    eq_zero_of_mem_inf_generic_left_of_mem_right U V hmemM
      (V.starProjection_apply_mem _)
  -- So `m ⊥ V`, and `M ⊓ Vᗮ = ⊥`.
  have hmV : (m : H) ∈ Vᗮ := by
    rwa [Submodule.starProjection_apply_eq_zero_iff] at hzero
  exact Subtype.ext
    (eq_zero_of_mem_inf_generic_left_of_mem_orthogonal_right U V m.2 hmV)


/-! ## The mirrored block on the `Uᗮ`-half

Everything above has a mirror obtained by swapping `U` for `Uᗮ`, and the mirror
of `genericCrossBlock_eq_zero_iff` is what says the cross block has *dense
range* as well as trivial kernel — the two together are what make its polar
factor a unitary `M ≃ₗᵢ N` rather than a mere partial isometry.
-/

omit [CompleteSpace H] in
/-- On the `Uᗮ`-half of the generic part, a vector lying in `V` is zero. -/
theorem eq_zero_of_mem_inf_generic_right_of_mem_right
    {x : H} (hx : x ∈ genericRightHalf U V) (hxV : x ∈ V) : x = 0 := by
  have : x ∈ halmosGenericPart U V ⊓ (Uᗮ ⊓ V) := ⟨hx.2, hx.1, hxV⟩
  simpa [halmosGenericPart_inf_inf_eq_bot_leftCompl_right U V] using this

omit [CompleteSpace H] in
/-- On the `Uᗮ`-half of the generic part, a vector orthogonal to `V` is zero. -/
theorem eq_zero_of_mem_inf_generic_right_of_mem_orthogonal_right
    {x : H} (hx : x ∈ genericRightHalf U V) (hxV : x ∈ Vᗮ) : x = 0 := by
  have : x ∈ halmosGenericPart U V ⊓ (Uᗮ ⊓ Vᗮ) := ⟨hx.2, hx.1, hxV⟩
  simpa [halmosGenericPart_inf_inf_eq_bot_leftCompl_rightCompl U V] using this

/-- On the generic part, projecting onto the `Uᗮ`-half is projecting onto
`Uᗮ`. -/
theorem starProjection_genericRightHalf_of_mem_generic {g : H}
    (hg : g ∈ halmosGenericPart U V) :
    (genericRightHalf U V).starProjection g = g - U.starProjection g := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (sub_starProjection_mem_genericRightHalf U V hg) ?_
  intro w hw
  have hcancel : g - (g - U.starProjection g) = U.starProjection g := by abel
  rw [hcancel]
  exact (Submodule.mem_orthogonal _ _).mp hw.1 _ (U.starProjection_apply_mem g)

/-- **The mirrored cross block** `B' = P_M P_V |_N`, the adjoint entry. -/
noncomputable def genericCrossBlockMirror :
    genericRightHalf U V →L[ℂ] genericLeftHalf U V :=
  (genericLeftHalf U V).orthogonalProjectionOnto ∘L V.starProjection ∘L
    (genericRightHalf U V).subtypeL

/-- `P_V` splits into the two blocks on the `Uᗮ`-half as well. -/
theorem starProjection_eq_mirror_add_of_mem_right (n : genericRightHalf U V) :
    V.starProjection (n : H) =
      ((genericCrossBlockMirror U V n : genericLeftHalf U V) : H) +
        (V.starProjection (n : H) -
          U.starProjection (V.starProjection (n : H))) := by
  have hgen : V.starProjection (n : H) ∈ halmosGenericPart U V :=
    projection_mem_halmosGenericPart_right U V n.2.2
  have hM : ((genericCrossBlockMirror U V n : genericLeftHalf U V) : H) =
      U.starProjection (V.starProjection (n : H)) := by
    have h : ((genericCrossBlockMirror U V n : genericLeftHalf U V) : H) =
        (genericLeftHalf U V).starProjection (V.starProjection (n : H)) := by
      simp [genericCrossBlockMirror]
    rw [h, starProjection_genericLeftHalf_of_mem_generic U V hgen]
  rw [hM]
  abel

/-- **The mirrored cross block has trivial kernel.**  Same argument as
`genericCrossBlock_eq_zero_iff` with `U` and `Uᗮ` exchanged: if `B' n = 0` then
`P_V n` lies in `N`, hence in `N ⊓ V = ⊥`, so `n ⊥ V`, so `n = 0`.

Trivial kernel here is trivial *cokernel* for `genericCrossBlock`; with
`genericCrossBlock_eq_zero_iff` this is what makes the polar factor a
unitary. -/
theorem genericCrossBlockMirror_eq_zero_iff (n : genericRightHalf U V) :
    genericCrossBlockMirror U V n = 0 ↔ n = 0 := by
  refine ⟨fun hB => ?_, fun hn => by rw [hn, map_zero]⟩
  have hgen : V.starProjection (n : H) ∈ halmosGenericPart U V :=
    projection_mem_halmosGenericPart_right U V n.2.2
  have hsplit := starProjection_eq_mirror_add_of_mem_right U V n
  rw [hB] at hsplit
  simp only [Submodule.coe_zero, zero_add] at hsplit
  -- The `M`-component is gone, so `P_V n` is its own `N`-component.
  have hmemN : V.starProjection (n : H) ∈ genericRightHalf U V := by
    rw [← starProjection_genericRightHalf_of_mem_generic U V hgen] at hsplit
    exact hsplit ▸ (genericRightHalf U V).starProjection_apply_mem _
  have hzero : V.starProjection (n : H) = 0 :=
    eq_zero_of_mem_inf_generic_right_of_mem_right U V hmemN
      (V.starProjection_apply_mem _)
  have hnV : (n : H) ∈ Vᗮ := by
    rwa [Submodule.starProjection_apply_eq_zero_iff] at hzero
  exact Subtype.ext
    (eq_zero_of_mem_inf_generic_right_of_mem_orthogonal_right U V n.2 hnV)


/-! ## Relation to the frontier's chosen invariant

`SameHalmosOperatorInvariant` (Frontier/Section3) records the generic part by
the unitary-equivalence class of `genericHalmosCosineSq U V`, the compression of
`P_U P_V P_U + P_Uᗮ P_Vᗮ P_Uᗮ` to `G`.  On the `U`-half that operator *is* the
cosine block, which the lemma below proves.

**This exposes a design question about the invariant, worth stating plainly.**
On the `Uᗮ`-half the same operator is `1 - D`, and under the identification of
the two halves that is again the cosine block.  So `genericHalmosCosineSq` is
`A ⊕ A`, not `A`.  Recovering `A` from `A ⊕ A` up to unitary equivalence is a
multiplicity-halving statement — precisely the Hahn--Hellinger material the
frontier lists as its `hard_math` blocker — whereas the pair `(U, V)` is
determined by `A` alone by elementary means.  If the invariant were recorded as
the cosine block on the `U`-half instead, the classification would not need
multiplicity theory at all.
-/

/-- **On the `U`-half, the frontier's generic cosine-square operator is the
cosine block.** -/
theorem coe_genericHalmosCosineSq_of_mem_left (m : genericLeftHalf U V) :
    ((genericHalmosCosineSq U V ⟨(m : H), m.2.2⟩ :
        halmosGenericPart U V) : H) =
      ((genericCosineBlock U V m : genericLeftHalf U V) : H) := by
  have hmU : U.starProjection (m : H) = (m : H) :=
    Submodule.starProjection_eq_self_iff.mpr m.2.1
  have hmUc : Uᗮ.starProjection (m : H) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    simpa using m.2.1
  -- Only the first summand survives on the `U`-half.
  have hval : halmosCosineSq U V (m : H) =
      U.starProjection (V.starProjection (m : H)) := by
    show U.starProjection (V.starProjection (U.starProjection (m : H))) +
      Uᗮ.starProjection (Vᗮ.starProjection (Uᗮ.starProjection (m : H))) = _
    rw [hmU, hmUc, map_zero, map_zero, add_zero]
  have hgen : halmosCosineSq U V (m : H) ∈ halmosGenericPart U V := by
    rw [hval]
    exact projection_mem_halmosGenericPart_left U V
      (projection_mem_halmosGenericPart_right U V m.2.2)
  have hL : ((genericHalmosCosineSq U V ⟨(m : H), m.2.2⟩ :
      halmosGenericPart U V) : H) = halmosCosineSq U V (m : H) := by
    have h : ((genericHalmosCosineSq U V ⟨(m : H), m.2.2⟩ :
        halmosGenericPart U V) : H) =
        (halmosGenericPart U V).starProjection (halmosCosineSq U V (m : H)) := by
      simp [genericHalmosCosineSq, DavisKahanExt.compressOperator]
    rw [h, Submodule.starProjection_eq_self_iff.mpr hgen]
  have hR : ((genericCosineBlock U V m : genericLeftHalf U V) : H) =
      U.starProjection (V.starProjection (m : H)) := by
    have h : ((genericCosineBlock U V m : genericLeftHalf U V) : H) =
        (genericLeftHalf U V).starProjection (V.starProjection (m : H)) := by
      simp [genericCosineBlock, DavisKahanExt.compressOperator]
    rw [h, starProjection_genericLeftHalf_of_mem_generic U V
      (projection_mem_halmosGenericPart_right U V m.2.2)]
  rw [hL, hR, hval]


/-! ## The cross block is the adjoint of its mirror, and has dense range

`‖B m‖² = ⟪A m, m⟫ - ‖A m‖²` is Pythagoras applied to `P_V m = A m + B m`, whose
two summands are orthogonal because `M ≤ U` and `N ≤ Uᗮ`.  In the classical
account this identity is `B*B = A(1 - A)`; here it is needed only in quadratic
form.

`B'` is the adjoint of `B`, so `genericCrossBlockMirror_eq_zero_iff` says exactly
that `B` has dense range.  Trivial kernel and dense range together are what make
the polar factor of `B` a unitary `M ≃ₗᵢ N`.
-/

omit [CompleteSpace H] in
/-- The two halves of the generic part are orthogonal. -/
theorem genericLeftHalf_le_orthogonal_genericRightHalf :
    genericLeftHalf U V ≤ (genericRightHalf U V)ᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  exact inner_eq_zero_symm.mp
    ((Submodule.mem_orthogonal _ _).mp hu.1 x hx.1)

/-- **`‖B m‖² = ⟪A m, m⟫ - ‖A m‖²`.**  The quadratic form of `B*B = A(1 - A)`,
by Pythagoras on `P_V m = A m + B m`. -/
theorem norm_sq_genericCrossBlock (m : genericLeftHalf U V) :
    ‖genericCrossBlock U V m‖ ^ 2 =
      RCLike.re ⟪genericCosineBlock U V m, m⟫_ℂ -
        ‖genericCosineBlock U V m‖ ^ 2 := by
  have hperp : ⟪((genericCosineBlock U V m : genericLeftHalf U V) : H),
      ((genericCrossBlock U V m : genericRightHalf U V) : H)⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp
      (genericLeftHalf_le_orthogonal_genericRightHalf U V
        (genericCosineBlock U V m).2) _ (genericCrossBlock U V m).2
      |> inner_eq_zero_symm.mp
  have hpy := @norm_add_sq ℂ _ _ _ _
    ((genericCosineBlock U V m : genericLeftHalf U V) : H)
    ((genericCrossBlock U V m : genericRightHalf U V) : H)
  rw [← starProjection_eq_cosineBlock_add_crossBlock U V m, hperp] at hpy
  simp only [map_zero, mul_zero, add_zero] at hpy
  have hA : ‖((genericCosineBlock U V m : genericLeftHalf U V) : H)‖ =
      ‖genericCosineBlock U V m‖ := Submodule.norm_coe _
  have hB : ‖((genericCrossBlock U V m : genericRightHalf U V) : H)‖ =
      ‖genericCrossBlock U V m‖ := Submodule.norm_coe _
  rw [hA, hB] at hpy
  rw [re_inner_genericCosineBlock]
  linarith

/-- **`B'` is the adjoint of `B`.** -/
theorem inner_genericCrossBlock (m : genericLeftHalf U V)
    (n : genericRightHalf U V) :
    ⟪genericCrossBlock U V m, n⟫_ℂ = ⟪m, genericCrossBlockMirror U V n⟫_ℂ := by
  have hBcoe : ((genericCrossBlock U V m : genericRightHalf U V) : H) =
      (genericRightHalf U V).starProjection (V.starProjection (m : H)) := by
    simp [genericCrossBlock]
  have hB'coe : ((genericCrossBlockMirror U V n : genericLeftHalf U V) : H) =
      (genericLeftHalf U V).starProjection (V.starProjection (n : H)) := by
    simp [genericCrossBlockMirror]
  calc ⟪genericCrossBlock U V m, n⟫_ℂ
      = ⟪(genericRightHalf U V).starProjection (V.starProjection (m : H)),
          (n : H)⟫_ℂ := by rw [← hBcoe]; rfl
    _ = ⟪V.starProjection (m : H),
          (genericRightHalf U V).starProjection (n : H)⟫_ℂ :=
        (genericRightHalf U V).inner_starProjection_left_eq_right _ _
    _ = ⟪V.starProjection (m : H), (n : H)⟫_ℂ := by
        rw [Submodule.starProjection_eq_self_iff.mpr n.2]
    _ = ⟪(m : H), V.starProjection (n : H)⟫_ℂ :=
        V.inner_starProjection_left_eq_right _ _
    _ = ⟪(genericLeftHalf U V).starProjection (m : H),
          V.starProjection (n : H)⟫_ℂ := by
        rw [Submodule.starProjection_eq_self_iff.mpr m.2]
    _ = ⟪(m : H), (genericLeftHalf U V).starProjection
          (V.starProjection (n : H))⟫_ℂ := by
        rw [(genericLeftHalf U V).inner_starProjection_left_eq_right]
    _ = ⟪m, genericCrossBlockMirror U V n⟫_ℂ := by rw [← hB'coe]; rfl

/-- **The cross block has dense range.**  A vector of `N` orthogonal to the
range is killed by the mirror, hence zero. -/
theorem orthogonal_range_genericCrossBlock_eq_bot :
    (LinearMap.range (genericCrossBlock U V : genericLeftHalf U V →ₗ[ℂ]
      genericRightHalf U V))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro n hn
  refine (genericCrossBlockMirror_eq_zero_iff U V n).mp ?_
  have hzero : ∀ m : genericLeftHalf U V,
      ⟪m, genericCrossBlockMirror U V n⟫_ℂ = 0 := by
    intro m
    rw [← inner_genericCrossBlock]
    exact (Submodule.mem_orthogonal _ _).mp hn _ ⟨m, rfl⟩
  have := hzero (genericCrossBlockMirror U V n)
  exact inner_self_eq_zero.mp this

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
