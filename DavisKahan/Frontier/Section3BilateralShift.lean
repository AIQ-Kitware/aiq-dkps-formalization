/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

import DavisKahan.Frontier.Section3
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The Remark after Proposition 3.2: the bilateral shift on `ℓ²(ℤ)`

Davis--Kahan 1970 attach a Remark to Proposition 3.2 whose only job is to show
that the standing dimension hypothesis (1.5) does **not** imply the crossed
defect hypothesis (3.5).  The witness is a pair of shift-related half-space
subspaces of the two-sided square-summable sequences:

* `H` is the space of square-summable sequences `(…, a₋₁, a₀, a₁, …)`;
* `P H` is the subspace of those with `aₙ = 0` for `n < 0`;
* `Q H` is the subspace of those with `aₙ = 0` for `n ≤ 0`.

Then (1.5) holds -- the bilateral shift is a unitary carrying `P H` onto `Q H`,
so it satisfies (1.4), and (1.5) follows -- while `P H ∩ Q̃ H` is the line of
sequences supported at `n = 0` and `P̃ H ∩ Q H` is zero, so (3.5) fails.  By
Proposition 3.2 the pair therefore admits no direct rotation at all.

The Hilbert space is presented as an arbitrary Hilbert space over an `RCLike`
field carrying a Hilbert basis indexed by `ℤ`; that is the same object as the
sequence space of
the Remark, and it is how the paper's coordinates `aₙ = ⟪bₙ, x⟫` are named
here.  The half-spaces are cut at an arbitrary integer `k` so that the shift
carries one to the next; the Remark is the pair `k = 0`, `k = 1`.

This example matters beyond Proposition 3.2: it is the canonical warning that
equality of two infinite ambient dimensions says nothing about equality of the
crossed defect dimensions.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section3

universe u

section BilateralShift

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-! The functional-calculus hypotheses of the nonacute existence criterion,
needed only by the final theorem, which invokes Proposition 3.2.  Typeclass
inference discharges them at `𝕜 = ℂ` and at `𝕜 = ℝ`. -/
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

omit [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- Membership in the orthogonal complement of a span is tested on the spanning
set alone. -/
theorem mem_orthogonal_span {S : Set H} {x : H} :
    x ∈ (Submodule.span 𝕜 S)ᗮ ↔ ∀ y ∈ S, ⟪y, x⟫_𝕜 = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h y hy
    exact h y (Submodule.subset_span hy)
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => exact inner_zero_left x
    | add a c _ _ ha hc => rw [inner_add_left, ha, hc, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]

omit [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **Transport of an orthogonal projection along a surjective isometry.** -/
theorem starProjection_of_map_eq {K L : Submodule 𝕜 H} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (e : H ≃ₗᵢ[𝕜] H)
    (h : K.map (e.toLinearEquiv : H →ₗ[𝕜] H) = L) (y : H) :
    L.starProjection (e y) = e (K.starProjection y) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [← h]
    exact Submodule.mem_map_of_mem (K.starProjection_apply_mem y)
  · intro w hw
    rw [← h] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    show ⟪e y - e (K.starProjection y), e u⟫_𝕜 = 0
    rw [← map_sub, e.inner_map_map]
    exact K.starProjection_inner_eq_zero y u hu

/-- **The coordinate half-space cut at `k`.**

For a Hilbert basis of `H` indexed by `ℤ` this is the closed subspace of
vectors whose coordinates `aₙ = ⟪bₙ, x⟫` vanish for every `n < k`.  The
Remark's `P H` is the cut at `0` and its `Q H` is the cut at `1`. -/
noncomputable abbrev coordinateHalfSpace (b : HilbertBasis ℤ 𝕜 H) (k : ℤ) :
    Submodule 𝕜 H :=
  (Submodule.span 𝕜 (b '' {n : ℤ | n < k}))ᗮ

omit [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- Coordinate description of a coordinate half-space. -/
theorem mem_coordinateHalfSpace {b : HilbertBasis ℤ 𝕜 H} {k : ℤ} {x : H} :
    x ∈ coordinateHalfSpace b k ↔ ∀ n : ℤ, n < k → ⟪b n, x⟫_𝕜 = 0 := by
  rw [mem_orthogonal_span]
  constructor
  · intro h n hn
    exact h (b n) ⟨n, hn, rfl⟩
  · rintro h _ ⟨n, hn, rfl⟩
    exact h n hn

omit [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- The orthogonal complement of a coordinate half-space kills every coordinate
at or above the cut. -/
theorem inner_eq_zero_of_mem_orthogonal_coordinateHalfSpace
    {b : HilbertBasis ℤ 𝕜 H} {k : ℤ} {x : H}
    (hx : x ∈ (coordinateHalfSpace b k)ᗮ) {n : ℤ} (hn : k ≤ n) :
    ⟪b n, x⟫_𝕜 = 0 := by
  have hle : Submodule.span 𝕜 (b '' {m : ℤ | m < k}) ≤
      (Submodule.span 𝕜 (b '' {m : ℤ | k ≤ m}))ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    refine mem_orthogonal_span.mpr ?_
    rintro _ ⟨p, hp, rfl⟩
    simp only [Set.mem_ofPred_eq] at hm hp
    exact b.orthonormal.2 (by omega)
  have hmono := Submodule.orthogonal_orthogonal_monotone hle
  rw [Submodule.triorthogonal_eq_orthogonal] at hmono
  exact mem_orthogonal_span.mp (hmono hx) (b n) ⟨n, hn, rfl⟩

/-! ### The shift -/

omit [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- Shifting the index by one permutes a Hilbert basis, so the shifted family
has the same range. -/
theorem range_comp_add_one (b : HilbertBasis ℤ 𝕜 H) :
    Set.range (fun n : ℤ => b (n + 1)) = Set.range b := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n - 1, by simp⟩

/-- The Hilbert basis obtained from `b` by shifting the index by one. -/
noncomputable def shiftedBasis (b : HilbertBasis ℤ 𝕜 H) : HilbertBasis ℤ 𝕜 H :=
  HilbertBasis.mk (v := fun n : ℤ => b (n + 1))
    (b.orthonormal.comp (fun n : ℤ => n + 1) fun m n h => by simpa using h)
    (by
      rw [range_comp_add_one b]
      exact b.dense_span.ge)

omit [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint] [Algebra ℝ (H →L[𝕜] H)]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- The shifted basis is the shift of the basis. -/
theorem shiftedBasis_apply (b : HilbertBasis ℤ 𝕜 H) (n : ℤ) :
    shiftedBasis b n = b (n + 1) :=
  congrFun (HilbertBasis.coe_mk _ _) n

/-- **The bilateral shift.**

The unitary carrying the `n`-th basis vector to the `(n+1)`-st; in the sequence
coordinates of the Remark this is `V (aₙ) = (bₙ)` with `bₙ = aₙ₋₁`. -/
noncomputable def bilateralShift (b : HilbertBasis ℤ 𝕜 H) : H ≃ₗᵢ[𝕜] H :=
  b.repr.trans (shiftedBasis b).repr.symm

omit [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint] [Algebra ℝ (H →L[𝕜] H)]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- The bilateral shift moves each basis vector one step up. -/
theorem bilateralShift_apply_basis (b : HilbertBasis ℤ 𝕜 H) (n : ℤ) :
    bilateralShift b (b n) = b (n + 1) := by
  classical
  have h : (shiftedBasis b).repr.symm (b.repr (b n)) = shiftedBasis b n := by
    rw [b.repr_self]
    exact (shiftedBasis b).repr_symm_single n
  rw [bilateralShift, LinearIsometryEquiv.trans_apply, h, shiftedBasis_apply]

/-- The bilateral shift as a bounded operator. -/
noncomputable def bilateralShiftL (b : HilbertBasis ℤ 𝕜 H) : H →L[𝕜] H :=
  (bilateralShift b : H →L[𝕜] H)

omit [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint] [Algebra ℝ (H →L[𝕜] H)]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- The bilateral shift is unitary. -/
theorem bilateralShiftL_mem_unitary (b : HilbertBasis ℤ 𝕜 H) :
    bilateralShiftL b ∈ unitary (H →L[𝕜] H) :=
  (Unitary.linearIsometryEquiv.symm (bilateralShift b)).property

omit [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint] [Algebra ℝ (H →L[𝕜] H)]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **The bilateral shift carries each coordinate half-space onto the next.** -/
theorem map_coordinateHalfSpace (b : HilbertBasis ℤ 𝕜 H) (k : ℤ) :
    (coordinateHalfSpace b k).map
        ((bilateralShift b).toLinearEquiv : H →ₗ[𝕜] H) =
      coordinateHalfSpace b (k + 1) := by
  rw [Submodule.map_orthogonal_equiv, Submodule.map_span]
  congr 2
  ext x
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨n + 1, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq] at hn ⊢
      omega
    · exact (bilateralShift_apply_basis b n).symm
  · rintro ⟨n, hn, rfl⟩
    refine ⟨b (n - 1), ⟨n - 1, ?_, rfl⟩, ?_⟩
    · simp only [Set.mem_ofPred_eq] at hn ⊢
      omega
    · show (bilateralShift b) (b (n - 1)) = b n
      rw [bilateralShift_apply_basis, sub_add_cancel]

omit [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint] [Algebra ℝ (H →L[𝕜] H)]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **The bilateral shift satisfies (1.4) for the shift pair.**

`V P = Q V`, with `P` the projector onto the cut at `k` and `Q` the projector
onto the cut at `k+1`. -/
theorem bilateralShiftL_intertwines (b : HilbertBasis ℤ 𝕜 H) (k : ℤ) :
    bilateralShiftL b * projection (coordinateHalfSpace b k) =
      projection (coordinateHalfSpace b (k + 1)) * bilateralShiftL b := by
  ext y
  simp only [mul_apply_eq_comp]
  exact (starProjection_of_map_eq (bilateralShift b)
    (map_coordinateHalfSpace b k) y).symm

omit [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint] [Algebra ℝ (H →L[𝕜] H)]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **(1.5) for the shift pair**, in the cardinal-free form used throughout this
development: the two subspaces are isometrically equivalent, and so are their
orthogonal complements. -/
theorem coordinateHalfSpace_dimensions_agree (b : HilbertBasis ℤ 𝕜 H) (k : ℤ) :
    Nonempty (coordinateHalfSpace b k ≃ₗᵢ[𝕜] coordinateHalfSpace b (k + 1)) ∧
      Nonempty ((coordinateHalfSpace b k)ᗮ ≃ₗᵢ[𝕜]
        (coordinateHalfSpace b (k + 1))ᗮ) := by
  constructor
  · exact ⟨((bilateralShift b).submoduleMap (coordinateHalfSpace b k)).trans
      (LinearIsometryEquiv.ofEq _ _ (map_coordinateHalfSpace b k))⟩
  · refine ⟨((bilateralShift b).submoduleMap (coordinateHalfSpace b k)ᗮ).trans
      (LinearIsometryEquiv.ofEq _ _ ?_)⟩
    have h := Submodule.map_orthogonal_equiv (K := coordinateHalfSpace b k)
      (bilateralShift b)
    rw [map_coordinateHalfSpace] at h
    exact h

/-! ### The two crossed defects of the shift pair -/

omit [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **The source crossed intersection of the shift pair is a line.**

`P H ∩ Q̃ H` is exactly the set of sequences supported at `n = 0`, which is the
Remark's computation that `P Q̃` is the projector onto that line. -/
theorem halmosSourceDefect_coordinateHalfSpace (b : HilbertBasis ℤ 𝕜 H) :
    halmosSourceDefect (coordinateHalfSpace b 0) (coordinateHalfSpace b 1) =
      Submodule.span 𝕜 {b 0} := by
  apply le_antisymm
  · rintro x ⟨hxU, hxV⟩
    have hsupp : ∀ n : ℤ, n ≠ 0 → b.repr x n • b n = 0 := by
      intro n hn
      rcases lt_or_gt_of_ne hn with h | h
      · rw [b.repr_apply_apply, mem_coordinateHalfSpace.mp hxU n (by omega),
          zero_smul]
      · rw [b.repr_apply_apply,
          inner_eq_zero_of_mem_orthogonal_coordinateHalfSpace hxV (by omega),
          zero_smul]
    have hx : x = b.repr x 0 • b 0 :=
      (b.hasSum_repr x).unique (hasSum_single 0 hsupp)
    exact Submodule.mem_span_singleton.mpr ⟨b.repr x 0, hx.symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine mem_halmosSourceDefect.mpr
      ⟨mem_coordinateHalfSpace.mpr fun n hn => b.orthonormal.2 (by omega), ?_⟩
    exact Submodule.le_orthogonal_orthogonal _
      (Submodule.subset_span ⟨0, by norm_num, rfl⟩)

omit [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **The target crossed intersection of the shift pair is zero.**

`P̃ H ∩ Q H` is zero, which is the Remark's computation that `P̃ Q = 0`. -/
theorem halmosTargetDefect_coordinateHalfSpace (b : HilbertBasis ℤ 𝕜 H) :
    halmosTargetDefect (coordinateHalfSpace b 0) (coordinateHalfSpace b 1) =
      ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro x ⟨hxU, hxV⟩
  have hall : ∀ n : ℤ, b.repr x n = 0 := by
    intro n
    rw [b.repr_apply_apply]
    by_cases h : 0 ≤ n
    · exact inner_eq_zero_of_mem_orthogonal_coordinateHalfSpace hxU h
    · exact mem_coordinateHalfSpace.mp hxV n (by omega)
  have hrepr : b.repr x = 0 := by
    ext n
    simpa using hall n
  exact b.repr.injective (hrepr.trans (map_zero b.repr).symm)

omit [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint] [Algebra ℝ (H →L[𝕜] H)]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **(3.5) fails for the shift pair.**

The two crossed intersections cannot be isometrically identified: one is a line
and the other is zero. -/
theorem not_crossedDefectsEquivalent_coordinateHalfSpace
    (b : HilbertBasis ℤ 𝕜 H) :
    ¬ CrossedDefectsEquivalent (coordinateHalfSpace b 0)
        (coordinateHalfSpace b 1) := by
  rintro ⟨J⟩
  have hb0 : b 0 ∈ halmosSourceDefect (coordinateHalfSpace b 0)
      (coordinateHalfSpace b 1) := by
    rw [halmosSourceDefect_coordinateHalfSpace]
    exact Submodule.mem_span_singleton_self _
  have hJz : J ⟨b 0, hb0⟩ = 0 :=
    Subtype.ext ((Submodule.eq_bot_iff _).mp
      (halmosTargetDefect_coordinateHalfSpace b) _ (J ⟨b 0, hb0⟩).2)
  have hnorm : ‖b 0‖ = 0 := by
    have h := J.norm_map ⟨b 0, hb0⟩
    rw [hJz, norm_zero] at h
    exact h.symm
  rw [b.orthonormal.1 0] at hnorm
  exact one_ne_zero hnorm

/-- **Davis--Kahan 1970, the Remark after Proposition 3.2.**

For the shift pair on the two-sided square-summable sequences, the bilateral
shift is a unitary satisfying (1.4), hence (1.5) holds; but the two crossed
intersections are a line and zero, so (3.5) fails, and by Proposition 3.2 the
pair admits no direct rotation whatever.

This is the source's own separation of (1.5) from (3.5). -/
theorem remark3_2_bilateralShift_separates_dimensionHypotheses
    (b : HilbertBasis ℤ 𝕜 H) :
    (bilateralShiftL b ∈ unitary (H →L[𝕜] H) ∧
        bilateralShiftL b * projection (coordinateHalfSpace b 0) =
          projection (coordinateHalfSpace b 1) * bilateralShiftL b) ∧
      (Nonempty (coordinateHalfSpace b 0 ≃ₗᵢ[𝕜] coordinateHalfSpace b 1) ∧
        Nonempty ((coordinateHalfSpace b 0)ᗮ ≃ₗᵢ[𝕜]
          (coordinateHalfSpace b 1)ᗮ)) ∧
      halmosSourceDefect (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) ≠ ⊥ ∧
      halmosTargetDefect (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) = ⊥ ∧
      ¬ ∃ T : H →L[𝕜] H,
        IsPaperDirectRotation (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) T := by
  refine ⟨⟨bilateralShiftL_mem_unitary b, ?_⟩, ?_, ?_,
    halmosTargetDefect_coordinateHalfSpace b, ?_⟩
  · have h := bilateralShiftL_intertwines b 0
    rwa [zero_add] at h
  · have h := coordinateHalfSpace_dimensions_agree b 0
    rwa [zero_add] at h
  · rw [halmosSourceDefect_coordinateHalfSpace]
    intro hbot
    have hb : b 0 = 0 := (Submodule.eq_bot_iff _).mp hbot (b 0)
      (Submodule.mem_span_singleton_self _)
    have hnorm : ‖b 0‖ = 0 := by rw [hb, norm_zero]
    rw [b.orthonormal.1 0] at hnorm
    exact one_ne_zero hnorm
  · intro h
    exact not_crossedDefectsEquivalent_coordinateHalfSpace b
      ((proposition3_2_exists_iff_crossedDefectsEquivalent _ _).mp h)

end BilateralShift

/-! ## The Remark over a real Hilbert space

Standing assumption 1 of Davis--Kahan 1970 admits real Hilbert spaces, and the
Remark is a statement about `ℓ²(ℤ)` in that scope too: nothing above uses the
complex structure, so the whole module is stated over an arbitrary `RCLike`
field and the real form is the `𝕜 = ℝ` instance, grounded on the generic
theorem by `:=` and carrying exactly its hypotheses.

Over `ℝ` the ambient space is the two-sided real square-summable sequences,
presented, as over `ℂ`, as any real Hilbert space carrying a `HilbertBasis ℤ ℝ`.
-/

section RealScalars

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- **Davis--Kahan 1970, the Remark after Proposition 3.2, over a real Hilbert
space.**

The `𝕜 = ℝ` instance of
`remark3_2_bilateralShift_separates_dimensionHypotheses`: the bilateral shift
witnesses (1.4), hence (1.5), while the crossed intersections are a line and
zero, so (3.5) fails and the pair admits no direct rotation. -/
theorem remark3_2_bilateralShift_separates_dimensionHypotheses_real
    (b : HilbertBasis ℤ ℝ E) :
    (bilateralShiftL b ∈ unitary (E →L[ℝ] E) ∧
        bilateralShiftL b * projection (coordinateHalfSpace b 0) =
          projection (coordinateHalfSpace b 1) * bilateralShiftL b) ∧
      (Nonempty (coordinateHalfSpace b 0 ≃ₗᵢ[ℝ] coordinateHalfSpace b 1) ∧
        Nonempty ((coordinateHalfSpace b 0)ᗮ ≃ₗᵢ[ℝ]
          (coordinateHalfSpace b 1)ᗮ)) ∧
      halmosSourceDefect (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) ≠ ⊥ ∧
      halmosTargetDefect (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) = ⊥ ∧
      ¬ ∃ T : E →L[ℝ] E,
        IsPaperDirectRotation (coordinateHalfSpace b 0)
          (coordinateHalfSpace b 1) T :=
  remark3_2_bilateralShift_separates_dimensionHypotheses b

end RealScalars

end Section3
end Frontier
end Experimental
end DavisKahan
end TauCeti
