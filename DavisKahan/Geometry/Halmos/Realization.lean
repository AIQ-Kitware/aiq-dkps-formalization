/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Geometry.Halmos.TwoProjections
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Davis--Kahan 1970, Theorem 3.1: the realization half

`GenericReconstruction.lean` and `CompactClassification.lean` prove the
*classification* half of Theorem 3.1: two ordered pairs of subspaces carrying the
same angle datum are unitarily equivalent as pairs.  This module proves the
*realization* half — the paper's sentence (ii): a prescribed admissible angle
datum is actually attained by a concrete pair of subspaces.

## The construction

Fix two complex Hilbert spaces `E` and `F`, to be read as `P H` and `Pᗮ H`, and
work in their `L²` direct sum `WithLp 2 (E × F)`.  The first subspace is the
`E`-factor,

`U := range modelInl = {(x, 0)}`,

and the second is the image of `U` under the direct rotation, i.e. the range of
the isometry

`W₀ : E → WithLp 2 (E × F)`,  `W₀ x = (C₀ x, J S₀ x)`,

where `C₀ = cos Θ₀` and `S₀ = sin Θ₀` are the prescribed angle data on the
`P`-side and `J` is the intertwiner supplied by the spectral classification.
`W₀` is isometric because `J` is isometric on the range of `S₀`, so
`V := range W₀` is a closed subspace and `P_V = W₀ W₀⋆`.

## The block matrix

Writing `C₁ = cos Θ₁`, `S₁ = sin Θ₁` on the `Pᗮ`-side, the resulting projection is

```text
P_V = [[ C₀ C₀   , C₀ S₀ J⋆ ],
       [ J S₀ C₀ , S₁ S₁    ]]
```

which is `starProjection_targetSubspace_apply` below.  Both off-diagonal entries
are positive, as they must be for a self-adjoint operator; here that is
structural rather than checked, since `starProjection` is self-adjoint by
construction.

This agrees with the source.  Equation (3.7) of the original prints
`Q = U P U⁻¹ ≃ [[C₀², C₀S₀⋆], [S₀C₀, S₀S₀⋆]]`, with both off-diagonal entries
positive; the minus sign appears only in the second column of the direct
rotation `U` at (3.6).  An earlier campaign note claiming a sign defect here was
withdrawn after checking the original scan; see
`dev/external-literature-references.md`, "Known source errata".

## Why the angle `0` is exceptional and the angle `π/2` is not

This is the mathematical content of the hypothesis of Theorem 3.1, and it is
proved here rather than asserted.  The four elementary Halmos summands of the
constructed pair are computed exactly:

* `halmosCommonPart_eq`  : `U ⊓ V   = modelInl '' ker S₀`;
* `halmosExteriorPart_eq`: `Uᗮ ⊓ Vᗮ = modelInr '' ker S₁`;
* `halmosSourceDefect_eq`: `U ⊓ Vᗮ  = modelInl '' ker C₀`;
* `halmosTargetDefect_eq`: `Uᗮ ⊓ V  = modelInr '' ker C₁`.

For an angle operator with spectrum in `[0, π/2]`, `ker S₀` is the eigenspace at
`0` and `ker C₀` the eigenspace at `π/2`.  So:

* the two `0`-eigenspaces land in the two *uncrossed* intersections `U ⊓ V` and
  `Uᗮ ⊓ Vᗮ`, and nothing relates them — `trivialHalmosAngleDatum` realizes
  `ker S₀ = E` and `ker S₁ = F` for **arbitrary** `E` and `F`, so the
  multiplicity at angle `0` genuinely may differ between the two sides;
* the two `π/2`-eigenspaces land in the *crossed* defects `U ⊓ Vᗮ` and
  `Uᗮ ⊓ V`, and `J` restricts to a linear isometric equivalence
  `ker C₀ ≃ₗᵢ ker C₁` (`crossedDefectEquiv`), so the multiplicity at `π/2` must
  agree.  Geometrically this is forced: a unitary of the ambient space carrying
  `U` onto `V` exists only when `dim (U ⊓ Vᗮ) = dim (Uᗮ ⊓ V)`.

## Generality

Arbitrary complex Hilbert spaces `E`, `F`: no compactness, no finite dimension,
no separability, and — as it turns out — no positivity.  The angle datum is
recorded by the *pair* `(cos Θ, sin Θ)` through the algebraic relations it
satisfies (self-adjoint, commuting, `C² + S² = 1`), which is all the
construction consumes.  Positivity of `C` and `S`, i.e. the restriction of the
angle to `[0, π/2]`, is what makes `ker S` the angle-`0` space and `ker C` the
angle-`π/2` space, and so belongs to the *reading* of the theorem rather than to
its proof.

## Main results

* `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum`
* `..._starProjection_targetSubspace_apply` — the block matrix of (3.7)
* `..._compress_source_eq` and `..._compress_sourceOrthogonal_eq` — the realized
  pair has the prescribed `cos² Θ₀` and `cos² Θ₁`
* `..._halmosCommonPart_eq`, `..._halmosSourceDefect_eq`,
  `..._halmosTargetDefect_eq`, `..._halmosExteriorPart_eq`
* `..._crossedDefectEquiv` and
  `..._nonempty_halmosSourceDefect_equiv_targetDefect`
* `..._trivialHalmosAngleDatum` with `..._trivial_halmosCommonPart_eq` and
  `..._trivial_halmosExteriorPart_eq`
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

universe u v

/-! ## Preliminaries -/

section Preliminaries

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- Two vectors of two inner product spaces with the same self-inner product have
the same norm.  Used repeatedly to promote an operator identity to an isometry
statement without leaving the inner product. -/
theorem norm_eq_norm_of_inner_self_eq {a : A} {b : B}
    (h : ⟪a, a⟫_ℂ = ⟪b, b⟫_ℂ) : ‖a‖ = ‖b‖ := by
  have h2 : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), h]
  exact (sq_eq_sq₀ (norm_nonneg a) (norm_nonneg b)).mp h2

end Preliminaries

/-! ## The model space `E ⊕₂ F` and its first factor -/

section Model

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (F : Type v) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The inclusion of the first factor into the `L²` direct sum. -/
noncomputable def modelInl : E →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℂ E F

/-- The inclusion of the second factor into the `L²` direct sum. -/
noncomputable def modelInr : F →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ E F

variable {E F}

omit [CompleteSpace E] [CompleteSpace F] in
/-- The first inclusion in coordinates. -/
@[simp]
theorem modelInl_apply (x : E) : modelInl E F x = WithLp.toLp 2 (x, (0 : F)) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The second inclusion in coordinates. -/
@[simp]
theorem modelInr_apply (y : F) : modelInr E F y = WithLp.toLp 2 ((0 : E), y) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The first inclusion is isometric. -/
theorem norm_modelInl (x : E) : ‖modelInl E F x‖ = ‖x‖ :=
  norm_eq_norm_of_inner_self_eq (by simp)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The second inclusion is isometric. -/
theorem norm_modelInr (y : F) : ‖modelInr E F y‖ = ‖y‖ :=
  norm_eq_norm_of_inner_self_eq (by simp)

omit [CompleteSpace E] [CompleteSpace F] in
/-- A vector with vanishing second component is in the first factor. -/
theorem eq_modelInl_of_snd_eq_zero {z : WithLp 2 (E × F)} (h : (WithLp.ofLp z).2 = 0) :
    z = modelInl E F (WithLp.ofLp z).1 := by
  rw [modelInl_apply, ← h]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A vector with vanishing first component is in the second factor. -/
theorem eq_modelInr_of_fst_eq_zero {z : WithLp 2 (E × F)} (h : (WithLp.ofLp z).1 = 0) :
    z = modelInr E F (WithLp.ofLp z).2 := by
  rw [modelInr_apply, ← h]

/-- The adjoint of the first inclusion is the first projection. -/
theorem adjoint_modelInl :
    ContinuousLinearMap.adjoint (modelInl E F) = WithLp.fstL 2 ℂ E F :=
  ((ContinuousLinearMap.eq_adjoint_iff (WithLp.fstL 2 ℂ E F) (modelInl E F)).mpr
    (by intro z x; simp)).symm

/-- The adjoint of the second inclusion is the second projection. -/
theorem adjoint_modelInr :
    ContinuousLinearMap.adjoint (modelInr E F) = WithLp.sndL 2 ℂ E F :=
  ((ContinuousLinearMap.eq_adjoint_iff (WithLp.sndL 2 ℂ E F) (modelInr E F)).mpr
    (by intro z y; simp)).symm

/-- A norm-preserving continuous linear map out of a complete space has closed,
hence complete, range. -/
theorem completeSpace_range_of_norm_map {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] (f : E →L[ℂ] G) (hf : ∀ x, ‖f x‖ = ‖x‖) :
    CompleteSpace (LinearMap.range (f : E →ₗ[ℂ] G)) := by
  have hiso : Isometry (f : E → G) := AddMonoidHomClass.isometry_of_norm f hf
  have hclosed : IsClosed (Set.range (f : E → G)) := hiso.isClosedEmbedding.isClosed_range
  have hcl : IsClosed ((LinearMap.range (f : E →ₗ[ℂ] G) : Submodule ℂ G) : Set G) := by
    simpa [LinearMap.coe_range] using hclosed
  exact hcl.completeSpace_coe

omit [CompleteSpace E] in
/-- A norm-preserving continuous linear map is injective. -/
theorem injective_of_norm_map {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (f : E →L[ℂ] G) (hf : ∀ x, ‖f x‖ = ‖x‖) :
    Function.Injective (f : E →ₗ[ℂ] G) := by
  intro a b hab
  have hz : ‖a - b‖ = 0 := by
    rw [← hf, map_sub]
    simp only [ContinuousLinearMap.coe_coe] at hab
    rw [hab, sub_self, norm_zero]
  simpa [sub_eq_zero] using norm_eq_zero.mp hz

/-- A norm-preserving continuous linear map carries a submodule isometrically onto
its image. -/
noncomputable def submoduleMapIsometry {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (f : E →L[ℂ] G) (hf : ∀ x, ‖f x‖ = ‖x‖) (K : Submodule ℂ E) :
    K ≃ₗᵢ[ℂ] Submodule.map (f : E →ₗ[ℂ] G) K :=
  { Submodule.equivMapOfInjective (f : E →ₗ[ℂ] G) (injective_of_norm_map f hf) K with
    norm_map' := fun x => by
      have h := Submodule.coe_equivMapOfInjective_apply (f : E →ₗ[ℂ] G)
        (injective_of_norm_map f hf) K x
      calc ‖(Submodule.equivMapOfInjective (f : E →ₗ[ℂ] G)
              (injective_of_norm_map f hf) K) x‖
          = ‖(((Submodule.equivMapOfInjective (f : E →ₗ[ℂ] G)
              (injective_of_norm_map f hf) K) x : Submodule.map (f : E →ₗ[ℂ] G) K) : G)‖ := rfl
        _ = ‖f (x : E)‖ := by rw [h]; simp
        _ = ‖(x : E)‖ := hf _
        _ = ‖x‖ := rfl }

variable (E F)

/-- **The first subspace of the realized pair**: the `E`-factor, i.e. `P H`. -/
noncomputable def sourceSubspace : Submodule ℂ (WithLp 2 (E × F)) :=
  LinearMap.range (modelInl E F : E →ₗ[ℂ] WithLp 2 (E × F))

/-- The `E`-factor is complete, being the isometric image of a complete space. -/
noncomputable instance : CompleteSpace (sourceSubspace E F) :=
  completeSpace_range_of_norm_map _ norm_modelInl

variable {E F}

omit [CompleteSpace E] [CompleteSpace F] in
/-- Membership in the `E`-factor is the vanishing of the second component. -/
theorem mem_sourceSubspace_iff (z : WithLp 2 (E × F)) :
    z ∈ sourceSubspace E F ↔ (WithLp.ofLp z).2 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [modelInl]
  · intro h
    exact ⟨(WithLp.ofLp z).1, (eq_modelInl_of_snd_eq_zero h).symm⟩

/-- The orthogonal complement of the `E`-factor is the kernel of the first projection. -/
theorem sourceSubspace_orthogonal :
    (sourceSubspace E F)ᗮ = LinearMap.ker (WithLp.fstL 2 ℂ E F : _ →ₗ[ℂ] E) := by
  rw [sourceSubspace, ContinuousLinearMap.orthogonal_range, adjoint_modelInl]

/-- Membership in the `F`-factor is the vanishing of the first component. -/
theorem mem_sourceSubspace_orthogonal_iff (z : WithLp 2 (E × F)) :
    z ∈ (sourceSubspace E F)ᗮ ↔ (WithLp.ofLp z).1 = 0 := by
  rw [sourceSubspace_orthogonal]
  simp [LinearMap.mem_ker]

/-- The orthogonal projection onto the `E`-factor discards the second component. -/
theorem starProjection_sourceSubspace (z : WithLp 2 (E × F)) :
    (sourceSubspace E F).starProjection z = modelInl E F (WithLp.ofLp z).1 := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ⟨(WithLp.ofLp z).1, rfl⟩ ?_
  rw [mem_sourceSubspace_orthogonal_iff]
  simp [modelInl]

/-- The orthogonal projection onto the `F`-factor discards the first component. -/
theorem starProjection_sourceSubspace_orthogonal (z : WithLp 2 (E × F)) :
    (sourceSubspace E F)ᗮ.starProjection z = modelInr E F (WithLp.ofLp z).2 := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [mem_sourceSubspace_orthogonal_iff]
    simp [modelInr]
  · rw [Submodule.orthogonal_orthogonal, mem_sourceSubspace_iff]
    simp [modelInr]

end Model

/-! ## Admissible angle data -/

/-- **A prescribed admissible angle datum for Davis--Kahan Theorem 3.1.**

`cos₀, sin₀` are `cos Θ₀, sin Θ₀` on the `P`-side, `cos₁, sin₁` are
`cos Θ₁, sin Θ₁` on the `Pᗮ`-side, and `intertwiner` is the map `J₀` supplied by
the spectral classification: a partial isometry whose initial space is
`(ker sin₀)ᗮ` and whose final space is `(ker sin₁)ᗮ`, intertwining the two angle
operators.

The last two fields record exactly the partial-isometry content that the
construction uses: `J₀` is isometric on the range of `sin₀` and co-isometric onto
the range of `sin₁`.  Together with the two intertwining fields they say that
`J₀` matches the spectral multiplicities of `Θ₀` and `Θ₁` at every angle *except*
`0`.  Angle `0` lies outside `J₀`'s initial and final spaces, which is exactly
why Theorem 3.1 permits the multiplicity at `0` to differ. -/
structure HalmosAngleDatum (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] where
  /-- `cos Θ₀`, the cosine of the angle operator on the `P`-side. -/
  cos₀ : E →L[ℂ] E
  /-- `sin Θ₀`, the sine of the angle operator on the `P`-side. -/
  sin₀ : E →L[ℂ] E
  /-- `cos Θ₁`, the cosine of the angle operator on the `Pᗮ`-side. -/
  cos₁ : F →L[ℂ] F
  /-- `sin Θ₁`, the sine of the angle operator on the `Pᗮ`-side. -/
  sin₁ : F →L[ℂ] F
  /-- `J₀`, the intertwiner supplied by the spectral classification. -/
  intertwiner : E →L[ℂ] F
  /-- `cos Θ₀` is self-adjoint. -/
  isSelfAdjoint_cos₀ : IsSelfAdjoint cos₀
  /-- `sin Θ₀` is self-adjoint. -/
  isSelfAdjoint_sin₀ : IsSelfAdjoint sin₀
  /-- `cos Θ₁` is self-adjoint. -/
  isSelfAdjoint_cos₁ : IsSelfAdjoint cos₁
  /-- `sin Θ₁` is self-adjoint. -/
  isSelfAdjoint_sin₁ : IsSelfAdjoint sin₁
  /-- The two `P`-side angle functions commute. -/
  commute₀ : cos₀ ∘L sin₀ = sin₀ ∘L cos₀
  /-- The two `Pᗮ`-side angle functions commute. -/
  commute₁ : cos₁ ∘L sin₁ = sin₁ ∘L cos₁
  /-- `cos² Θ₀ + sin² Θ₀ = 1`. -/
  pythagoras₀ : cos₀ ∘L cos₀ + sin₀ ∘L sin₀ = 1
  /-- `cos² Θ₁ + sin² Θ₁ = 1`. -/
  pythagoras₁ : cos₁ ∘L cos₁ + sin₁ ∘L sin₁ = 1
  /-- `J₀ cos Θ₀ = cos Θ₁ J₀`. -/
  map_cos : intertwiner ∘L cos₀ = cos₁ ∘L intertwiner
  /-- `J₀ sin Θ₀ = sin Θ₁ J₀`. -/
  map_sin : intertwiner ∘L sin₀ = sin₁ ∘L intertwiner
  /-- `J₀` is isometric on the range of `sin Θ₀`. -/
  isometry_on_sin₀ :
    ContinuousLinearMap.adjoint intertwiner ∘L intertwiner ∘L sin₀ = sin₀
  /-- `J₀` is co-isometric onto the range of `sin Θ₁`. -/
  coisometry_on_sin₁ :
    intertwiner ∘L ContinuousLinearMap.adjoint intertwiner ∘L sin₁ = sin₁

namespace HalmosAngleDatum

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (d : HalmosAngleDatum E F)

/-! ### Pointwise forms of the datum's relations -/

/-- `cos Θ₀` moves across the inner product. -/
theorem inner_cos₀ (x y : E) : ⟪d.cos₀ x, y⟫_ℂ = ⟪x, d.cos₀ y⟫_ℂ := by
  conv_lhs => rw [← ContinuousLinearMap.isSelfAdjoint_iff'.mp d.isSelfAdjoint_cos₀]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- `sin Θ₀` moves across the inner product. -/
theorem inner_sin₀ (x y : E) : ⟪d.sin₀ x, y⟫_ℂ = ⟪x, d.sin₀ y⟫_ℂ := by
  conv_lhs => rw [← ContinuousLinearMap.isSelfAdjoint_iff'.mp d.isSelfAdjoint_sin₀]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- `cos Θ₁` moves across the inner product. -/
theorem inner_cos₁ (x y : F) : ⟪d.cos₁ x, y⟫_ℂ = ⟪x, d.cos₁ y⟫_ℂ := by
  conv_lhs => rw [← ContinuousLinearMap.isSelfAdjoint_iff'.mp d.isSelfAdjoint_cos₁]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- `sin Θ₁` moves across the inner product. -/
theorem inner_sin₁ (x y : F) : ⟪d.sin₁ x, y⟫_ℂ = ⟪x, d.sin₁ y⟫_ℂ := by
  conv_lhs => rw [← ContinuousLinearMap.isSelfAdjoint_iff'.mp d.isSelfAdjoint_sin₁]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The `P`-side commutation, at a vector. -/
theorem commute₀_apply (x : E) : d.cos₀ (d.sin₀ x) = d.sin₀ (d.cos₀ x) :=
  congrArg (fun f : E →L[ℂ] E => f x) d.commute₀

/-- The `Pᗮ`-side commutation, at a vector. -/
theorem commute₁_apply (y : F) : d.cos₁ (d.sin₁ y) = d.sin₁ (d.cos₁ y) :=
  congrArg (fun f : F →L[ℂ] F => f y) d.commute₁

/-- The `P`-side Pythagorean identity, at a vector. -/
theorem pythagoras₀_apply (x : E) : d.cos₀ (d.cos₀ x) + d.sin₀ (d.sin₀ x) = x :=
  congrArg (fun f : E →L[ℂ] E => f x) d.pythagoras₀

/-- The `Pᗮ`-side Pythagorean identity, at a vector. -/
theorem pythagoras₁_apply (y : F) : d.cos₁ (d.cos₁ y) + d.sin₁ (d.sin₁ y) = y :=
  congrArg (fun f : F →L[ℂ] F => f y) d.pythagoras₁

/-- The cosine intertwining, at a vector. -/
theorem map_cos_apply (x : E) : d.intertwiner (d.cos₀ x) = d.cos₁ (d.intertwiner x) :=
  congrArg (fun f : E →L[ℂ] F => f x) d.map_cos

/-- The sine intertwining, at a vector. -/
theorem map_sin_apply (x : E) : d.intertwiner (d.sin₀ x) = d.sin₁ (d.intertwiner x) :=
  congrArg (fun f : E →L[ℂ] F => f x) d.map_sin

/-- `J₀⋆ J₀` is the identity on the range of `sin Θ₀`, at a vector. -/
theorem isometry_on_sin₀_apply (x : E) :
    ContinuousLinearMap.adjoint d.intertwiner (d.intertwiner (d.sin₀ x)) = d.sin₀ x :=
  congrArg (fun f : E →L[ℂ] E => f x) d.isometry_on_sin₀

/-- `J₀ J₀⋆` is the identity on the range of `sin Θ₁`, at a vector. -/
theorem coisometry_on_sin₁_apply (y : F) :
    d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y)) = d.sin₁ y :=
  congrArg (fun f : F →L[ℂ] F => f y) d.coisometry_on_sin₁

/-- The angle-`π/2` eigenspace lies in the range of `sin Θ₀`. -/
theorem sin₀_sin₀_of_cos₀_eq_zero {x : E} (hx : d.cos₀ x = 0) :
    d.sin₀ (d.sin₀ x) = x := by
  have h := d.pythagoras₀_apply x
  rw [hx, map_zero, zero_add] at h
  exact h

/-- The angle-`π/2` eigenspace lies in the range of `sin Θ₁`. -/
theorem sin₁_sin₁_of_cos₁_eq_zero {y : F} (hy : d.cos₁ y = 0) :
    d.sin₁ (d.sin₁ y) = y := by
  have h := d.pythagoras₁_apply y
  rw [hy, map_zero, zero_add] at h
  exact h

/-- `J₀` preserves the norm on the range of `sin Θ₀`. -/
theorem norm_intertwiner_sin₀ (x : E) :
    ‖d.intertwiner (d.sin₀ x)‖ = ‖d.sin₀ x‖ := by
  refine norm_eq_norm_of_inner_self_eq (A := F) (B := E) ?_
  rw [← ContinuousLinearMap.adjoint_inner_right, d.isometry_on_sin₀_apply]

/-! ### Adjoint transport

The intertwining relations, moved across the adjoint of `J₀`.  These are the
identities that make the `Pᗮ`-side of the construction close. -/

/-- `cos Θ₀ J₀⋆ = J₀⋆ cos Θ₁`. -/
theorem cos₀_adjoint_intertwiner (y : F) :
    d.cos₀ (ContinuousLinearMap.adjoint d.intertwiner y) =
      ContinuousLinearMap.adjoint d.intertwiner (d.cos₁ y) := by
  refine ext_inner_right ℂ fun x => ?_
  calc ⟪d.cos₀ (ContinuousLinearMap.adjoint d.intertwiner y), x⟫_ℂ
      = ⟪ContinuousLinearMap.adjoint d.intertwiner y, d.cos₀ x⟫_ℂ := d.inner_cos₀ _ _
    _ = ⟪y, d.intertwiner (d.cos₀ x)⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪y, d.cos₁ (d.intertwiner x)⟫_ℂ := by rw [d.map_cos_apply]
    _ = ⟪d.cos₁ y, d.intertwiner x⟫_ℂ := (d.inner_cos₁ _ _).symm
    _ = ⟪ContinuousLinearMap.adjoint d.intertwiner (d.cos₁ y), x⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_left _ _ _).symm

/-- `sin Θ₀ J₀⋆ = J₀⋆ sin Θ₁`. -/
theorem sin₀_adjoint_intertwiner (y : F) :
    d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y) =
      ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y) := by
  refine ext_inner_right ℂ fun x => ?_
  calc ⟪d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y), x⟫_ℂ
      = ⟪ContinuousLinearMap.adjoint d.intertwiner y, d.sin₀ x⟫_ℂ := d.inner_sin₀ _ _
    _ = ⟪y, d.intertwiner (d.sin₀ x)⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪y, d.sin₁ (d.intertwiner x)⟫_ℂ := by rw [d.map_sin_apply]
    _ = ⟪d.sin₁ y, d.intertwiner x⟫_ℂ := (d.inner_sin₁ _ _).symm
    _ = ⟪ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y), x⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_left _ _ _).symm

/-- The adjoint form of the co-isometry field: `sin Θ₁ J₀ J₀⋆ = sin Θ₁`. -/
theorem sin₁_intertwiner_adjoint (y : F) :
    d.sin₁ (d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner y)) = d.sin₁ y := by
  refine ext_inner_right ℂ fun w => ?_
  calc ⟪d.sin₁ (d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner y)), w⟫_ℂ
      = ⟪d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner y), d.sin₁ w⟫_ℂ :=
        d.inner_sin₁ _ _
    _ = ⟪ContinuousLinearMap.adjoint d.intertwiner y,
          ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ w)⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪y, d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ w))⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪y, d.sin₁ w⟫_ℂ := by rw [d.coisometry_on_sin₁_apply]
    _ = ⟪d.sin₁ y, w⟫_ℂ := (d.inner_sin₁ _ _).symm

/-! ### The realizing isometry and the second subspace -/

/-- **The direct rotation, applied to the first factor.**  `W₀ x = (C₀ x, J S₀ x)`. -/
noncomputable def realizingIsometry : E →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap ∘L
    (d.cos₀.prod (d.intertwiner ∘L d.sin₀))

/-- The realizing isometry in coordinates. -/
@[simp]
theorem realizingIsometry_apply (x : E) :
    d.realizingIsometry x = WithLp.toLp 2 (d.cos₀ x, d.intertwiner (d.sin₀ x)) := rfl

/-- The adjoint of the realizing isometry: `W₀⋆ (x, y) = C₀ x + S₀ J⋆ y`. -/
noncomputable def realizingCoisometry : WithLp 2 (E × F) →L[ℂ] E :=
  d.cos₀ ∘L WithLp.fstL 2 ℂ E F +
    d.sin₀ ∘L ContinuousLinearMap.adjoint d.intertwiner ∘L WithLp.sndL 2 ℂ E F

/-- The realizing coisometry in coordinates. -/
@[simp]
theorem realizingCoisometry_apply (z : WithLp 2 (E × F)) :
    d.realizingCoisometry z =
      d.cos₀ (WithLp.ofLp z).1 +
        d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner (WithLp.ofLp z).2) := rfl

/-- `W₀⋆` is the operator written down as `realizingCoisometry`. -/
theorem adjoint_realizingIsometry :
    ContinuousLinearMap.adjoint d.realizingIsometry = d.realizingCoisometry := by
  refine ((ContinuousLinearMap.eq_adjoint_iff d.realizingCoisometry
    d.realizingIsometry).mpr ?_).symm
  intro z x
  rw [realizingCoisometry_apply, inner_add_left, realizingIsometry_apply,
    WithLp.prod_inner_apply]
  congr 1
  · exact d.inner_cos₀ _ _
  · rw [d.inner_sin₀, ContinuousLinearMap.adjoint_inner_left]

/-- `W₀⋆ W₀ = 1`: the realizing map is an isometry. -/
theorem realizingCoisometry_realizingIsometry (x : E) :
    d.realizingCoisometry (d.realizingIsometry x) = x := by
  rw [realizingIsometry_apply, realizingCoisometry_apply]
  rw [d.isometry_on_sin₀_apply, d.pythagoras₀_apply]

/-- `W₀` preserves norms. -/
theorem norm_realizingIsometry (x : E) : ‖d.realizingIsometry x‖ = ‖x‖ := by
  refine norm_eq_norm_of_inner_self_eq ?_
  rw [← ContinuousLinearMap.adjoint_inner_right, d.adjoint_realizingIsometry,
    d.realizingCoisometry_realizingIsometry]

/-- **The second subspace of the realized pair**: the image of the first under the
direct rotation, i.e. `Q H`. -/
noncomputable def targetSubspace : Submodule ℂ (WithLp 2 (E × F)) :=
  LinearMap.range (d.realizingIsometry : E →ₗ[ℂ] WithLp 2 (E × F))

/-- The realized subspace is complete, being the isometric image of a complete space. -/
noncomputable instance : CompleteSpace d.targetSubspace :=
  completeSpace_range_of_norm_map _ d.norm_realizingIsometry

/-- Membership in `Vᗮ` is the vanishing of `W₀⋆`. -/
theorem mem_targetSubspace_orthogonal_iff (z : WithLp 2 (E × F)) :
    z ∈ (d.targetSubspace)ᗮ ↔
      d.cos₀ (WithLp.ofLp z).1 +
        d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner (WithLp.ofLp z).2) = 0 := by
  rw [targetSubspace, ContinuousLinearMap.orthogonal_range, d.adjoint_realizingIsometry]
  simp [LinearMap.mem_ker]

/-- **The projection onto the realized subspace is `W₀ W₀⋆`.** -/
theorem starProjection_targetSubspace (z : WithLp 2 (E × F)) :
    d.targetSubspace.starProjection z =
      d.realizingIsometry (d.realizingCoisometry z) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ⟨d.realizingCoisometry z, rfl⟩ ?_
  rw [mem_targetSubspace_orthogonal_iff]
  have h : d.realizingCoisometry (z - d.realizingIsometry (d.realizingCoisometry z)) = 0 := by
    rw [map_sub, d.realizingCoisometry_realizingIsometry, sub_self]
  simpa using h

/-- **Davis--Kahan 1970, the Theorem 3.1 realization matrix, with the source's sign
error corrected.**

`Q = [[C₀ C₀, C₀ S₀ J⋆], [J S₀ C₀, S₁ S₁]]`.  The printed matrix carries a minus
sign in the upper-right entry against a positive lower-left entry and is
therefore not self-adjoint; the minus belongs to the second column of the direct
rotation, not to the outer product defining `Q`.  Here the entries are read off a
genuine `starProjection`, so self-adjointness is not in question. -/
theorem starProjection_targetSubspace_apply (x : E) (y : F) :
    d.targetSubspace.starProjection (WithLp.toLp 2 (x, y)) =
      WithLp.toLp 2
        (d.cos₀ (d.cos₀ x) + d.cos₀ (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)),
          d.intertwiner (d.sin₀ (d.cos₀ x)) + d.sin₁ (d.sin₁ y)) := by
  have hkey : d.intertwiner (d.sin₀ (d.sin₀
      (ContinuousLinearMap.adjoint d.intertwiner y))) = d.sin₁ (d.sin₁ y) :=
    calc d.intertwiner (d.sin₀ (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)))
        = d.sin₁ (d.intertwiner (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y))) :=
          d.map_sin_apply _
      _ = d.sin₁ (d.sin₁ (d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner y))) := by
          rw [d.map_sin_apply]
      _ = d.sin₁ (d.sin₁ y) := by rw [d.sin₁_intertwiner_adjoint]
  have hfst : d.cos₀ (d.cos₀ x + d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y))
      = d.cos₀ (d.cos₀ x) + d.cos₀ (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)) :=
    map_add _ _ _
  have hsnd : d.intertwiner (d.sin₀ (d.cos₀ x +
      d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)))
      = d.intertwiner (d.sin₀ (d.cos₀ x)) + d.sin₁ (d.sin₁ y) := by
    rw [map_add, map_add, hkey]
  rw [d.starProjection_targetSubspace, realizingCoisometry_apply]
  simp only [realizingIsometry_apply]
  rw [hfst, hsnd]

/-! ### The realized pair has the prescribed angle operators -/

/-- **The `P`-side angle of the realized pair is the prescribed one**: the
compression of `P_V` to `U` is `cos² Θ₀`. -/
theorem compress_source_eq (x : E) :
    (sourceSubspace E F).starProjection
        (d.targetSubspace.starProjection (modelInl E F x)) =
      modelInl E F (d.cos₀ (d.cos₀ x)) := by
  rw [modelInl_apply, d.starProjection_targetSubspace_apply, starProjection_sourceSubspace]
  simp

/-- **The `Pᗮ`-side angle of the realized pair is the prescribed one**: the
compression of `P_Vᗮ` to `Uᗮ` is `cos² Θ₁`. -/
theorem compress_sourceOrthogonal_eq (y : F) :
    (sourceSubspace E F)ᗮ.starProjection
        ((d.targetSubspace)ᗮ.starProjection (modelInr E F y)) =
      modelInr E F (d.cos₁ (d.cos₁ y)) := by
  have hQ : d.targetSubspace.starProjection (modelInr E F y) =
      WithLp.toLp 2 (d.cos₀ (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)),
        d.sin₁ (d.sin₁ y)) := by
    rw [modelInr_apply, d.starProjection_targetSubspace_apply]
    simp
  have hperp : (d.targetSubspace)ᗮ.starProjection (modelInr E F y) =
      modelInr E F y - d.targetSubspace.starProjection (modelInr E F y) :=
    eq_sub_of_add_eq' (d.targetSubspace.starProjection_add_starProjection_orthogonal _)
  rw [hperp, hQ, starProjection_sourceSubspace_orthogonal]
  congr 1
  have hsnd : (WithLp.ofLp (modelInr E F y -
      WithLp.toLp 2 (d.cos₀ (d.sin₀ (ContinuousLinearMap.adjoint d.intertwiner y)),
        d.sin₁ (d.sin₁ y)))).2 = y - d.sin₁ (d.sin₁ y) := by
    simp
  rw [hsnd]
  exact (eq_sub_of_add_eq (d.pythagoras₁_apply y)).symm

/-! ### The four elementary Halmos summands of the realized pair -/

/-- **`U ⊓ V` is the angle-`0` eigenspace on the `P`-side.** -/
theorem halmosCommonPart_eq :
    sourceSubspace E F ⊓ d.targetSubspace =
      Submodule.map (modelInl E F : E →ₗ[ℂ] WithLp 2 (E × F))
        (LinearMap.ker (d.sin₀ : E →ₗ[ℂ] E)) := by
  refine Submodule.ext fun z => ?_
  constructor
  · intro hz
    obtain ⟨hzU, a, rfl⟩ := Submodule.mem_inf.mp hz
    rw [mem_sourceSubspace_iff] at hzU
    simp only [ContinuousLinearMap.coe_coe, realizingIsometry_apply,
      WithLp.ofLp_toLp] at hzU
    have hsa : d.sin₀ a = 0 := by
      have hn := d.norm_intertwiner_sin₀ a
      rw [hzU, norm_zero] at hn
      exact norm_eq_zero.mp hn.symm
    refine ⟨d.cos₀ a, ?_, ?_⟩
    · simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [← d.commute₀_apply, hsa, map_zero]
    · simp only [ContinuousLinearMap.coe_coe, modelInl_apply, realizingIsometry_apply]
      rw [hzU]
  · rintro ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
    have h1 : d.sin₀ (d.cos₀ x) = 0 := by rw [← d.commute₀_apply, hx, map_zero]
    have h2 : d.cos₀ (d.cos₀ x) = x := by
      have h := d.pythagoras₀_apply x
      rw [hx, map_zero, add_zero] at h
      exact h
    refine Submodule.mem_inf.mpr ⟨?_, ⟨d.cos₀ x, ?_⟩⟩
    · rw [mem_sourceSubspace_iff]
      simp
    · simp only [realizingIsometry_apply, h1, h2, map_zero, ContinuousLinearMap.coe_coe,
        modelInl_apply]

/-- **`U ⊓ Vᗮ` is the angle-`π/2` eigenspace on the `P`-side.** -/
theorem halmosSourceDefect_eq :
    sourceSubspace E F ⊓ (d.targetSubspace)ᗮ =
      Submodule.map (modelInl E F : E →ₗ[ℂ] WithLp 2 (E × F))
        (LinearMap.ker (d.cos₀ : E →ₗ[ℂ] E)) := by
  refine Submodule.ext fun z => ?_
  constructor
  · intro hz
    obtain ⟨hzU, hzV⟩ := Submodule.mem_inf.mp hz
    rw [mem_sourceSubspace_iff] at hzU
    rw [d.mem_targetSubspace_orthogonal_iff, hzU] at hzV
    simp only [map_zero, add_zero] at hzV
    exact ⟨(WithLp.ofLp z).1, hzV, (eq_modelInl_of_snd_eq_zero hzU).symm⟩
  · rintro ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_sourceSubspace_iff]
      simp
    · rw [d.mem_targetSubspace_orthogonal_iff]
      simp [hx]

/-- **`Uᗮ ⊓ Vᗮ` is the angle-`0` eigenspace on the `Pᗮ`-side.** -/
theorem halmosExteriorPart_eq :
    (sourceSubspace E F)ᗮ ⊓ (d.targetSubspace)ᗮ =
      Submodule.map (modelInr E F : F →ₗ[ℂ] WithLp 2 (E × F))
        (LinearMap.ker (d.sin₁ : F →ₗ[ℂ] F)) := by
  refine Submodule.ext fun z => ?_
  constructor
  · intro hz
    obtain ⟨hzU, hzV⟩ := Submodule.mem_inf.mp hz
    rw [mem_sourceSubspace_orthogonal_iff] at hzU
    rw [d.mem_targetSubspace_orthogonal_iff, hzU] at hzV
    simp only [map_zero, zero_add] at hzV
    rw [d.sin₀_adjoint_intertwiner] at hzV
    have hs : d.sin₁ (WithLp.ofLp z).2 = 0 := by
      have h := d.coisometry_on_sin₁_apply (WithLp.ofLp z).2
      rw [hzV, map_zero] at h
      exact h.symm
    exact ⟨(WithLp.ofLp z).2, hs, (eq_modelInr_of_fst_eq_zero hzU).symm⟩
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_sourceSubspace_orthogonal_iff]
      simp
    · rw [d.mem_targetSubspace_orthogonal_iff]
      simp only [ContinuousLinearMap.coe_coe, modelInr_apply, WithLp.ofLp_toLp, map_zero,
        zero_add]
      rw [d.sin₀_adjoint_intertwiner, hy, map_zero]

/-- **`Uᗮ ⊓ V` is the angle-`π/2` eigenspace on the `Pᗮ`-side.** -/
theorem halmosTargetDefect_eq :
    (sourceSubspace E F)ᗮ ⊓ d.targetSubspace =
      Submodule.map (modelInr E F : F →ₗ[ℂ] WithLp 2 (E × F))
        (LinearMap.ker (d.cos₁ : F →ₗ[ℂ] F)) := by
  refine Submodule.ext fun z => ?_
  constructor
  · intro hz
    obtain ⟨hzU, a, rfl⟩ := Submodule.mem_inf.mp hz
    rw [mem_sourceSubspace_orthogonal_iff] at hzU
    simp only [ContinuousLinearMap.coe_coe, realizingIsometry_apply,
      WithLp.ofLp_toLp] at hzU
    refine ⟨d.intertwiner (d.sin₀ a), ?_, ?_⟩
    · simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [← d.map_cos_apply, d.commute₀_apply, hzU, map_zero, map_zero]
    · simp only [ContinuousLinearMap.coe_coe, modelInr_apply, realizingIsometry_apply]
      rw [hzU]
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy
    have h1 : d.cos₀ (ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y)) = 0 := by
      rw [d.cos₀_adjoint_intertwiner, d.commute₁_apply, hy, map_zero, map_zero]
    have h2 : d.intertwiner (d.sin₀
        (ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y))) = y := by
      rw [d.sin₀_adjoint_intertwiner, d.coisometry_on_sin₁_apply]
      exact d.sin₁_sin₁_of_cos₁_eq_zero hy
    refine Submodule.mem_inf.mpr ⟨?_, ⟨ContinuousLinearMap.adjoint d.intertwiner (d.sin₁ y), ?_⟩⟩
    · rw [mem_sourceSubspace_orthogonal_iff]
      simp
    · simp only [realizingIsometry_apply, h1, h2, ContinuousLinearMap.coe_coe, modelInr_apply]

/-! ### Why `0` is exceptional and `π/2` is not

The crossed defects are forced to agree; the uncrossed ones are not. -/

/-- **The intertwiner restricts to a linear isometric equivalence of the two
angle-`π/2` eigenspaces.**

This is where the paper's admissibility condition at `π/2` comes from.  The
angle-`π/2` space `ker cos₀` lies inside the range of `sin₀`, on which `J₀` is
isometric, and symmetrically on the other side — so the multiplicity at `π/2`
*must* agree.  Contrast `ker sin₀` and `ker sin₁`, which `J₀` annihilates,
respectively misses entirely. -/
noncomputable def crossedDefectEquiv :
    LinearMap.ker (d.cos₀ : E →ₗ[ℂ] E) ≃ₗᵢ[ℂ] LinearMap.ker (d.cos₁ : F →ₗ[ℂ] F) where
  toFun x := ⟨d.intertwiner (x : E), by
    have hx : d.cos₀ (x : E) = 0 := x.2
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    rw [← d.map_cos_apply, hx, map_zero]⟩
  invFun y := ⟨ContinuousLinearMap.adjoint d.intertwiner (y : F), by
    have hy : d.cos₁ (y : F) = 0 := y.2
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    rw [d.cos₀_adjoint_intertwiner, hy, map_zero]⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  left_inv x := by
    have hsq : d.sin₀ (d.sin₀ (x : E)) = (x : E) := d.sin₀_sin₀_of_cos₀_eq_zero x.2
    ext
    show ContinuousLinearMap.adjoint d.intertwiner (d.intertwiner (x : E)) = (x : E)
    conv_lhs => rw [← hsq]
    rw [d.isometry_on_sin₀_apply, hsq]
  right_inv y := by
    have hsq : d.sin₁ (d.sin₁ (y : F)) = (y : F) := d.sin₁_sin₁_of_cos₁_eq_zero y.2
    ext
    show d.intertwiner (ContinuousLinearMap.adjoint d.intertwiner (y : F)) = (y : F)
    conv_lhs => rw [← hsq]
    rw [d.coisometry_on_sin₁_apply, hsq]
  norm_map' x := by
    have hsq : d.sin₀ (d.sin₀ (x : E)) = (x : E) := d.sin₀_sin₀_of_cos₀_eq_zero x.2
    show ‖d.intertwiner (x : E)‖ = ‖(x : E)‖
    conv_lhs => rw [← hsq]
    rw [d.norm_intertwiner_sin₀, hsq]

/-- **The two crossed defects of the realized pair are isometric.**

`U ⊓ Vᗮ ≃ₗᵢ Uᗮ ⊓ V`: the paper's admissibility condition at `π/2` is not an extra
hypothesis on the datum, it is a *consequence* of the construction.  It is also
exactly the condition for a unitary of the ambient space to carry `U` onto `V`. -/
theorem nonempty_halmosSourceDefect_equiv_targetDefect :
    Nonempty (↥(sourceSubspace E F ⊓ (d.targetSubspace)ᗮ) ≃ₗᵢ[ℂ]
      ↥((sourceSubspace E F)ᗮ ⊓ d.targetSubspace)) := by
  refine ⟨(LinearIsometryEquiv.ofEq _ _ d.halmosSourceDefect_eq).trans
    (((submoduleMapIsometry (modelInl E F) norm_modelInl
        (LinearMap.ker (d.cos₀ : E →ₗ[ℂ] E))).symm.trans d.crossedDefectEquiv).trans
      ((submoduleMapIsometry (modelInr E F) norm_modelInr
        (LinearMap.ker (d.cos₁ : F →ₗ[ℂ] F))).trans
        (LinearIsometryEquiv.ofEq _ _ d.halmosTargetDefect_eq.symm)))⟩

end HalmosAngleDatum

/-! ## The multiplicity at angle `0` is genuinely unconstrained -/

section Trivial

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (F : Type v) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The datum with every angle equal to `0`: `cos Θ = 1`, `sin Θ = 0`, and no
intertwiner at all.  Its two `0`-eigenspaces are all of `E` and all of `F`, which
are arbitrary and unrelated — the machine-checked witness that the multiplicity
at angle `0` may differ between the two sides. -/
noncomputable def trivialHalmosAngleDatum : HalmosAngleDatum E F where
  cos₀ := 1
  sin₀ := 0
  cos₁ := 1
  sin₁ := 0
  intertwiner := 0
  isSelfAdjoint_cos₀ := IsSelfAdjoint.one _
  isSelfAdjoint_sin₀ := IsSelfAdjoint.zero _
  isSelfAdjoint_cos₁ := IsSelfAdjoint.one _
  isSelfAdjoint_sin₁ := IsSelfAdjoint.zero _
  commute₀ := by ext x; simp
  commute₁ := by ext y; simp
  pythagoras₀ := by ext x; simp
  pythagoras₁ := by ext y; simp
  map_cos := by ext x; simp
  map_sin := by ext x; simp
  isometry_on_sin₀ := by ext x; simp
  coisometry_on_sin₁ := by ext y; simp

/-- The all-`0` datum has vanishing `sin Θ₀`. -/
@[simp]
theorem trivialHalmosAngleDatum_sin₀ :
    (trivialHalmosAngleDatum E F).sin₀ = 0 := rfl

/-- The all-`0` datum has vanishing `sin Θ₁`. -/
@[simp]
theorem trivialHalmosAngleDatum_sin₁ :
    (trivialHalmosAngleDatum E F).sin₁ = 0 := rfl

/-- For the all-`0` datum the two subspaces coincide, so `U ⊓ V` is the whole
`E`-factor: the multiplicity at angle `0` on the `P`-side is `dim E`. -/
theorem trivial_halmosCommonPart_eq :
    sourceSubspace E F ⊓ (trivialHalmosAngleDatum E F).targetSubspace =
      sourceSubspace E F := by
  rw [(trivialHalmosAngleDatum E F).halmosCommonPart_eq, trivialHalmosAngleDatum_sin₀,
    show LinearMap.ker ((0 : E →L[ℂ] E) : E →ₗ[ℂ] E) = ⊤ by ext x; simp,
    Submodule.map_top]
  rfl

/-- Symmetrically, `Uᗮ ⊓ Vᗮ` is the whole `F`-factor: the multiplicity at angle
`0` on the `Pᗮ`-side is `dim F`.  `E` and `F` are arbitrary, so the two
multiplicities are unrelated. -/
theorem trivial_halmosExteriorPart_eq :
    (sourceSubspace E F)ᗮ ⊓ ((trivialHalmosAngleDatum E F).targetSubspace)ᗮ =
      Submodule.map (modelInr E F : F →ₗ[ℂ] WithLp 2 (E × F)) ⊤ := by
  rw [(trivialHalmosAngleDatum E F).halmosExteriorPart_eq, trivialHalmosAngleDatum_sin₁,
    show LinearMap.ker ((0 : F →L[ℂ] F) : F →ₗ[ℂ] F) = ⊤ by ext y; simp]

end Trivial

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
