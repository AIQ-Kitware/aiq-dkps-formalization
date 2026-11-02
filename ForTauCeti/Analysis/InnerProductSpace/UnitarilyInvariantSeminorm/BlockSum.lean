/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.BlockSum

/-!
# Orthogonal block sums of rectangular maps

The block sum is Mathlib's `(A.prodMap B).withLpMap 2`; its adjoint, doubled-block
singular values, Ky Fan sums and sharp seminorm comparison come from Tau Ceti.
This donor retains subspace/projector and modulus compatibility, the linear
map assembling equal blocks, and additional equality consequences.

## Provenance

Adapted from the rectangular majorization and block-sum modules in the Davis--Kahan/DKPS
formalization (Kitware, Inc.). The vector majorization descent remains in
`ForTauCeti.Analysis.Convex.Majorization`.
-/

public section


namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]

namespace UnitarilyInvariantSeminorm

variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

/-- **Doubling a map onto the diagonal of a block sum, as a linear map.**
`A ↦ A ⊕ A`.

This bundles the diagonal assembly used by the finite unitary-orbit
certificate proofs. Its action is the native product-map construction. -/
@[expose]
noncomputable def orthogonalBlockSumDiagonal
    {E₁ F₁ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] :
    (E₁ →ₗ[𝕜] F₁) →ₗ[𝕜] (WithLp 2 (E₁ × E₁) →ₗ[𝕜] WithLp 2 (F₁ × F₁)) where
  toFun A := (A.prodMap A).withLpMap 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Symmetry of square operators is preserved by orthogonal block sum. -/
theorem orthogonalBlockSum_isSymmetric
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    {A : E₁ →ₗ[𝕜] E₁} {B : E₂ →ₗ[𝕜] E₂}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    ((A.prodMap B).withLpMap 2).IsSymmetric := by
  intro x y
  simp only [LinearMap.coe_withLpMap, WithLp.map, LinearMap.prodMap_apply, WithLp.prod_inner_apply,
    WithLp.ofLp_fst, WithLp.ofLp_snd]
  rw [hA x.fst y.fst, hB x.snd y.snd]

/-- Positivity of square operators is preserved by orthogonal block sum. -/
theorem orthogonalBlockSum_isPositive
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    {A : E₁ →ₗ[𝕜] E₁} {B : E₂ →ₗ[𝕜] E₂}
    (hA : A.IsPositive) (hB : B.IsPositive) :
    ((A.prodMap B).withLpMap 2).IsPositive := by
  refine ⟨orthogonalBlockSum_isSymmetric hA.isSymmetric hB.isSymmetric, ?_⟩
  intro x
  rw [LinearMap.coe_withLpMap, WithLp.map, LinearMap.prodMap_apply, WithLp.prod_inner_apply]
  have hsum :
      0 ≤ RCLike.re ⟪A x.fst, x.fst⟫_𝕜 + RCLike.re ⟪B x.snd, x.snd⟫_𝕜 :=
    add_nonneg (hA.re_inner_nonneg_left x.fst) (hB.re_inner_nonneg_left x.snd)
  simpa only [WithLp.ofLp_fst, WithLp.ofLp_snd, map_add] using hsum

/-- The operator modulus of a block-diagonal map is block-diagonal. -/
theorem operatorAbs_orthogonalBlockSum
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂) :
    LinearMap.operatorAbs ((A.prodMap B).withLpMap 2) =
      ((A.operatorAbs).prodMap (B.operatorAbs)).withLpMap 2 := by
  symm
  refine LinearMap.IsPositive.eq_operatorAbs
    (orthogonalBlockSum_isPositive (A.isPositive_operatorAbs) (B.isPositive_operatorAbs)) ?_
  rw [← LinearMap.withLpMap_comp, LinearMap.prodMap_comp, LinearMap.operatorAbs_sq,
    LinearMap.operatorAbs_sq,
    LinearMap.adjoint_prodMap_withLpMap, ← LinearMap.withLpMap_comp, LinearMap.prodMap_comp]

/-- **The orthogonal block sum of two subspaces**, as a submodule of the Hilbert `L²` product.

This is the subspace-level partner of the native product-map sum. A direct-sum statement
is a statement about a block matrix; with it -- through
`starProjection_orthogonalBlockSumSubmodule` -- it becomes a statement about an actual pair of
subspaces of `WithLp 2 (E₁ × E₂)`. -/
noncomputable def orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    (U₁ : Submodule 𝕜 E₁) (U₂ : Submodule 𝕜 E₂) :
    Submodule 𝕜 (WithLp 2 (E₁ × E₂)) :=
  (U₁.prod U₂).comap (WithLp.linearEquiv 2 𝕜 (E₁ × E₂)).toLinearMap

/-- Membership in the block sum of two subspaces is blockwise. -/
@[simp] theorem mem_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    {U₁ : Submodule 𝕜 E₁} {U₂ : Submodule 𝕜 E₂} {x : WithLp 2 (E₁ × E₂)} :
    x ∈ orthogonalBlockSumSubmodule U₁ U₂ ↔ x.fst ∈ U₁ ∧ x.snd ∈ U₂ := Iff.rfl

/-- **The orthogonal projector onto a block sum of subspaces is the block sum of the
projectors.**

This is the bookkeeping that turns the direct-sum equality theorems -- which are stated on
native block sums of two plane angle operators into statements about the pair of
subspaces `U₁ ⊞ U₂` and `V₁ ⊞ V₂`.  Iteration to `m` blocks composes this lemma and is left to
the consumer. -/
theorem starProjection_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ : Submodule 𝕜 E₁) (U₂ : Submodule 𝕜 E₂) :
    (((orthogonalBlockSumSubmodule U₁ U₂).starProjection :
        WithLp 2 (E₁ × E₂) →L[𝕜] WithLp 2 (E₁ × E₂)) :
        WithLp 2 (E₁ × E₂) →ₗ[𝕜] WithLp 2 (E₁ × E₂)) =
      (((U₁.starProjection : E₁ →L[𝕜] E₁) : E₁ →ₗ[𝕜] E₁).prodMap
        ((U₂.starProjection : E₂ →L[𝕜] E₂) : E₂ →ₗ[𝕜] E₂)).withLpMap 2 := by
  refine LinearMap.ext fun x => ?_
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [mem_orthogonalBlockSumSubmodule]
    exact ⟨U₁.starProjection_apply_mem _, U₂.starProjection_apply_mem _⟩
  · intro y hy
    rw [mem_orthogonalBlockSumSubmodule] at hy
    rw [WithLp.prod_inner_apply]
    have h₁ := Submodule.starProjection_inner_eq_zero (K := U₁)
      (WithLp.ofLp x).1 (WithLp.ofLp y).1 hy.1
    have h₂ := Submodule.starProjection_inner_eq_zero (K := U₂)
      (WithLp.ofLp x).2 (WithLp.ofLp y).2 hy.2
    change ⟪(WithLp.ofLp x).1 - U₁.starProjection (WithLp.ofLp x).1,
        (WithLp.ofLp y).1⟫_𝕜 +
      ⟪(WithLp.ofLp x).2 - U₂.starProjection (WithLp.ofLp x).2,
        (WithLp.ofLp y).2⟫_𝕜 = 0
    rw [h₁, h₂, add_zero]

/-- **A blockwise scalar singular-value identity transfers to every unitarily invariant
seminorm on the block sum.**

If the singular values of `c • Sⱼ` are those of `Pⱼ` in each block, then `c • (S₁ ⊕ S₂)` and
`P₁ ⊕ P₂` have the same singular values, so every unitarily invariant seminorm sees the same
proportionality.  This is the mechanism by which finite orthogonal direct sums of planar
extremizers keep attaining equality at every unitarily invariant seminorm at once. -/
theorem apply_orthogonalBlockSum_eq_of_singularValues_smul_eq
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (E₁ × E₂)))
    {c : ℝ} (hc : 0 ≤ c)
    {S₁ P₁ : E₁ →ₗ[𝕜] E₁} {S₂ P₂ : E₂ →ₗ[𝕜] E₂}
    (h₁ : ((c : 𝕜) • S₁).singularValues = P₁.singularValues)
    (h₂ : ((c : 𝕜) • S₂).singularValues = P₂.singularValues) :
    c * N ((S₁.prodMap S₂).withLpMap 2) = N ((P₁.prodMap P₂).withLpMap 2) := by
  have hblock := LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq.mp
    (LinearMap.prodMap_withLpMap_mem_twoSidedUnitaryOrbit
      (LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq.mpr h₁)
      (LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq.mpr h₂))
  change ((c : 𝕜) • (S₁.prodMap S₂).withLpMap 2).singularValues =
    ((P₁.prodMap P₂).withLpMap 2).singularValues at hblock
  calc
    c * N ((S₁.prodMap S₂).withLpMap 2)
        = N ((c : 𝕜) • (S₁.prodMap S₂).withLpMap 2) := by
          rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_nonneg hc]
    _ = N ((P₁.prodMap P₂).withLpMap 2) := N.map_eq_of_singularValues_eq hblock

/-- Pointwise singular-value dominance implies norm dominance.
-/
theorem apply_le_of_singularValues_le {A B : E →ₗ[𝕜] F}
    (h : ∀ i, A.singularValues i ≤ B.singularValues i) : N A ≤ N B := by
  apply N.map_le_of_kyFanSum_le
  intro k
  simp only [LinearMap.kyFanSum_def]
  exact Finset.sum_le_sum fun i _ => h i


end UnitarilyInvariantSeminorm


end TauCeti
