/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import ForTauCeti.Analysis.InnerProductSpace.Residual.TrialMap
public import ForTauCeti.Analysis.InnerProductSpace.FrameFactorization

/-!
# Principal-angle embeddings for trial subspaces

Coordinate-space sine and cosine embeddings, their projected residual identity,
and the singular-value dictionary relating them to directed principal angles.

## Sources

Principal angles between subspaces and their use in a residual bound follow
Davis--Kahan; see
`prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex` and
`prose/distilled_literature/DavisKahan1970_part_III.tex`.  The trial-subspace
embedding shape is this library's.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Residual/AngleEmbedding.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

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
/-- Sine map from approximate coordinates into the orthogonal complement of
an exact subspace. -/
@[expose]
noncomputable def sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- On an *isometric* trial map the complementary block is the sine-Θ
embedding, definitionally.  The two names exist because the block is defined
for an arbitrary linear trial map and the embedding only for an isometric one. -/
@[simp] theorem complementaryTrialBlock_toLinearMap (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    complementaryTrialBlock U X.toLinearMap = sinThetaEmbedding U X :=
  rfl

/-- Cosine map from approximate coordinates into an exact subspace. -/
noncomputable def cosThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  U.starProjection.toLinearMap ∘ₗ X.toLinearMap

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The cosine embedding is pointwise contractive. -/
theorem cosThetaEmbedding_apply_norm_le (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) (x : F) :
    ‖cosThetaEmbedding U X x‖ ≤ ‖x‖ := by
  -- names the projection application so the norm bound applies to it directly.
  change ‖U.starProjection (X x)‖ ≤ ‖x‖
  calc
    ‖U.starProjection (X x)‖ ≤ ‖X x‖ := U.norm_starProjection_apply_le _
    _ = ‖x‖ := X.norm_map x

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The sine embedding is pointwise contractive. -/
theorem sinThetaEmbedding_apply_norm_le (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) (x : F) :
    ‖sinThetaEmbedding U X x‖ ≤ ‖x‖ := by
  -- names the projection application so the norm bound applies to it directly.
  change ‖Uᗮ.starProjection (X x)‖ ≤ ‖x‖
  calc
    ‖Uᗮ.starProjection (X x)‖ ≤ ‖X x‖ := Uᗮ.norm_starProjection_apply_le _
    _ = ‖x‖ := X.norm_map x

omit [FiniteDimensional 𝕜 E] in
/-- The operator norm of the cosine embedding is at most one. -/
theorem cosThetaEmbedding_opNorm_le_one (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    ‖(cosThetaEmbedding U X).toContinuousLinearMap‖ ≤ 1 := by
  refine (cosThetaEmbedding U X).toContinuousLinearMap.opNorm_le_bound
    zero_le_one fun x => ?_
  simpa using cosThetaEmbedding_apply_norm_le U X x

omit [FiniteDimensional 𝕜 E] in
/-- The operator norm of the sine embedding is at most one. -/
theorem sinThetaEmbedding_opNorm_le_one (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    ‖(sinThetaEmbedding U X).toContinuousLinearMap‖ ≤ 1 := by
  refine (sinThetaEmbedding U X).toContinuousLinearMap.opNorm_le_bound
    zero_le_one fun x => ?_
  simpa using sinThetaEmbedding_apply_norm_le U X x

/-- Source-side cosine Gram block `C⋆C`, where `C = P_U X`. -/
noncomputable def cosThetaGram (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] F :=
  LinearMap.adjoint (cosThetaEmbedding U X) ∘ₗ cosThetaEmbedding U X

/-- Source-side sine Gram block `S⋆S`, where `S = P_{Uᗮ} X`. -/
@[expose]
noncomputable def sinThetaGram (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] F :=
  LinearMap.adjoint (sinThetaEmbedding U X) ∘ₗ sinThetaEmbedding U X

/-- The positive source-coordinate cosine `|C| = (C⋆C)^(1/2)`.

Unlike the rectangular block `C : F → E`, this is an endomorphism of the
trial-coordinate space.  Its eigenvalues are the principal-angle cosines, so
it is the denominator used by the coordinate tangent map. -/
@[expose]
noncomputable def cosThetaMagnitude (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] F :=
  trialGramSqrt (cosThetaEmbedding U X)

/-- The positive source cosine is pointwise contractive. -/
theorem cosThetaMagnitude_apply_norm_le (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) (x : F) :
    ‖cosThetaMagnitude U X x‖ ≤ ‖x‖ := by
  rw [cosThetaMagnitude, norm_trialGramSqrt_apply]
  exact cosThetaEmbedding_apply_norm_le U X x

/-- The operator norm of the positive source cosine is at most one. -/
theorem cosThetaMagnitude_opNorm_le_one (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    ‖(cosThetaMagnitude U X).toContinuousLinearMap‖ ≤ 1 := by
  refine (cosThetaMagnitude U X).toContinuousLinearMap.opNorm_le_bound
    zero_le_one fun x => ?_
  simpa using cosThetaMagnitude_apply_norm_le U X x

/-- The cosine and sine Gram blocks partition the identity on trial
coordinates: `C⋆C + S⋆S = I`. -/
theorem cosThetaGram_add_sinThetaGram_eq_id (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    cosThetaGram U X + sinThetaGram U X = LinearMap.id := by
  ext x
  apply ext_inner_right 𝕜
  intro y
  simp only [LinearMap.add_apply, cosThetaGram, sinThetaGram,
    LinearMap.comp_apply, LinearMap.id_apply, inner_add_left]
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  -- states the goal with the definition unfolded, in the shape the next step needs.
  change
    ⟪U.starProjection (X x), U.starProjection (X y)⟫_𝕜 +
        ⟪Uᗮ.starProjection (X x), Uᗮ.starProjection (X y)⟫_𝕜 =
      ⟪x, y⟫_𝕜
  have hPU : U.starProjection (U.starProjection (X y)) = U.starProjection (X y) :=
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem _)
  have hPUperp :
      Uᗮ.starProjection (Uᗮ.starProjection (X y)) = Uᗮ.starProjection (X y) :=
    Submodule.starProjection_eq_self_iff.mpr (Uᗮ.starProjection_apply_mem _)
  simp only [U.inner_starProjection_left_eq_right,
    Uᗮ.inner_starProjection_left_eq_right, hPU, hPUperp,
    ← inner_add_right, U.starProjection_add_starProjection_orthogonal,
    X.inner_map_map]

/-- The positive cosine squares to the cosine Gram block. -/
theorem cosThetaMagnitude_sq (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    cosThetaMagnitude U X ∘ₗ cosThetaMagnitude U X = cosThetaGram U X := by
  simp [cosThetaMagnitude, cosThetaGram, trialGramSqrt]

/-- The positive coordinate cosine has exactly the kernel of the rectangular
cosine block. -/
theorem ker_cosThetaMagnitude (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    LinearMap.ker (cosThetaMagnitude U X) =
      LinearMap.ker (cosThetaEmbedding U X) := by
  simpa [cosThetaMagnitude] using ker_trialGramSqrt (cosThetaEmbedding U X)

/-- Transversality of the rectangular cosine block transfers to its positive
source-coordinate factor. -/
theorem cosThetaMagnitude_injective
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (hC : Function.Injective (cosThetaEmbedding U X)) :
    Function.Injective (cosThetaMagnitude U X) := by
  simpa [cosThetaMagnitude] using
    trialGramSqrt_injective (X := cosThetaEmbedding U X) hC

/-- Passing from the rectangular cosine block to its positive source factor
preserves the full zero-padded singular-value sequence. -/
theorem singularValues_cosThetaMagnitude_eq_embedding
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) :
    (cosThetaMagnitude U X).singularValues =
      (cosThetaEmbedding U X).singularValues := by
  apply singularValues_eq_of_gram_eq
  have hpos : (cosThetaMagnitude U X).IsPositive := by
    simpa [cosThetaMagnitude, trialGramSqrt] using
      (cosThetaEmbedding U X).isPositive_adjoint_comp_self.sqrt_isPositive
  rw [hpos.adjoint_eq, cosThetaMagnitude_sq U X]
  rfl

/-- Source-side double-angle cosine
`cos(2Θ) = C⋆C - S⋆S` on trial coordinates. -/
noncomputable def cosTwoThetaSourceOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] F :=
  cosThetaGram U X - sinThetaGram U X

/-- The source-side double-angle cosine is symmetric. -/
theorem cosTwoThetaSourceOperator_isSymmetric (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    (cosTwoThetaSourceOperator U X).IsSymmetric :=
  (cosThetaEmbedding U X).isSymmetric_adjoint_comp_self.sub
    (sinThetaEmbedding U X).isSymmetric_adjoint_comp_self

/-- Equivalent affine form `cos(2Θ) = 2 C⋆C - I`. -/
theorem cosTwoThetaSourceOperator_eq_two_smul_sub_id
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) :
    cosTwoThetaSourceOperator U X =
      (2 : 𝕜) • cosThetaGram U X - LinearMap.id := by
  have hsum := cosThetaGram_add_sinThetaGram_eq_id U X
  calc
    cosTwoThetaSourceOperator U X =
        cosThetaGram U X - sinThetaGram U X := rfl
    _ = (2 : 𝕜) • cosThetaGram U X -
        (cosThetaGram U X + sinThetaGram U X) := by module
    _ = (2 : 𝕜) • cosThetaGram U X - LinearMap.id := by rw [hsum]

/-- Trial-coordinate double-angle cosine embedded isometrically into `E`.

The source operator `C⋆C - S⋆S` has eigenvalues `cos (2 θᵢ)`.  Left
composition by `X` preserves its singular values and keeps the historical
rectangular signature `F → E`. -/
noncomputable def cosTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  X.toLinearMap ∘ₗ cosTwoThetaSourceOperator U X

/-- The isometric codomain embedding does not change the kernel of the
source-side double-angle cosine. -/
theorem ker_cosTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    LinearMap.ker (cosTwoThetaEmbedding U X) =
      LinearMap.ker (cosTwoThetaSourceOperator U X) := by
  apply le_antisymm
  · intro y hy
    -- restates the hypothesis with the definition unfolded, which is the form the
    -- following step matches against.
    change X (cosTwoThetaSourceOperator U X y) = 0 at hy
    -- unfolds the named residual/compression so the following rewrite sees its
    -- definition; there is no `_apply` lemma for it to route through.
    change cosTwoThetaSourceOperator U X y = 0
    exact X.injective (hy.trans (map_zero X).symm)
  · intro y hy
    -- restates the hypothesis with the definition unfolded, which is the form the
    -- following step matches against.
    change cosTwoThetaSourceOperator U X y = 0 at hy
    -- unfolds the named residual/compression so the following rewrite sees its
    -- definition; there is no `_apply` lemma for it to route through.
    change X (cosTwoThetaSourceOperator U X y) = 0
    rw [hy, map_zero]

/-- The historical rectangular double-angle cosine has exactly the
singular values of its source-coordinate operator. -/
theorem singularValues_cosTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    (cosTwoThetaEmbedding U X).singularValues =
      (cosTwoThetaSourceOperator U X).singularValues := by
  simp [cosTwoThetaEmbedding]

/-- Injectivity of the rectangular and source-coordinate double-angle cosine
blocks is equivalent. -/
theorem cosTwoThetaEmbedding_injective_iff (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    Function.Injective (cosTwoThetaEmbedding U X) ↔
      Function.Injective (cosTwoThetaSourceOperator U X) := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot,
    ker_cosTwoThetaEmbedding U X]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- **The projected-residual (cross-block) Sylvester identity for an isometric
trial map.**  This is the normalized specialization of
`sylvester_complementaryTrialBlock_eq_projectedGeneralResidual`. -/
theorem sylvester_sinThetaEmbedding_eq_projectedResidual
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A))
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    A ∘ₗ sinThetaEmbedding U X - sinThetaEmbedding U X ∘ₗ M =
      Uᗮ.starProjection.toLinearMap ∘ₗ residual A X M := by
  simpa only [complementaryTrialBlock_toLinearMap, generalResidual_toLinearMap] using
    sylvester_complementaryTrialBlock_eq_projectedGeneralResidual
      hA hU X.toLinearMap M

/-- The orthogonal projection onto the range of an isometric embedding is
`X X⋆`. -/
theorem projection_approximateSubspace_eq_comp_adjoint (X : F →ₗᵢ[𝕜] E) :
    ((approximateSubspace X)).starProjection.toLinearMap =
      X.toLinearMap ∘ₗ X.toLinearMap.adjoint := by
  ext y
  -- states the goal with the definition unfolded, in the shape the next step needs.
  change (approximateSubspace X).starProjection y =
    X.toLinearMap (X.toLinearMap.adjoint y)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change X.toLinearMap (X.toLinearMap.adjoint y) ∈
      LinearMap.range X.toLinearMap
    exact ⟨X.toLinearMap.adjoint y, rfl⟩
  · intro w hw
    -- restates the hypothesis with the definition unfolded, which is the form the
    -- following step matches against.
    change w ∈ LinearMap.range X.toLinearMap at hw
    rcases hw with ⟨z, rfl⟩
    rw [inner_sub_left]
    apply sub_eq_zero.mpr
    -- states the goal as the inner-product identity the isometry/adjoint lemma
    -- expects, rather than through the bundled map.
    change ⟪y, X z⟫_𝕜 =
      ⟪X (X.toLinearMap.adjoint y), X z⟫_𝕜
    exact (LinearMap.adjoint_inner_left X.toLinearMap z y).symm |>.trans
      (X.inner_map_map (X.toLinearMap.adjoint y) z).symm

/-- The singular values of `sinThetaEmbedding U X = P_{Uᗮ}X` are the
principal sines directed from `range X` toward `U`.

The proof identifies the projection onto `range X` with `X X⋆`, precomposes by
`X⋆`, and uses coisometry padding to show that the ambient cross projection has
exactly the same singular-value sequence as the rectangular embedding map.
-/
theorem singularValues_sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    (sinThetaEmbedding U X).singularValues =
      Submodule.principalSines (approximateSubspace X) U := by
  have hmap :
      sinThetaEmbedding U X ∘ₗ X.toLinearMap.adjoint =
        ((approximateSubspace X).sinThetaMap U).toLinearMap := by
    rw [sinThetaEmbedding, Submodule.sinThetaMap_def]
    change (Uᗮ.starProjection.toLinearMap ∘ₗ X.toLinearMap) ∘ₗ X.toLinearMap.adjoint =
      Uᗮ.starProjection.toLinearMap ∘ₗ ((approximateSubspace X)).starProjection.toLinearMap
    rw [projection_approximateSubspace_eq_comp_adjoint X]
    simp only [LinearMap.comp_assoc]
  calc
    (sinThetaEmbedding U X).singularValues =
        (sinThetaEmbedding U X ∘ₗ X.toLinearMap.adjoint).singularValues :=
      (LinearMap.singularValues_comp_adjoint_linearIsometry (sinThetaEmbedding U X) X).symm
    _ = (((approximateSubspace X).sinThetaMap U).toLinearMap).singularValues := by rw [hmap]
    _ = Submodule.principalSines (approximateSubspace X) U := by
      rw [Submodule.principalSines_def]

/-- The singular values of `cosThetaEmbedding U X = P_U X` are the
principal cosines directed from `range X` toward `U`. -/
theorem singularValues_cosThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    (cosThetaEmbedding U X).singularValues =
      Submodule.principalCosines (approximateSubspace X) U := by
  have hmap :
      cosThetaEmbedding U X ∘ₗ X.toLinearMap.adjoint =
        ((approximateSubspace X).cosThetaMap U).toLinearMap := by
    rw [cosThetaEmbedding, Submodule.cosThetaMap_def]
    change (U.starProjection.toLinearMap ∘ₗ X.toLinearMap) ∘ₗ X.toLinearMap.adjoint =
      U.starProjection.toLinearMap ∘ₗ ((approximateSubspace X)).starProjection.toLinearMap
    rw [projection_approximateSubspace_eq_comp_adjoint X]
    simp only [LinearMap.comp_assoc]
  calc
    (cosThetaEmbedding U X).singularValues =
        (cosThetaEmbedding U X ∘ₗ X.toLinearMap.adjoint).singularValues :=
      (LinearMap.singularValues_comp_adjoint_linearIsometry (cosThetaEmbedding U X) X).symm
    _ = (((approximateSubspace X).cosThetaMap U).toLinearMap).singularValues := by rw [hmap]
    _ = Submodule.principalCosines (approximateSubspace X) U := by
      rw [Submodule.principalCosines_def]

/-- The positive coordinate cosine has the principal-angle cosine
singular-value sequence. -/
theorem singularValues_cosThetaMagnitude (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    (cosThetaMagnitude U X).singularValues =
      Submodule.principalCosines (approximateSubspace X) U := by
  rw [singularValues_cosThetaMagnitude_eq_embedding,
    singularValues_cosThetaEmbedding]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The tangent map is finite exactly when the represented subspace is
transverse to `U`.

The native disjointness condition is projection injectivity on `range X`,
exactly the kernel condition on the right.
-/
theorem tanThetaEmbedding_defined_iff (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    Disjoint (approximateSubspace X) Uᗮ ↔
      LinearMap.ker (cosThetaEmbedding U X) = ⊥ := by
  rw [← Submodule.injOn_starProjection_iff_disjoint (approximateSubspace X) U,
    LinearMap.ker_eq_bot]
  constructor
  · intro h x y hxy
    apply X.injective
    apply h ⟨x, rfl⟩ ⟨y, rfl⟩
    exact hxy
  · intro h x hx y hy hxy
    rcases hx with ⟨u, rfl⟩
    rcases hy with ⟨v, rfl⟩
    have huv : u = v := h hxy
    exact congrArg X huv


end TauCeti
