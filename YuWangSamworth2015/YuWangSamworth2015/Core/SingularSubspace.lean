/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import YuWangSamworth2015.Core.Statistics
public import ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
public import ForTauCeti.Analysis.InnerProductSpace.Gram.Operator
public import TauCeti.Analysis.InnerProductSpace.SingularSubspace.Perturbation
public import YuWangSamworth2015.Core.Residual

/-!
# Singular-subspace Davis--Kahan and Wedin-style corollaries

Literature map:

* `prose/core-arguments/Yu-Wang-Samworth-2014-core-arguments.tex`, Section
  "The singular-vector extension".
* `prose/core-arguments/Horn-Johnson-2013-Gram-core-arguments.tex`, Sections on
  Gram factorization and isometric freedom.
* `papers/old/formalization_comparisons/DavisKahan-formalized-vs-literature.tex`, paragraph
  "The singular-subspace extension".

The right singular subspaces are spectral subspaces of `A⋆A`, the left ones
are spectral subspaces of `AA⋆`, and the Hermitian dilation packages both at
once.  Reusable singular-subspace and Gram infrastructure lives in
`ForTauCeti`; this file records the YWS-specific application API built on it.

## Provenance

This application layer was previously staged under
`ForTauCeti/Analysis/InnerProductSpace/YuWangSamworth/SingularSubspace.lean`.
On 2026-08-17 it moved to `YuWangSamworth2015.Core` so the foundation library
contains the reusable singular-subspace primitives but not the paper-specific
YWS corollaries.

-/

public section

namespace YuWangSamworth2015
open TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The product-coordinate block map underlying the Hermitian dilation. -/
noncomputable def hermitianDilationProd (A : E →ₗ[𝕜] F) :
    (E × F) →ₗ[𝕜] (E × F) where
  toFun x := (A.adjoint x.2, A x.1)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Hermitian dilation `[[0,A⋆],[A,0]]`. -/
noncomputable def hermitianDilation (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
    hermitianDilationProd A ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

/-- The product-coordinate block map `diag(A⋆A, AA⋆)`. -/
noncomputable def gramBlockDiagonalProd (A : E →ₗ[𝕜] F) :
    (E × F) →ₗ[𝕜] (E × F) where
  toFun x := (rightGram A x.1, leftGram A x.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Block diagonal operator `diag(A⋆A, AA⋆)`. -/
noncomputable def gramBlockDiagonal (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
    gramBlockDiagonalProd A ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

/-- The Hermitian dilation `[[0, A⋆], [A, 0]]`, unfolded to its two coordinates. -/
@[simp] theorem hermitianDilation_apply (A : E →ₗ[𝕜] F)
    (x : WithLp 2 (E × F)) :
    hermitianDilation A x =
      WithLp.toLp 2 (A.adjoint (WithLp.ofLp x).2, A (WithLp.ofLp x).1) := by
  rfl

/-- The block-diagonal Gram operator `[[A⋆A, 0], [0, AA⋆]]`, unfolded. -/
@[simp] theorem gramBlockDiagonal_apply (A : E →ₗ[𝕜] F)
    (x : WithLp 2 (E × F)) :
    gramBlockDiagonal A x =
      WithLp.toLp 2 (rightGram A (WithLp.ofLp x).1, leftGram A (WithLp.ofLp x).2) := by
  rfl

/-- The dilation is symmetric.
-/
theorem isSymmetric_hermitianDilation (A : E →ₗ[𝕜] F) :
    (hermitianDilation A).IsSymmetric := fun x y => by
  simp only [hermitianDilation_apply, WithLp.prod_inner_apply]
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, add_comm]

/-- Squaring the dilation gives the two Gram operators on the diagonal.
-/
theorem hermitianDilation_sq (A : E →ₗ[𝕜] F) :
    hermitianDilation A ∘ₗ hermitianDilation A =
      gramBlockDiagonal A := by
  ext x
  apply WithLp.ofLp_injective 2
  ext <;> simp [rightGram, leftGram]

/-! ### Canonical singular-subspace perturbation interface

The YWS singular-subspace bounds are specializations of the accepted TauCeti
Gram perturbation results. The selected subspaces, interval/exterior gap, and
sine map below use TauCeti's canonical APIs directly. No separate singular
subspace representation or compatibility conversions are maintained here. -/

/-- Right singular-subspace `sin Θ` theorem, using the canonical Gram
perturbation theorem with the same spectral window on both operators. -/
theorem rightSingularSubspace_sinTheta_le
    {A Â : E →ₗ[𝕜] F} {a b δ : ℝ} (_hδ : 0 < δ)
    (hgap : Module.End.PointIntervalExteriorGap (A.adjoint ∘ₗ A)
      (A.rightSingularSubspace (Set.Icc a b)) (Â.adjoint ∘ₗ Â)
      (Â.rightSingularSubspace (Set.Icc a b))ᗮ a b δ) :
    δ * ‖(A.rightSingularSubspace (Set.Icc a b)).sinThetaMap
        (Â.rightSingularSubspace (Set.Icc a b))‖ ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  have h := LinearMap.mul_norm_sinThetaMap_rightSingularSubspace_le A Â hgap
  have hsub : (Â - A).toContinuousLinearMap =
      Â.toContinuousLinearMap - A.toContinuousLinearMap := by
    ext x
    rfl
  rw [← hsub] at h
  exact h

/-- Left singular-subspace `sin Θ` counterpart, using the accepted Gram bound. -/
theorem leftSingularSubspace_sinTheta_le
    {A Â : E →ₗ[𝕜] F} {a b δ : ℝ} (_hδ : 0 < δ)
    (hgap : Module.End.PointIntervalExteriorGap (A ∘ₗ A.adjoint)
      (A.leftSingularSubspace (Set.Icc a b)) (Â ∘ₗ Â.adjoint)
      (Â.leftSingularSubspace (Set.Icc a b))ᗮ a b δ) :
    δ * ‖(A.leftSingularSubspace (Set.Icc a b)).sinThetaMap
        (Â.leftSingularSubspace (Set.Icc a b))‖ ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  have h := LinearMap.mul_norm_sinThetaMap_leftSingularSubspace_le A Â hgap
  have hsub : (Â - A).toContinuousLinearMap =
      Â.toContinuousLinearMap - A.toContinuousLinearMap := by
    ext x
    rfl
  rw [← hsub] at h
  exact h

/-- Hermitian-dilation form controlling left and right singular subspaces in a
single Davis--Kahan application.

Signature audit: the previous constant-one conclusion was too strong for an
arbitrary `HybridGap`; constant one requires a stronger gap predicate.
-/
theorem singularSubspace_dilation_sinTheta_le
    {A Â : E →ₗ[𝕜] F} {Ω : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : HybridGap (hermitianDilation A) (hermitianDilation Â)
      (Module.End.pointSpectralSubspace (hermitianDilation A) Ω)
      (Module.End.pointSpectralSubspace (hermitianDilation Â) Ω) δ) :
    δ * ‖(sinThetaMap (Module.End.pointSpectralSubspace (hermitianDilation A) Ω)
        (Module.End.pointSpectralSubspace (hermitianDilation Â) Ω)).toContinuousLinearMap‖ ≤
      (Real.pi / 2) *
        ‖(hermitianDilation Â - hermitianDilation A).toContinuousLinearMap‖ := by
  have h := sinTheta_perturbation_le_of_spectralDistance
    (UnitarilyInvariantSeminorm.opNorm (𝕜 := 𝕜) (E := (WithLp 2 (E × F))) (F := (WithLp 2 (E × F))))
    (isSymmetric_hermitianDilation A) (isSymmetric_hermitianDilation Â)
    (isInvariant_pointSpectralSubspace (hermitianDilation A) Ω)
    (isInvariant_pointSpectralSubspace (hermitianDilation Â) Ω) hδ hgap
  simp only [UnitarilyInvariantSeminorm.opNorm_apply] at h
  exact h

/-- Equal-dimensional right singular subspaces admit an isometric
identification; the aligned-frame theorem in `Statistics.lean` chooses the
identification minimizing basis discrepancy. -/
theorem nonempty_rightSingularSubspace_isometry
    {A Â : E →ₗ[𝕜] F} {Ω : Set ℝ}
    (hrank : finrank 𝕜 (A.rightSingularSubspace Ω) =
      finrank 𝕜 (Â.rightSingularSubspace Ω)) :
    Nonempty (Â.rightSingularSubspace Ω ≃ₗᵢ[𝕜]
      A.rightSingularSubspace Ω) :=
  ⟨(stdOrthonormalBasis 𝕜 (Â.rightSingularSubspace Ω)).equiv
    (stdOrthonormalBasis 𝕜 (A.rightSingularSubspace Ω)) (finCongr hrank.symm)⟩


open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ## Yu--Wang--Samworth singular-vector extension -/

/-- **Yu–Wang–Samworth singular-vector extension (operator-norm branch).** The
right singular vectors of `A, Â : E →ₗ[𝕜] F` are the eigenvectors of the Gram
operators `A⋆A, Â⋆Â`, whose eigenvalues are the squared singular values.
Applying the symmetric YWS bound (`sq_gap_mul_sum_cross_le_of_population_gap_opNorm`)
to the Gram operators — with the perturbation controlled by
`norm_gram_sub_gram_apply_le` — gives, for a squared-singular-value population gap
`Γ` separating the block `s`, `Γ² · overlap ≤ 4 · d · ((a + â) ε)²`. -/
theorem sq_gap_mul_sum_cross_singularVectors_le
    {A Â : E →ₗ[𝕜] F} {Γ a â ε : ℝ} (hΓ : 0 ≤ Γ) (hâ : 0 ≤ â) (hε : 0 ≤ ε)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖)
    {n : ℕ} (hn : finrank 𝕜 E = n) (s : Finset (Fin n))
    (hgap : ∀ j ∈ s, ∀ k ∉ s,
      Γ ≤ |A.isSymmetric_adjoint_comp_self.eigenvalues hn j
            - A.isSymmetric_adjoint_comp_self.eigenvalues hn k|) :
    Γ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪A.isSymmetric_adjoint_comp_self.eigenvectorBasis hn k,
            Â.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j⟫_𝕜‖ ^ 2
      ≤ 4 * s.card * ((a + â) * ε) ^ 2 :=
  sq_gap_mul_sum_cross_le_of_population_gap_opNorm
    A.isSymmetric_adjoint_comp_self Â.isSymmetric_adjoint_comp_self hn s hΓ hgap
    (fun x => norm_gram_sub_gram_apply_le hâ hε hA hÂ hE x)

end YuWangSamworth2015
