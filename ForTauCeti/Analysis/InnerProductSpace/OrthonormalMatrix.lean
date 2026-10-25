/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Orthonormal matrices preserve singular values

The accepted matrix equivalence is conjugation by the basis representation
isometry. Consequently it preserves the full singular-value sequence,
without sorting, dropping zero values or comparing only a particular norm.
This is the coordinate transfer used by abstract spectral transport.
-/

public section

noncomputable section

namespace OrthonormalBasis

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [Fintype ι] [DecidableEq ι]

/-- Reading an operator's orthonormal matrix as a Euclidean linear map is
exactly conjugation by the basis representation isometry. -/
theorem toEuclideanLin_toMatrixOrthonormal (b : OrthonormalBasis ι 𝕜 E)
    (A : E →ₗ[𝕜] E) :
    (LinearMap.toMatrixOrthonormal b A).toEuclideanLin =
      b.repr.toLinearMap ∘ₗ A ∘ₗ b.repr.symm.toLinearMap := by
  apply (EuclideanSpace.basisFun ι 𝕜).toBasis.ext
  intro i
  ext j
  simp [Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply, Matrix.mulVec_single,
    LinearMap.toMatrix_apply, b.repr_symm_single, b.repr_apply_apply]

/-- An orthonormal matrix has exactly the original operator's singular
values, including their full zero padding. -/
theorem singularValues_toMatrixOrthonormal (b : OrthonormalBasis ι 𝕜 E)
    (A : E →ₗ[𝕜] E) :
    (LinearMap.toMatrixOrthonormal b A).toEuclideanLin.singularValues = A.singularValues := by
  rw [b.toEuclideanLin_toMatrixOrthonormal A]
  change ((b.repr : E →ₗ[𝕜] EuclideanSpace 𝕜 ι) ∘ₗ
    (A ∘ₗ (b.repr.symm : EuclideanSpace 𝕜 ι →ₗ[𝕜] E))).singularValues = _
  rw [LinearMap.singularValues_linearIsometryEquiv_comp,
    LinearMap.singularValues_comp_linearIsometryEquiv]

end OrthonormalBasis
