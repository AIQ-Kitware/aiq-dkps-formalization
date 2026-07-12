/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import ForMathlib.Analysis.InnerProductSpace.RectangularSingularValues

/-!
# Intrinsic singular systems for rectangular linear maps

This file scaffolds a reusable singular-vector and SVD layer stated directly for a linear map
between finite-dimensional `RCLike` inner-product spaces. It is deliberately not imported by
`ForMathlib.lean` while signatures and proofs are being audited.

The final API should be intrinsic and basis-free. Matrix factorizations should be corollaries
obtained after choosing orthonormal bases, not the foundational definitions.

## Proof donors

The closest licensed donor is
`vendor/lean/lean-stat-learning-theory/SingularSystemGram.excerpt.lean`, which proves the
right-basis equation, total left singular vectors, orthonormality on the nonzero subtype,
reconstruction, and both Gram decompositions for Euclidean matrix maps. Asterism contains a
modular full-basis completion route but is reference-only because no repository license was
visible during the survey. Full source notes are in `dev/external-lean-references.md`.
-/

namespace ForMathlib

open Module

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The right singular basis, chosen as the sorted orthonormal eigenbasis of `A†A`. -/
noncomputable def rightSingularBasis (A : E →ₗ[𝕜] F) :
    OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

/-- The total left singular-vector expression `σᵢ⁻¹ • A vᵢ`.

At a zero singular value this definition evaluates to zero because division in a field is
total. Orthonormality is asserted only on the subtype of nonzero singular values.
-/
noncomputable def leftSingularVector (A : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) : F :=
  (((A.singularValues i : ℝ) : 𝕜)⁻¹) • A (rightSingularBasis A i)

/-- The right singular basis diagonalizes `A†A`.

Proof strategy: unfold `rightSingularBasis`, apply
`LinearMap.IsSymmetric.apply_eigenvectorBasis`, and rewrite the eigenvalue with
`LinearMap.sq_singularValues_fin`.
-/
theorem adjointCompSelf_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) :
    (A.adjoint.comp A) (rightSingularBasis A i) =
      (((A.singularValues i : ℝ) ^ 2 : ℝ) : 𝕜) • rightSingularBasis A i := by
  sorry

/-- A right singular vector with zero singular value lies in the kernel of `A`.

Executable proof strategy:

1. Rewrite membership in `ker (A†A)` using
   `LinearMap.ker_adjoint_comp_self`.
2. Apply `adjointCompSelf_apply_rightSingularBasis` and the zero hypothesis.
3. Extract `A vᵢ = 0` with `LinearMap.mem_ker`.

An alternative proof expands `‖A vᵢ‖²` as the Gram quadratic form and uses
`inner_self_eq_zero`.
-/
theorem apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero
    (A : E →ₗ[𝕜] F) {i : Fin (finrank 𝕜 E)}
    (hi : A.singularValues i = 0) :
    A (rightSingularBasis A i) = 0 := by
  sorry

/-- The singular relation `A vᵢ = σᵢ uᵢ`, including the zero case.

Proof strategy:

* if `σᵢ = 0`, use `apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero`;
* otherwise unfold `leftSingularVector`, normalize `smul_smul`, cast nonzeroness from `ℝ`
  to `𝕜`, and cancel the inverse.
-/
theorem apply_rightSingularBasis_eq_smul_leftSingularVector
    (A : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) :
    A (rightSingularBasis A i) =
      ((A.singularValues i : ℝ) : 𝕜) • leftSingularVector A i := by
  sorry

/-- Left singular vectors attached to nonzero singular values are orthonormal.

Executable proof strategy:

1. Rewrite both left vectors as normalized images of right singular vectors.
2. Move one occurrence of `A` through the inner product using
   `LinearMap.adjoint_inner_left`.
3. insert `adjointCompSelf_apply_rightSingularBasis`;
4. use orthonormality of `rightSingularBasis` to reduce to an `if i = j` expression;
5. cancel singular-value factors in the diagonal case and simplify the off-diagonal case.

The vendored `lean-stat-learning-theory` excerpt contains this proof in matrix-Euclidean
notation and should be adapted rather than rediscovered.
-/
theorem orthonormal_leftSingularVector_subtype (A : E →ₗ[𝕜] F) :
    Orthonormal 𝕜
      (fun i : {j : Fin (finrank 𝕜 E) // A.singularValues j ≠ 0} =>
        leftSingularVector A i.1) := by
  sorry

/-- Every nonzero left singular vector is an eigenvector of `AA†` with eigenvalue `σᵢ²`.

Proof strategy: start from `A vᵢ = σᵢ uᵢ`, derive `A†uᵢ = σᵢvᵢ` from the right-Gram
eigen-equation, and apply `A`. This theorem is also a concrete witness for the abstract
nonzero eigenspace equivalence in `RectangularSingularValues.lean`.
-/
theorem selfCompAdjoint_apply_leftSingularVector
    (A : E →ₗ[𝕜] F) {i : Fin (finrank 𝕜 E)}
    (hi : A.singularValues i ≠ 0) :
    (A.comp A.adjoint) (leftSingularVector A i) =
      (((A.singularValues i : ℝ) ^ 2 : ℝ) : 𝕜) • leftSingularVector A i := by
  sorry

/-- Intrinsic finite singular expansion of `A x`.

Proof strategy:

1. Expand `x` in `rightSingularBasis A` with `OrthonormalBasis.sum_repr`.
2. Apply `A` through the finite sum and scalar multiplication.
3. Rewrite each image using
   `apply_rightSingularBasis_eq_smul_leftSingularVector`.
4. Rewrite basis coefficients as inner products and normalize scalar order with
   `smul_smul` and commutativity in `𝕜`.
-/
theorem singular_reconstruction (A : E →ₗ[𝕜] F) (x : E) :
    A x = ∑ i : Fin (finrank 𝕜 E),
      (inner 𝕜 (rightSingularBasis A i) x * ((A.singularValues i : ℝ) : 𝕜)) •
        leftSingularVector A i := by
  sorry

/-- Rank-one operator reconstruction of `A`.

Proof strategy: ext on `x`, rewrite each rank-one application, and invoke
`singular_reconstruction`. This is the intrinsic source for literal matrix `UΣV†`
factorizations and for both Gram decompositions.
-/
theorem eq_sum_singularValue_rankOne (A : E →ₗ[𝕜] F) :
    A = ∑ i : Fin (finrank 𝕜 E),
      ((A.singularValues i : ℝ) : 𝕜) •
        (InnerProductSpace.rankOne 𝕜
          (leftSingularVector A i) (rightSingularBasis A i)).toLinearMap := by
  sorry

/-- The nonzero left singular family extends to an orthonormal basis of the codomain.

Proof strategy:

1. Apply `orthonormal_leftSingularVector_subtype`.
2. Use Mathlib's orthonormal-family extension theorem directly.
3. Reindex the resulting basis by `Fin (finrank 𝕜 F)` using finite-dimensional cardinality.

Avoid packaging a basis indexed by a `Finset F`; that introduces equality and cardinality
obligations unrelated to the mathematics.
-/
theorem exists_orthonormalBasis_extending_leftSingularVector
    (A : E →ₗ[𝕜] F) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F,
      Set.range
          (fun i : {j : Fin (finrank 𝕜 E) // A.singularValues j ≠ 0} =>
            leftSingularVector A i.1) ⊆ Set.range b := by
  sorry

end ForMathlib
