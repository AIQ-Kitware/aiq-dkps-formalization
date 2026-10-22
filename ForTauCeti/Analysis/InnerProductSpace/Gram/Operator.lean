/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Gram operators of a linear map

For `A : E →ₗ[𝕜] F` the two *Gram operators* are `A⋆A` on `E` and `AA⋆` on `F`.
Both are symmetric and positive semidefinite, and their eigenvalues are the
squared singular values of `A` — which is what makes them the carrier of the
singular-subspace theory: a right singular subspace of `A` is a spectral
subspace of `A⋆A`, a left one a spectral subspace of `AA⋆`.

This module records the Gram operators and their symmetry. Perturbation
identities and operator-norm bounds are provided by Tau Ceti's accepted
`ContinuousLinearMap` API, which also works in arbitrary dimension.

## Sources

That `A⋆A` and `A A⋆` are positive with eigenvalues the squared singular values is
standard singular-value theory (Horn--Johnson, *Matrix Analysis*; distilled in
`prose/distilled_literature/HornJohnson2013_selected_matrix_analysis.tex`).
Tau Ceti's `Analysis/InnerProductSpace/Gram/Perturbation` module owns the
perturbation identities and bounds.

## Provenance

* Original module: `DavisKahan/Specialized/SingularSubspace.lean`, where this
  API sat alongside the paper-specific singular-subspace definitions.
* Extraction class: **relocation**, unchanged Gram definitions and symmetry
  facts. Migrated because they are generic: nothing here mentions a paper, a
  gap condition, or a spectral subspace. The former finite-dimensional Gram
  perturbation identities and operator-norm proofs were retired on
  2026-10-21 in favor of Tau Ceti's accepted arbitrary-dimensional API.
* The former paper-local `rightSingularSubspace` and `leftSingularSubspace`
  definitions have been retired: `YuWangSamworth2015.Core.SingularSubspace`
  consumes `LinearMap.rightSingularSubspace` and
  `LinearMap.leftSingularSubspace` from TauCeti, built on its canonical
  point-spectral subspaces. The paper-facing Hermitian-dilation block remains
  in the YWS module; this Gram operator file does not implement it.
* Spectra influence: none.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Right Gram operator `A⋆A`. -/
@[expose]
noncomputable def rightGram (A : E →ₗ[𝕜] F) : E →ₗ[𝕜] E :=
  A.adjoint ∘ₗ A

/-- The right Gram operator is symmetric and positive semidefinite. -/
theorem isSymmetric_rightGram (A : E →ₗ[𝕜] F) : (rightGram A).IsSymmetric := by
  simpa [rightGram] using A.isSymmetric_adjoint_comp_self

/-- Left Gram operator `AA⋆`. -/
@[expose]
noncomputable def leftGram (A : E →ₗ[𝕜] F) : F →ₗ[𝕜] F :=
  A ∘ₗ A.adjoint

/-- The left Gram operator is symmetric and positive semidefinite. -/
theorem isSymmetric_leftGram (A : E →ₗ[𝕜] F) : (leftGram A).IsSymmetric := by
  simpa [leftGram] using A.adjoint.isSymmetric_adjoint_comp_self

end TauCeti
