/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Rectangular singular values and adjoint-product spectra

This file scaffolds the Mathlib-facing rectangular spectral layer needed by the finite-frame
and Perfect Quench developments. It is deliberately not imported by `ForMathlib.lean` while
its signatures and proofs are under development.

Mathlib already defines `LinearMap.singularValues` for a rectangular map as a zero-padded,
`Nat`-indexed sequence derived from `A†A`. The canonical missing bridge is therefore not a new
singular-value definition. It is the equivalence of the nonzero eigenspaces of `A†A` and
`AA†`, followed by equality of the two multiplicity-counted positive spectra and invariance
of singular values under adjoint.

## Contribution boundary

The intended upstream contribution is independent of DKPS:

1. a linear equivalence between corresponding nonzero eigenspaces of `A†A` and `AA†`;
2. equality of their eigenspace dimensions and nonzero eigenvalue multiplicities;
3. zero-padded equality `A†.singularValues = A.singularValues`;
4. sorted left-Gram eigenvalues expressed as squared singular values.

## Proof sources

Licensed proof snapshots and exact provenance are recorded under `vendor/lean/`. In
particular, `lean-stat-learning-theory/SingularSystemGram.excerpt.lean` constructs the left
singular vectors and both Gram decompositions. Reference-only approaches using
`spectrum.nonzero_mul_comm`, characteristic polynomials, or full SVDs are catalogued in
`dev/external-lean-references.md`.
-/

namespace ForMathlib

open Module

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The nonzero `μ`-eigenspaces of `A†A` and `AA†` are linearly equivalent.

Mathematical map:

* forward: `x ↦ A x`;
* inverse: `y ↦ μ⁻¹ • A† y`.

Executable proof strategy:

1. For `x` in the `μ`-eigenspace of `A†A`, show `A x` lies in the `μ`-eigenspace of
   `AA†` by applying `A` to `(A†A)x = μx` and reassociating composition.
2. For `y` in the `μ`-eigenspace of `AA†`, show `μ⁻¹ • A†y` lies in the other eigenspace
   by applying `A†` to `(AA†)y = μy`.
3. Prove the two inverse laws using `hμ : μ ≠ 0`, the corresponding eigen-equation, and
   `inv_smul_smul₀`/`smul_smul` normalization.
4. Construct a `LinearEquiv` between the two eigenspace subtypes. No spectral theorem,
   finite-dimensionality, or chosen basis is mathematically required for this lemma; if the
   current eigenspace API forces finite-dimensional assumptions, audit and remove them in the
   upstream version.

This is the preferred root theorem. It preserves geometric multiplicity directly and avoids
reasoning first with unordered spectrum sets.
-/
noncomputable def nonzeroEigenspaceEquivAdjointCompSelfSelfCompAdjoint
    (A : E →ₗ[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0) :
    Module.End.eigenspace (A.adjoint.comp A) μ ≃ₗ[𝕜]
      Module.End.eigenspace (A.comp A.adjoint) μ := by
  sorry

/-- Corresponding nonzero eigenspaces of `A†A` and `AA†` have equal dimension.

Proof strategy: take `LinearEquiv.finrank_eq` of
`nonzeroEigenspaceEquivAdjointCompSelfSelfCompAdjoint`. This should be a one-line theorem once
the equivalence above has the final namespace and argument order.
-/
theorem finrank_eigenspace_adjointCompSelf_eq_selfCompAdjoint
    (A : E →ₗ[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0) :
    finrank 𝕜 (Module.End.eigenspace (A.adjoint.comp A) μ) =
      finrank 𝕜 (Module.End.eigenspace (A.comp A.adjoint) μ) := by
  sorry

/-- A nonzero scalar is an eigenvalue of `A†A` exactly when it is an eigenvalue of `AA†`.

Proof strategy: rewrite `Module.End.HasEigenvalue` as nontriviality of the eigenspace and
transport a nonzero vector through the equivalence above. The theorem
`spectrum.nonzero_mul_comm` gives a shorter set-level proof and is a useful cross-check, but
the eigenspace route should remain primary because downstream multiplicity results need the
actual equivalence.
-/
theorem hasEigenvalue_adjointCompSelf_iff_selfCompAdjoint
    (A : E →ₗ[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (A.adjoint.comp A) μ ↔
      Module.End.HasEigenvalue (A.comp A.adjoint) μ := by
  sorry

/-- Every positive squared singular value of `A` occurs in the left Gram operator `AA†`.

Executable proof strategy:

1. Use `LinearMap.hasEigenvalue_adjoint_comp_self_sq_singularValues` to obtain the
   corresponding eigenvalue of `A†A`.
2. Show the scalar cast of `A.singularValues i ^ 2` is nonzero from
   `singularValues_pos_iff_lt_finrank_range` and `hi`.
3. Apply `hasEigenvalue_adjointCompSelf_iff_selfCompAdjoint`.
4. Keep the coercion from `ℝ` to `𝕜` explicit; this is the main elaboration seam over a
   general `RCLike` field.
-/
theorem hasEigenvalue_selfCompAdjoint_sq_singularValues
    (A : E →ₗ[𝕜] F) {i : ℕ} (hi : i < finrank 𝕜 A.range) :
    Module.End.HasEigenvalue (A.comp A.adjoint) ((A.singularValues i ^ 2 : ℝ) : 𝕜) := by
  sorry

/-- Singular values are invariant under adjoint for rectangular finite-dimensional maps.

Mathlib's `Nat`-indexed sequence is zero-padded, so no equality of ambient dimensions is
needed.

Executable proof strategy:

1. The support of both singular-value sequences is `Finset.range (finrank 𝕜 A.range)`;
   rewrite the adjoint support using `finrank_range_adjoint`.
2. For an index inside the common support, square both nonnegative singular values.
3. Rewrite each square as a sorted eigenvalue of the appropriate Gram operator.
4. Use the nonzero multiplicity theorem to identify the positive sorted eigenvalue lists.
   A helper converting equal multiplicity functions into equal antitone finite sequences may
   deserve its own general lemma.
5. Outside the support, use `singularValues_eq_zero_iff_le_finrank_range` on both sides.

Do not prove this by embedding the rectangular map into an arbitrary square block operator;
that obscures the zero-padding convention and creates unnecessary basis choices.
-/
theorem singularValues_adjoint_rectangular (A : E →ₗ[𝕜] F) :
    A.adjoint.singularValues = A.singularValues := by
  sorry

/-- Pointwise adjoint invariance, convenient for rewriting a fixed index. -/
theorem singularValues_adjoint_apply (A : E →ₗ[𝕜] F) (i : ℕ) :
    A.adjoint.singularValues i = A.singularValues i := by
  simpa using congrFun (singularValues_adjoint_rectangular A) i

/-- The eigenvalues of the left Gram operator are the squared singular values, with zeros
added after the rank.

The exact public statement may ultimately use a zero-padded eigenvalue sequence rather than
`Fin`-indexed `IsSymmetric.eigenvalues`. The theorem is scaffolded in the existing API so the
Perfect Quench adapter can consume it before a broader eigenvalue-sequence abstraction is
decided.

Proof strategy:

* inside the rank, identify the eigenvalue through the nonzero eigenspace equivalence and the
  antitone ordering;
* from the rank to `finrank 𝕜 F`, show the left-Gram eigenvalue is zero using positivity,
  rank-nullity, and exhaustion of the positive eigenspaces;
* cross-check the zero multiplicity with `finrank_range_adjoint`.
-/
theorem eigenvalues_selfCompAdjoint_eq_sq_singularValues_zeroPadded
    (A : E →ₗ[𝕜] F) {m : ℕ} (hm : finrank 𝕜 F = m) (i : Fin m) :
    A.isPositive_self_comp_adjoint.isSymmetric.eigenvalues hm i =
      A.singularValues i ^ 2 := by
  sorry

end ForMathlib
