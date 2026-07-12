/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import ForMathlib.Analysis.InnerProductSpace.RectangularSingularValues

/-!
# Finite frames and Gram operators

This file scaffolds a finite analysis/synthesis API suitable for a standalone Mathlib
contribution. It is deliberately not imported by `ForMathlib.lean` while the definitions and
proofs are being audited.

The abstraction is a finite family `v : ι → E`. Application-specific covariance matrices,
sample normalizations, and DKPS events should be thin adapters over this layer.

## Design principle

Define the analysis map first and define synthesis as its adjoint unless a direct finite-sum
definition proves substantially easier to simplify. Whichever direction is chosen, establish
`analysis† = synthesis` immediately; frame and Gram identities should then be consequences of
adjoint composition rather than repeated coordinate calculations.

## Proof donor and DK relevance

`vendor/lean/drifting-identifiability/FiniteFrameBound.excerpt.lean` proves that
finite linear independence yields a positive lower stability constant through
an antilipschitz estimate.  Its application-specific coordinates should be
re-authored as the intrinsic frame API below.  The resulting lower frame bound
is also a coercivity certificate for generalized and trial-subspace
Davis--Kahan theorems, not only a Perfect Quench prerequisite.
-/

namespace ForMathlib

open Module
open scoped BigOperators

variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [Fintype ι] [DecidableEq ι]

/-- Analysis map of a finite family, with coordinate `i` equal to `⟪v i, x⟫`.

The inner-product argument order is chosen so this map is `𝕜`-linear under Mathlib's
convention. Verify the convention over both `ℝ` and `ℂ` before upstreaming.

Proof strategy: use the `EuclideanSpace`/`PiLp` linear-map constructor and prove linearity
coordinatewise with `inner_add_right` and `inner_smul_right`.
-/
noncomputable def finiteAnalysis (v : ι → E) : E →ₗ[𝕜] EuclideanSpace 𝕜 ι := by
  sorry

/-- Synthesis map `c ↦ ∑ i, c i • v i`.

Proof strategy: construct the linear map directly from the finite sum. Keep a simp theorem
for its application; it is the main bridge to existing `Matrix.gram` and finite-family code.
-/
noncomputable def finiteSynthesis (v : ι → E) : EuclideanSpace 𝕜 ι →ₗ[𝕜] E := by
  sorry

/-- Frame operator `A†A` on the ambient space. -/
noncomputable def finiteFrameOperator (v : ι → E) : E →ₗ[𝕜] E :=
  (finiteSynthesis v).comp (finiteAnalysis v)

/-- Gram operator `AA†` on coefficient space. -/
noncomputable def finiteGramOperator (v : ι → E) :
    EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι :=
  (finiteAnalysis v).comp (finiteSynthesis v)

/-- Explicit lower and upper frame bounds for a finite family. -/
def HasFiniteFrameBounds (v : ι → E) (a b : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ b ∧ ∀ x : E,
    a * ‖x‖ ^ 2 ≤ ∑ i, ‖inner 𝕜 (v i) x‖ ^ 2 ∧
      ∑ i, ‖inner 𝕜 (v i) x‖ ^ 2 ≤ b * ‖x‖ ^ 2

/-- Analysis and synthesis are adjoints.

Executable proof strategy:

1. Extensionality on `c : EuclideanSpace 𝕜 ι` and `x : E` through the adjoint
   characterization.
2. Expand the Euclidean inner product as a finite sum.
3. Expand `finiteSynthesis`, distribute the inner product over the sum, and match terms.
4. Audit conjugation carefully: the coordinate convention in `finiteAnalysis` must make the
   two sides definitionally or simplifiably equal over an arbitrary `RCLike` field.
-/
theorem finiteAnalysis_adjoint_eq_synthesis (v : ι → E) :
    (finiteAnalysis v).adjoint = finiteSynthesis v := by
  sorry

/-- The frame operator is the right Gram operator of analysis. -/
theorem finiteFrameOperator_eq_adjointCompSelf (v : ι → E) :
    finiteFrameOperator v = (finiteAnalysis v).adjoint.comp (finiteAnalysis v) := by
  sorry

/-- The coefficient Gram operator is the left Gram operator of analysis. -/
theorem finiteGramOperator_eq_selfCompAdjoint (v : ι → E) :
    finiteGramOperator v = (finiteAnalysis v).comp (finiteAnalysis v).adjoint := by
  sorry

/-- The frame operator is positive. -/
theorem finiteFrameOperator_isPositive (v : ι → E) :
    (finiteFrameOperator v).IsPositive := by
  sorry

/-- The Gram operator is positive. -/
theorem finiteGramOperator_isPositive (v : ι → E) :
    (finiteGramOperator v).IsPositive := by
  sorry

/-- The frame quadratic form is the sum of squared analysis coefficients.

Proof strategy:

1. rewrite the frame operator as `analysis† ∘ analysis`;
2. move the adjoint through the inner product;
3. reduce to `‖finiteAnalysis v x‖²`;
4. expand the Euclidean norm square as the finite sum of coordinate norm squares.

This should be the only coordinate-level identity needed by downstream frame-bound proofs.
-/
theorem re_inner_finiteFrameOperator_eq_sum_sq
    (v : ι → E) (x : E) :
    RCLike.re (inner 𝕜 (finiteFrameOperator v x) x) =
      ∑ i, ‖inner 𝕜 (v i) x‖ ^ 2 := by
  sorry

/-- Frame bounds are exactly Löwner bounds on the positive frame operator.

Executable proof strategy:

1. unfold `HasFiniteFrameBounds` and rewrite with
   `re_inner_finiteFrameOperator_eq_sum_sq`;
2. use `LinearMap.le_def` and `LinearMap.nonneg_iff_isPositive`;
3. expand positivity of `finiteFrameOperator v - a • 1` and
   `b • 1 - finiteFrameOperator v` through their quadratic forms;
4. keep coercions `(a : 𝕜)` and `(b : 𝕜)` explicit and use `RCLike.ofReal_nonneg`.

The final statement may split the required side conditions `0 ≤ a` and `a ≤ b` from the
operator-order equivalence if reviewers prefer a more orthogonal API.
-/
theorem hasFiniteFrameBounds_iff_loewner
    (v : ι → E) (a b : ℝ) :
    HasFiniteFrameBounds v a b ↔
      0 ≤ a ∧ a ≤ b ∧
        (a : 𝕜) • (1 : E →ₗ[𝕜] E) ≤ finiteFrameOperator v ∧
        finiteFrameOperator v ≤ (b : 𝕜) • (1 : E →ₗ[𝕜] E) := by
  sorry

/-- Injectivity of analysis is equivalent to spanning of the finite family.

Proof strategy: characterize `ker (finiteAnalysis v)` as the orthogonal complement of
`Submodule.span 𝕜 (Set.range v)`. Then use `ker_eq_bot` and `orthogonal_eq_bot_iff` (or the
available finite-dimensional equivalent) to conclude that the span is `⊤`.
-/
theorem finiteAnalysis_injective_iff_span_eq_top (v : ι → E) :
    Function.Injective (finiteAnalysis v) ↔
      Submodule.span 𝕜 (Set.range v) = ⊤ := by
  sorry

/-- In finite dimension, injectivity of analysis yields a positive lower frame bound.

Proof strategy: apply `LinearMap.exists_antilipschitzWith` to `finiteAnalysis v`, exactly as
in the MIT-licensed vendored `drifting-identifiability` proof, then square the gain
inequality and rewrite the analysis norm using the frame quadratic-form identity.
-/
theorem exists_pos_lowerFrameBound_of_injective
    (v : ι → E) (hinj : Function.Injective (finiteAnalysis v)) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : E,
      a * ‖x‖ ^ 2 ≤ ∑ i, ‖inner 𝕜 (v i) x‖ ^ 2 := by
  sorry

/-- A finite family spans iff it admits a positive lower frame bound.

Proof strategy: combine `finiteAnalysis_injective_iff_span_eq_top`,
`exists_pos_lowerFrameBound_of_injective`, and the easy converse obtained by evaluating the
lower bound on a vector in the kernel of analysis.
-/
theorem spans_iff_exists_pos_lowerFrameBound (v : ι → E) :
    Submodule.span 𝕜 (Set.range v) = ⊤ ↔
      ∃ a : ℝ, 0 < a ∧ ∀ x : E,
        a * ‖x‖ ^ 2 ≤ ∑ i, ‖inner 𝕜 (v i) x‖ ^ 2 := by
  sorry

/-- The optimal lower frame constant is the square of the smallest domain-indexed singular
value of analysis.

Proof strategy: prove or reuse the singular Courant–Fischer minimum-gain formula, specialize
it to the full domain, and rewrite the quotient numerator via the frame quadratic-form
identity. Treat the zero-dimensional endpoint separately instead of introducing a junk
`Fin 0` index.
-/
theorem smallestSingularValue_sq_is_lowerFrameBound
    (v : ι → E) {n : ℕ} (hn : finrank 𝕜 E = n) (hn0 : 0 < n) (x : E) :
    (finiteAnalysis v).singularValues (n - 1) ^ 2 * ‖x‖ ^ 2 ≤
      ∑ i, ‖inner 𝕜 (v i) x‖ ^ 2 := by
  sorry

/-- Frame and Gram operators have the same positive spectrum, including multiplicities.

Proof strategy: rewrite them as the two adjoint products of `finiteAnalysis v`, then apply
`finrank_eigenspace_adjointCompSelf_eq_selfCompAdjoint`.
-/
theorem finrank_eigenspace_finiteFrameOperator_eq_finiteGramOperator
    (v : ι → E) (μ : 𝕜) (hμ : μ ≠ 0) :
    finrank 𝕜 (Module.End.eigenspace (finiteFrameOperator v) μ) =
      finrank 𝕜 (Module.End.eigenspace (finiteGramOperator v) μ) := by
  sorry

/-- Singular values of analysis and synthesis coincide under zero padding. -/
theorem finiteAnalysis_singularValues_adjoint (v : ι → E) :
    (finiteAnalysis v).adjoint.singularValues = (finiteAnalysis v).singularValues := by
  exact singularValues_adjoint_rectangular (finiteAnalysis v)

end ForMathlib
