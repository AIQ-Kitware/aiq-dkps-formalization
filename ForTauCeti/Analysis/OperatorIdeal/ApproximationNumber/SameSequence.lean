/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Completion
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Modulus
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Operators with the same approximation-number sequence

Two bounded operators, possibly between different pairs of Hilbert spaces, **have the same
approximation numbers** when their whole sequences agree:

```
A.SameSingularValues B ↔ ∀ n, A.singularValue n = B.singularValue n.
```

Since every unitarily invariant norm is a function of that sequence, this is the exact
hypothesis under which two operators are interchangeable for ideal-theoretic purposes, and
it is the relation the Davis--Kahan sine-theta development uses literally.

The relation is deliberately *heterogeneous* — the four spaces are independent — because its
uses compare an operator with a transported copy of itself living somewhere else.  That is
also why it is stated as a plain `Prop` rather than a `Setoid`: it is reflexive, symmetric
and transitive, but not on a single type.

Completeness of the four spaces is *not* assumed: approximation numbers are defined for
bounded operators between normed spaces, and nothing here needs more.  The source relation
carried the hypothesis, so this is a small generalisation.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/SingularValueTransport.lean`.
* Original declarations: `TauCeti.DavisKahan.Experimental.ExactSinTheta.{`
  `SameApproximationSingularSequence, SameApproximationSingularSequence.refl,`
  `SameApproximationSingularSequence.symm, SameApproximationSingularSequence.trans,`
  `SameApproximationSingularSequence.opNorm_eq,`
  `SameApproximationSingularSequence.kyFanApproximationGauge_eq}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **copied and renamespaced**.  The relation moves to
  `ContinuousLinearMap.HasSameApproximationNumbers` and was spelled with
  `approximationNumber` rather than its `approximationSingularValue` alias.
  The relation and its equivalence proofs have since been retired in favor of
  accepted `ContinuousLinearMap.SameSingularValues`; only the additional
  norm and incomplete-target comparison results remain local.
* Extraction motive: `DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean` — a
  *generic* module — imported the source-layer file above for these six declarations alone.
  That backwards dependency was the last obstacle recorded against extraction cluster 1b.
* Spectra influence: none.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

universe u v₁ w₁ v₂ w₂ v₃ w₃

variable {𝕜 : Type u} [RCLike 𝕜]
  {E₁ : Type v₁} {F₁ : Type w₁} {E₂ : Type v₂} {F₂ : Type w₂} {E₃ : Type v₃} {F₃ : Type w₃}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
  [NormedAddCommGroup F₃] [InnerProductSpace 𝕜 F₃]

/-- Equal canonical singular-value sequences give equal operator norms. -/
theorem SameSingularValues.norm_eq {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : A.SameSingularValues B) : ‖A‖ = ‖B‖ := by
  have hzero := (sameSingularValues_iff _ _).mp h 0
  simpa only [singularValue_zero, coe_nnNorm] using congrArg NNReal.toReal hzero

/-! Equality of sequences and its equivalence laws are maintained by Tau Ceti's
`ContinuousLinearMap.SameSingularValues`. Only the additional Hilbert-space
comparison results remain here. -/

section PointwiseComparison

/-! ## Pointwise comparison for incomplete targets -/

variable {X : Type v₁} {Y : Type w₁} {Z : Type w₂}
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace 𝕜 Z] [CompleteSpace Z]

omit [CompleteSpace Y] [CompleteSpace Z] in
/-- Pointwise norm domination compares approximation numbers even when the
target spaces are incomplete. Passing to their completions preserves both
the pointwise bounds and every approximation number. -/
theorem approximationNumber_le_of_norm_apply_le [CompleteSpace X]
    (A : X →L[𝕜] Y) (B : X →L[𝕜] Z) (h : ∀ x : X, ‖A x‖ ≤ ‖B x‖) (n : ℕ) :
    (A.singularValue n : ℝ) ≤ (B.singularValue n : ℝ) := by
  let A' := (UniformSpace.Completion.toComplL : Y →L[𝕜] UniformSpace.Completion Y) ∘L A
  let B' := (UniformSpace.Completion.toComplL : Z →L[𝕜] UniformSpace.Completion Z) ∘L B
  have h' (x : X) : ‖A' x‖ ≤ ((1 : ℝ≥0) : ℝ) * ‖B' x‖ := by
    simpa only [A', B', ContinuousLinearMap.comp_apply, UniformSpace.Completion.coe_toComplL,
      UniformSpace.Completion.norm_coe, NNReal.coe_one, one_mul] using h x
  have hle := singularValue_le_mul_of_forall_norm_apply_le h' n
  dsimp only [A', B'] at hle
  rw [one_mul, A.singularValue_toComplL_comp, B.singularValue_toComplL_comp] at hle
  exact NNReal.coe_le_coe.mpr hle

omit [CompleteSpace Y] [CompleteSpace Z] in
/-- Pointwise equality of norms determines the whole approximation-number sequence.  The two
operators may have different targets, which is what the heterogeneous relation is for. -/
theorem hasSameApproximationNumbers_of_norm_apply_eq [CompleteSpace X]
    (A : X →L[𝕜] Y) (B : X →L[𝕜] Z) (h : ∀ x : X, ‖A x‖ = ‖B x‖) :
    A.SameSingularValues B := by
  apply (sameSingularValues_iff _ _).mpr
  intro n
  apply NNReal.eq
  exact le_antisymm
    (approximationNumber_le_of_norm_apply_le A B (fun x => (h x).le) n)
    (approximationNumber_le_of_norm_apply_le B A (fun x => (h x).ge) n)

end PointwiseComparison

end ContinuousLinearMap
