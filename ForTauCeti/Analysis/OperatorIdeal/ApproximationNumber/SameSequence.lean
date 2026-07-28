/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan

/-!
# Operators with the same approximation-number sequence

Two bounded operators, possibly between different pairs of Hilbert spaces, **have the same
approximation numbers** when their whole sequences agree:

```
A.HasSameApproximationNumbers B ↔ ∀ n, A.approximationNumber n = B.approximationNumber n.
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
  `ContinuousLinearMap.HasSameApproximationNumbers` and is spelled with
  `approximationNumber` rather than its `approximationSingularValue` alias.
* Extraction motive: `DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean` — a
  *generic* module — imported the source-layer file above for these six declarations alone.
  That backwards dependency was the last obstacle recorded against extraction cluster 1b.
* Spectra influence: none.
-/

@[expose] public section

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

/-- `A` and `B` have the same complete approximation-number sequence. -/
def HasSameApproximationNumbers (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₂) : Prop :=
  ∀ n : ℕ, A.approximationNumber n = B.approximationNumber n

namespace HasSameApproximationNumbers

@[refl] theorem refl (A : E₁ →L[𝕜] F₁) : A.HasSameApproximationNumbers A := fun _ => rfl

theorem symm {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : A.HasSameApproximationNumbers B) : B.HasSameApproximationNumbers A :=
  fun n => (h n).symm

theorem trans {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂} {C : E₃ →L[𝕜] F₃}
    (hAB : A.HasSameApproximationNumbers B) (hBC : B.HasSameApproximationNumbers C) :
    A.HasSameApproximationNumbers C :=
  fun n => (hAB n).trans (hBC n)

/-- Equal approximation numbers give equal operator norms: they agree already at `n = 0`. -/
theorem norm_eq {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : A.HasSameApproximationNumbers B) : ‖A‖ = ‖B‖ := by
  rw [← A.approximationNumber_index_zero, ← B.approximationNumber_index_zero, h 0]

/-- Equal approximation numbers give equal Ky Fan gauges. -/
theorem kyFanGauge_eq {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : A.HasSameApproximationNumbers B) (k : ℕ) :
    A.kyFanGauge k = B.kyFanGauge k :=
  Finset.sum_congr rfl fun n _ => h n

end HasSameApproximationNumbers

end ContinuousLinearMap
