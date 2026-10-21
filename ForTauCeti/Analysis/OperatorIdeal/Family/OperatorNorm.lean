/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.OperatorIdeal.OperatorNorm
public import ForTauCeti.Analysis.OperatorIdeal.Family.Basic

/-!
# The operator norm in the symmetric ideal-family view

Tau Ceti defines the rectangular operator-norm family as
`OperatorIdealFamily.opNorm` and supplies its completeness proof. This module
packages that accepted family as a symmetric diagonal family for current DKPS
consumers. The local real two-sided composition estimate is used in the
unbounded Neumann argument.

The remaining `operatorNormFamily` spelling is a transitional consumer-facing
specialization. It does not define a new rectangular family or a new carrier.

## Provenance

* The rectangular family and completeness result are provided by
  `TauCeti.Analysis.OperatorIdeal.OperatorNorm`.
* DKPS-specific consumer migration is tracked in the repository history.
* Copyright and license remain those of Kitware, Inc., Apache 2.0.
-/

public section

namespace TauCeti

open scoped ENNReal

universe u v w

section Base

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Submultiplicativity of the operator norm across a **two-sided** composition.

Mathlib has the two-fold `ContinuousLinearMap.opNorm_comp_le`; the two-sided
form is what every ideal law is stated against, so it is worth a name.  Nothing
here needs an inner product or completeness — it is a fact about normed spaces
— but it is stated where its first consumer is rather than in a file of its own.

`opNorm_comp_comp_le` in the legacy rectangular namespace was this same calc
proof, verbatim; it now delegates here. -/
theorem ContinuousLinearMap.opNorm_comp_comp_le
    {𝕜 : Type*} [RCLike 𝕜]
    {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    ‖L ∘L A ∘L R‖ ≤ ‖L‖ * ‖A‖ * ‖R‖ :=
  calc ‖L ∘L A ∘L R‖ ≤ ‖L‖ * ‖A ∘L R‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * (‖A‖ * ‖R‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le A R) (norm_nonneg L)
    _ = ‖L‖ * ‖A‖ * ‖R‖ := (mul_assoc _ _ _).symm

end Base

section Symmetric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The operator norm, as a *symmetric* ideal family: the adjoint is an
isometry, so the operator norm is adjoint-invariant. -/
@[expose]
noncomputable def operatorNormFamily (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toOperatorIdealFamily := OperatorIdealFamily.opNorm 𝕜
  gauge_adjoint A := by
    simp only [OperatorIdealFamily.gauge_opNorm, ← ofReal_norm]
    rw [ContinuousLinearMap.adjoint.norm_map]

/-- Completeness transfers to the symmetric view, which shares its underlying
family with `OperatorIdealFamily.opNorm`. The instance has to be restated rather
than inherited: `instIsCompleteOperatorNormIdealFamily` is stated at three
independent universes, and the symmetric family constrains the last two to be
equal, so instance search does not find it without this specialization. -/
instance : (operatorNormFamily.{u, v} 𝕜).toOperatorIdealFamily.IsComplete :=
  inferInstanceAs (OperatorIdealFamily.opNorm.{u, v, v} 𝕜).IsComplete

/-- The symmetric operator-norm family has the same gauge as the plain one; the
symmetric structure adds adjoint-invariance, not a different norm. -/
@[simp]
theorem gauge_operatorNormFamily (A : E →L[𝕜] F) :
    (operatorNormFamily.{u, v} 𝕜).gauge A = ‖A‖ₑ := by
  exact OperatorIdealFamily.gauge_opNorm A
end Symmetric

end TauCeti
