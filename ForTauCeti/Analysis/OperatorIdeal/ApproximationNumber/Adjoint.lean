/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.CanonicalGauge
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.CompactHilbert
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint

/-!
# Adjoint invariance of approximation numbers

Tau Ceti proves adjoint invariance for its canonical `ℝ≥0` approximation numbers. The redundant
real-valued adjoint theorem has been removed; consumers now use that canonical result through the
real-view equation where needed. The compact-adjoint result remains local because it follows from
the maintained compactness/approximation-number criterion, for which Tau Ceti has no equivalent.

## Provenance

The original local adjoint proof was adapted from
`ForMathlib/Analysis/Normed/Operator/ApproximationNumberAdjoint.lean`. Its rank and approximation
arguments have been removed in favor of
`TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint`.
-/

public section

noncomputable section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Schauder's theorem for Hilbert spaces:** the adjoint of a compact operator is compact.

Compactness on a complete Hilbert target is equivalent to the vanishing of the approximation
numbers. Tau Ceti now supplies adjoint invariance of those numbers, so this local consequence is
an equality rewrite. -/
theorem isCompactOperator_adjoint {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    IsCompactOperator T.adjoint := by
  rw [isCompactOperator_iff_tendsto_approximationNumber]
  have hadj : T.adjoint.approximationNumber = T.approximationNumber := by
    funext n
    rw [approximationNumber_eq_singularValue_toReal,
      approximationNumber_eq_singularValue_toReal, singularValue_adjoint]
  rw [hadj]
  exact (isCompactOperator_iff_tendsto_approximationNumber T).1 hT

/-- Schauder's theorem in both directions. -/
@[simp]
theorem isCompactOperator_adjoint_iff {T : E →L[𝕜] F} :
    IsCompactOperator T.adjoint ↔ IsCompactOperator T :=
  ⟨fun h => by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using isCompactOperator_adjoint h,
    isCompactOperator_adjoint⟩

end ContinuousLinearMap

end

end
