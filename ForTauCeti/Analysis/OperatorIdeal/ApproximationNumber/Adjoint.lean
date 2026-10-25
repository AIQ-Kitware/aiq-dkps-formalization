/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint

/-!
# Compactness of the adjoint on Hilbert spaces

The remaining Schauder consequences use Tau Ceti's canonical singular values:
compactness is equivalent to their convergence to zero, and taking the adjoint
preserves them. No real-valued approximation-number layer is imported.

## Provenance

The original DKPS adjoint-invariance proof was adapted from
`ForMathlib/Analysis/Normed/Operator/ApproximationNumberAdjoint.lean`. Its rank and
approximation arguments were replaced by accepted Tau Ceti APIs. The compactness
consequence remains local; the duplicate compactness/approximability proofs have
also been retired in favor of accepted `ApproximationNumber.Compact`.
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

Compactness on a complete Hilbert target is equivalent to vanishing singular values.
Taking the adjoint preserves those values. -/
theorem isCompactOperator_adjoint {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    IsCompactOperator T.adjoint := by
  apply isCompactOperator_of_tendsto_singularValue
  have h : T.adjoint.singularValue = T.singularValue := funext T.singularValue_adjoint
  rw [h]
  exact hT.tendsto_singularValue

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
