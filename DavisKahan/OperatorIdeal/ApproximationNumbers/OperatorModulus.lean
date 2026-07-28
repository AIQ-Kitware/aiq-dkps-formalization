/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence

/-!
# Approximation singular values of the rectangular operator modulus

For a bounded operator `T : E -> F`, its source modulus is the positive square
root of `T* T` on `E`.  The paper uses this object to define the cosine and sine
of a directed operator angle.  Its complete approximation-singular-value
sequence is exactly that of `T`.

The proof avoids any choice of polar factor.  The repository's exact min--max
characterization shows that pointwise equality of norms determines every
approximation number, while the square-root identity gives
`norm (|T| x) = norm (T x)`.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v vF vG

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A pointwise lower modulus comparison transports every approximation
singular value.  The argument is the exact Courant--Fischer localization: any
strict lower bound for `a_n A` is realized on an `(n+1)`-dimensional subspace,
and the pointwise estimate carries that same subspace witness over to `B`.

This is rank-safe.  No averaging of `A` against a second operator is performed,
so no rank doubling can occur. -/
theorem approximationSingularValue_le_of_norm_apply_le
    {G : Type vG} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : E →L[ℂ] F) (B : E →L[ℂ] G) (h : ∀ x : E, ‖A x‖ ≤ ‖B x‖) (n : ℕ) :
    A.approximationNumber n ≤ B.approximationNumber n :=
  ContinuousLinearMap.approximationNumber_le_of_norm_apply_le A B h n

/-- Pointwise equality of norms determines every approximation singular value
on complex Hilbert spaces.  The two operators may have different targets, so
the conclusion is the heterogeneous singular-sequence relation. -/
theorem sameApproximationSingularValues_of_norm_apply_eq
    {G : Type vG} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : E →L[ℂ] F) (B : E →L[ℂ] G) (h : ∀ x : E, ‖A x‖ = ‖B x‖) :
    A.HasSameApproximationNumbers B :=
  ContinuousLinearMap.hasSameApproximationNumbers_of_norm_apply_eq A B h

/-- A rectangular operator and its positive source modulus have the same
complete singular-value sequence.  The modulus acts on `E` while `T` maps into
`F`, so this is the heterogeneous relation. -/
theorem sameApproximationSingularValues_rectangularOperatorModulus
    (T : E →L[ℂ] F) :
    (ContinuousLinearMap.modulus T).HasSameApproximationNumbers T :=
  T.modulus_hasSameApproximationNumbers

/-- Square-operator specialization. -/
theorem modulus_sameApproximationSingularValues
    (T : E →L[ℂ] E) :
    (ContinuousLinearMap.modulus T).HasSameApproximationNumbers T :=
  T.modulus_hasSameApproximationNumbers

end

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti