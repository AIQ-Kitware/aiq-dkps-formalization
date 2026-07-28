/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
import ForTauCeti.Analysis.InnerProductSpace.OperatorModulus

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
    approximationSingularValue n A ≤ approximationSingularValue n B := by
  by_contra hnot
  have hlt : approximationSingularValue n B <
      approximationSingularValue n A := lt_of_not_ge hnot
  have hB0 : 0 ≤ approximationSingularValue n B :=
    approximationSingularValue_nonneg n B
  obtain ⟨s, hrs, v, hv, hV⟩ :=
    (SpectraBridge.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
      A n hB0).mp hlt
  have hself : approximationSingularValue n B <
      approximationSingularValue n B :=
    (SpectraBridge.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
      B n hB0).mpr ⟨s, hrs, v, hv, fun x hx => (hV x hx).trans (h x)⟩
  exact lt_irrefl _ hself

/-- Pointwise equality of norms determines every approximation singular value
on complex Hilbert spaces.  The two operators may have different targets, so
the conclusion is the heterogeneous singular-sequence relation. -/
theorem sameApproximationSingularValues_of_norm_apply_eq
    {G : Type vG} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : E →L[ℂ] F) (B : E →L[ℂ] G) (h : ∀ x : E, ‖A x‖ = ‖B x‖) :
    SameApproximationSingularSequence A B := fun n =>
  le_antisymm
    (approximationSingularValue_le_of_norm_apply_le A B (fun x => (h x).le) n)
    (approximationSingularValue_le_of_norm_apply_le B A (fun x => (h x).ge) n)

/-- A rectangular operator and its positive source modulus have the same
complete singular-value sequence.  The modulus acts on `E` while `T` maps into
`F`, so this is the heterogeneous relation. -/
theorem sameApproximationSingularValues_rectangularOperatorModulus
    (T : E →L[ℂ] F) :
    SameApproximationSingularSequence (ContinuousLinearMap.modulus T) T :=
  sameApproximationSingularValues_of_norm_apply_eq _ _
    (ContinuousLinearMap.norm_modulus_apply T)

/-- Square-operator specialization. -/
theorem modulus_sameApproximationSingularValues
    (T : E →L[ℂ] E) :
    SameApproximationSingularValues (ContinuousLinearMap.modulus T) T :=
  sameApproximationSingularValues_of_norm_apply_eq _ _
    (ContinuousLinearMap.norm_modulus_apply T)

/-- Every current ideal family assigns the same membership and gauge to `T`
and its positive modulus. -/
theorem modulus_mem_and_gauge_eq
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    {T : E →L[ℂ] E}
    (hT : N.toRectangularSymmetricIdealFamily.Mem T) :
    N.toRectangularSymmetricIdealFamily.Mem (ContinuousLinearMap.modulus T) ∧
      N.toRectangularSymmetricIdealFamily.gauge (ContinuousLinearMap.modulus T) =
        N.toRectangularSymmetricIdealFamily.gauge T :=
  (modulus_sameApproximationSingularValues T).mem_and_gauge_eq N hT

/-- Every literal paper norm assigns exactly the same extended value to an
operator and its positive modulus. -/
theorem paperNorm_modulus_eq
    (N : PaperUnitaryInvariantNorm) (T : E →L[ℂ] E) :
    N.extendedGauge (ContinuousLinearMap.modulus T) = N.extendedGauge T :=
  N.gauge_eq_of_sameApproximationSingularValues
    (modulus_sameApproximationSingularValues T)

end

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti