/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
import ForMathlib.Analysis.InnerProductSpace.OperatorAbsoluteValue

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

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v vF vG

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The positive source modulus `(T* T)^(1/2)` of a rectangular operator. -/
noncomputable def rectangularOperatorModulus (T : E →L[ℂ] F) : E →L[ℂ] E :=
  CFC.sqrt (T.adjoint ∘L T)

/-- The Gram operator of a rectangular map is nonnegative. -/
theorem rectangularGram_nonneg (T : E →L[ℂ] F) :
    0 ≤ T.adjoint ∘L T :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self T)

/-- The rectangular modulus is nonnegative. -/
theorem rectangularOperatorModulus_nonneg (T : E →L[ℂ] F) :
    0 ≤ rectangularOperatorModulus T :=
  CFC.sqrt_nonneg _

/-- The rectangular modulus is self-adjoint. -/
theorem isSelfAdjoint_rectangularOperatorModulus (T : E →L[ℂ] F) :
    IsSelfAdjoint (rectangularOperatorModulus T) :=
  IsSelfAdjoint.of_nonneg (rectangularOperatorModulus_nonneg T)

/-- Defining square identity for the rectangular modulus. -/
theorem rectangularOperatorModulus_mul_self (T : E →L[ℂ] F) :
    rectangularOperatorModulus T * rectangularOperatorModulus T =
      T.adjoint ∘L T := by
  exact CFC.sqrt_mul_sqrt_self _ (rectangularGram_nonneg T)

/-- The rectangular modulus preserves the pointwise norm of `T`. -/
theorem norm_rectangularOperatorModulus_apply (T : E →L[ℂ] F) (x : E) :
    ‖rectangularOperatorModulus T x‖ = ‖T x‖ := by
  have hself : (rectangularOperatorModulus T).adjoint =
      rectangularOperatorModulus T := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (isSelfAdjoint_rectangularOperatorModulus T).star_eq
  have hmod :
      (⟪rectangularOperatorModulus T x,
          rectangularOperatorModulus T x⟫_ℂ : ℂ) =
        ⟪x, (rectangularOperatorModulus T *
          rectangularOperatorModulus T) x⟫_ℂ := by
    calc
      (⟪rectangularOperatorModulus T x,
          rectangularOperatorModulus T x⟫_ℂ : ℂ)
          = ⟪(rectangularOperatorModulus T).adjoint x,
              rectangularOperatorModulus T x⟫_ℂ := by rw [hself]
      _ = ⟪x, rectangularOperatorModulus T
              (rectangularOperatorModulus T x)⟫_ℂ :=
            ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = ⟪x, (rectangularOperatorModulus T *
              rectangularOperatorModulus T) x⟫_ℂ := rfl
  have hT : (⟪T x, T x⟫_ℂ : ℂ) = ⟪x, (T.adjoint ∘L T) x⟫_ℂ := by
    exact (ContinuousLinearMap.adjoint_inner_right T x (T x)).symm
  have hinner :
      (⟪rectangularOperatorModulus T x,
          rectangularOperatorModulus T x⟫_ℂ : ℂ) = ⟪T x, T x⟫_ℂ := by
    rw [hmod, hT, rectangularOperatorModulus_mul_self]
  have hsq : ‖rectangularOperatorModulus T x‖ ^ 2 = ‖T x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
    exact_mod_cast hinner
  have hsqrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt

/-- The rectangular modulus has the same operator norm as the original map. -/
theorem norm_rectangularOperatorModulus (T : E →L[ℂ] F) :
    ‖rectangularOperatorModulus T‖ = ‖T‖ := by
  apply le_antisymm
  · refine (rectangularOperatorModulus T).opNorm_le_bound (norm_nonneg T) ?_
    intro x
    rw [norm_rectangularOperatorModulus_apply]
    exact T.le_opNorm x
  · refine T.opNorm_le_bound (norm_nonneg (rectangularOperatorModulus T)) ?_
    intro x
    rw [← norm_rectangularOperatorModulus_apply]
    exact (rectangularOperatorModulus T).le_opNorm x

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
    SameApproximationSingularSequence (rectangularOperatorModulus T) T :=
  sameApproximationSingularValues_of_norm_apply_eq _ _
    (norm_rectangularOperatorModulus_apply T)

/-- Square-operator specialization. -/
theorem operatorAbs_sameApproximationSingularValues
    (T : E →L[ℂ] E) :
    SameApproximationSingularValues (ForMathlib.operatorAbs T) T :=
  sameApproximationSingularValues_of_norm_apply_eq _ _
    (ForMathlib.norm_operatorAbs_apply T)

/-- Every current ideal family assigns the same membership and gauge to `T`
and its positive modulus. -/
theorem operatorAbs_mem_and_gauge_eq
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    {T : E →L[ℂ] E}
    (hT : N.toRectangularSymmetricIdealFamily.Mem T) :
    N.toRectangularSymmetricIdealFamily.Mem (ForMathlib.operatorAbs T) ∧
      N.toRectangularSymmetricIdealFamily.gauge (ForMathlib.operatorAbs T) =
        N.toRectangularSymmetricIdealFamily.gauge T :=
  (operatorAbs_sameApproximationSingularValues T).mem_and_gauge_eq N hT

/-- Every literal paper norm assigns exactly the same extended value to an
operator and its positive modulus. -/
theorem paperNorm_operatorAbs_eq
    (N : PaperUnitaryInvariantNorm) (T : E →L[ℂ] E) :
    N.extendedGauge (ForMathlib.operatorAbs T) = N.extendedGauge T :=
  N.gauge_eq_of_sameApproximationSingularValues
    (operatorAbs_sameApproximationSingularValues T)

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
