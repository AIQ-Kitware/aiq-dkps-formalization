/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperSingularValueTransport
import DavisKahan.Experimental.InfiniteDimensional.Core.Compatibility

/-!
# Singular-value transport across canonical subspace coordinates

The paper writes projection blocks as ambient operators, whereas the natural
Lean theorem often uses a subtype as source or target.  Canonical inclusion and
orthogonal projection add only zero singular values, so the complete
approximation-number sequence is unchanged.  These lemmas make that
identification explicit.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Extending a map from a closed subspace by zero on its orthogonal complement
preserves every approximation singular value. -/
theorem sameApproximationSingularValues_extendDomainByZero
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : U →L[𝕜] F) :
    SameApproximationSingularValues
      (T ∘L U.subtypeL.adjoint) T := by
  intro n
  apply le_antisymm
  · have hraw := congrArg (fun x : NNReal => (x : ℝ))
      (T.approximationNumber_comp_right_le U.subtypeL.adjoint n)
    have hnorm : ‖U.subtypeL.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint_norm]
      exact U.norm_subtypeL_le
    exact (by
      simpa only [approximationSingularValue, NNReal.coe_mul, coe_nnnorm]
        using hraw).trans
      (mul_le_of_le_one_right (approximationSingularValue_nonneg n T) hnorm)
  · have hfactor :
        (T ∘L U.subtypeL.adjoint) ∘L U.subtypeL = T := by
      rw [← ContinuousLinearMap.comp_assoc,
        Submodule.adjoint_subtypeL_comp_subtypeL]
      simp
    rw [← hfactor]
    have hraw := congrArg (fun x : NNReal => (x : ℝ))
      ((T ∘L U.subtypeL.adjoint).approximationNumber_comp_right_le
        U.subtypeL n)
    have hnorm : ‖U.subtypeL‖ ≤ 1 := U.norm_subtypeL_le
    exact (by
      simpa only [approximationSingularValue, NNReal.coe_mul, coe_nnnorm]
        using hraw).trans
      (mul_le_of_le_one_right
        (approximationSingularValue_nonneg n
          (T ∘L U.subtypeL.adjoint)) hnorm)

/-- Including the range of a map into the ambient Hilbert space preserves every
approximation singular value. -/
theorem sameApproximationSingularValues_includeCodomain
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] V) :
    SameApproximationSingularValues (V.subtypeL ∘L T) T := by
  intro n
  apply le_antisymm
  · have hraw := congrArg (fun x : NNReal => (x : ℝ))
      (T.approximationNumber_comp_left_le V.subtypeL n)
    exact (by
      simpa only [approximationSingularValue, NNReal.coe_mul, coe_nnnorm]
        using hraw).trans
      (mul_le_of_le_one_left (approximationSingularValue_nonneg n T)
        V.norm_subtypeL_le)
  · have hfactor : V.subtypeL.adjoint ∘L (V.subtypeL ∘L T) = T := by
      rw [ContinuousLinearMap.comp_assoc,
        Submodule.adjoint_subtypeL_comp_subtypeL]
      simp
    rw [← hfactor]
    have hraw := congrArg (fun x : NNReal => (x : ℝ))
      ((V.subtypeL ∘L T).approximationNumber_comp_left_le
        V.subtypeL.adjoint n)
    have hnorm : ‖V.subtypeL.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint_norm]
      exact V.norm_subtypeL_le
    exact (by
      simpa only [approximationSingularValue, NNReal.coe_mul, coe_nnnorm]
        using hraw).trans
      (mul_le_of_le_one_left
        (approximationSingularValue_nonneg n (V.subtypeL ∘L T)) hnorm)

/-- Ambient extension of a rectangular subspace block preserves the complete
singular-value sequence. -/
theorem sameApproximationSingularValues_ambientSubspaceBlock
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : U →L[𝕜] V) :
    SameApproximationSingularValues
      (V.subtypeL ∘L T ∘L U.subtypeL.adjoint) T := by
  exact (sameApproximationSingularValues_includeCodomain V
    (T ∘L U.subtypeL.adjoint)).trans
      (sameApproximationSingularValues_extendDomainByZero U T)

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
