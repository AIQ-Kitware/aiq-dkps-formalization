/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport
import DavisKahan.BoundedOperator.Compat

/-!
# Singular-value transport across canonical subspace coordinates

The paper writes projection blocks as ambient operators, whereas the natural
Lean theorem often uses a subtype as source or target.  Canonical inclusion and
orthogonal projection add only zero singular values, so the complete
approximation-number sequence is unchanged.  These lemmas make that
identification explicit.

Because the ambient and subtype coordinates are genuinely different Hilbert
spaces, the statements use the heterogeneous relation
`SameApproximationSingularSequence` rather than its same-type specialisation
`SameApproximationSingularValues`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete.  `local instance` does not propagate through imports,
so it is reinstalled here. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjection
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

omit [CompleteSpace E] in
/-- The canonical inclusion of a subspace has `‖·‖ ≤ 1`. -/
private theorem norm_subtypeL_le_one (U : Submodule 𝕜 E) :
    ‖U.subtypeL‖ ≤ 1 := by
  exact_mod_cast U.norm_subtypeL_le

/-- The adjoint of the canonical inclusion is the orthogonal projection, so it
too has `‖·‖ ≤ 1`. -/
private theorem norm_adjoint_subtypeL_le_one
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    ‖U.subtypeL.adjoint‖ ≤ 1 := by
  rw [Submodule.adjoint_subtypeL]
  exact_mod_cast U.orthogonalProjectionOnto_norm_le

/-- Extending a map from a closed subspace by zero on its orthogonal complement
preserves every approximation singular value. -/
theorem sameApproximationSingularValues_extendDomainByZero
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : U →L[𝕜] F) :
    SameApproximationSingularSequence
      (T ∘L U.subtypeL.adjoint) T := by
  intro n
  have hfactor : (T ∘L U.subtypeL.adjoint) ∘L U.subtypeL = T := by
    ext x
    simp [Submodule.adjoint_subtypeL]
  have key : (T ∘L U.subtypeL.adjoint).approximationNumber n
      = T.approximationNumber n := by
    refine le_antisymm ?_ ?_
    · calc (T ∘L U.subtypeL.adjoint).approximationNumber n
          ≤ T.approximationNumber n * ‖U.subtypeL.adjoint‖ :=
            T.approximationNumber_comp_le_mul_norm _ n
        _ ≤ T.approximationNumber n * 1 := by
            gcongr <;>
              first
                | exact norm_adjoint_subtypeL_le_one U
                | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
        _ = T.approximationNumber n := mul_one _
    · calc T.approximationNumber n
          = ((T ∘L U.subtypeL.adjoint) ∘L U.subtypeL).approximationNumber n := by
            rw [hfactor]
        _ ≤ (T ∘L U.subtypeL.adjoint).approximationNumber n * ‖U.subtypeL‖ :=
            (T ∘L U.subtypeL.adjoint).approximationNumber_comp_le_mul_norm _ n
        _ ≤ (T ∘L U.subtypeL.adjoint).approximationNumber n * 1 := by
            gcongr <;>
              first
                | exact norm_subtypeL_le_one U
                | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
        _ = (T ∘L U.subtypeL.adjoint).approximationNumber n := mul_one _
  exact key

/-- Including the range of a map into the ambient Hilbert space preserves every
approximation singular value. -/
theorem sameApproximationSingularValues_includeCodomain
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] V) :
    SameApproximationSingularSequence (V.subtypeL ∘L T) T := by
  intro n
  have hfactor : V.subtypeL.adjoint ∘L (V.subtypeL ∘L T) = T := by
    ext x
    simp [Submodule.adjoint_subtypeL]
  have key : (V.subtypeL ∘L T).approximationNumber n
      = T.approximationNumber n := by
    refine le_antisymm ?_ ?_
    · calc (V.subtypeL ∘L T).approximationNumber n
          ≤ ‖V.subtypeL‖ * T.approximationNumber n :=
            ContinuousLinearMap.approximationNumber_comp_le_norm_mul _ T n
        _ ≤ 1 * T.approximationNumber n := by
            gcongr <;>
              first
                | exact norm_subtypeL_le_one V
                | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
        _ = T.approximationNumber n := one_mul _
    · calc T.approximationNumber n
          = (V.subtypeL.adjoint ∘L (V.subtypeL ∘L T)).approximationNumber n := by
            rw [hfactor]
        _ ≤ ‖V.subtypeL.adjoint‖ * (V.subtypeL ∘L T).approximationNumber n :=
            ContinuousLinearMap.approximationNumber_comp_le_norm_mul _ _ n
        _ ≤ 1 * (V.subtypeL ∘L T).approximationNumber n := by
            gcongr <;>
              first
                | exact norm_adjoint_subtypeL_le_one V
                | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
        _ = (V.subtypeL ∘L T).approximationNumber n := one_mul _
  exact key

/-- Ambient extension of a rectangular subspace block preserves the complete
singular-value sequence. -/
theorem sameApproximationSingularValues_ambientSubspaceBlock
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : U →L[𝕜] V) :
    SameApproximationSingularSequence
      (V.subtypeL ∘L T ∘L U.subtypeL.adjoint) T :=
  (sameApproximationSingularValues_includeCodomain V
    (T ∘L U.subtypeL.adjoint)).trans
      (sameApproximationSingularValues_extendDomainByZero U T)

end

end ExactSinTheta
end DavisKahan
end TauCeti