/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.Scratch.SharedFoundations.Residual.TrialResidual

/-!
# Isometric Ritz pairs

For an isometric trial embedding, choosing the compressed operator
`M = X* A X` makes the residual orthogonal to the trial range.  These identities
are shared by generalized tangent estimates, Galerkin/Ritz theory, and
finite-rank approximation arguments.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace SharedFoundations

open scoped InnerProductSpace
open DavisKahanExt

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Certified isometric Ritz data. -/
structure IsometricRitzPair (A : H →L[ℂ] H) where
  X : F →L[ℂ] H
  M : F →L[ℂ] F
  isometric : IsometricEmbedding X
  compression_eq : M = X.adjoint ∘L A ∘L X

namespace IsometricRitzPair

/-- The Ritz compression of a self-adjoint operator is self-adjoint. -/
theorem compression_isSelfAdjoint
    {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (P : IsometricRitzPair (F := F) A) : IsSelfAdjoint P.M := by
  rw [P.compression_eq, ContinuousLinearMap.isSelfAdjoint_iff',
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hA.adjoint_eq,
    ContinuousLinearMap.comp_assoc]

/-- The residual is orthogonal to the trial coordinates. -/
theorem adjoint_comp_residual_eq_zero
    {A : H →L[ℂ] H} (P : IsometricRitzPair (F := F) A) :
    P.X.adjoint ∘L residual A P.X P.M = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hM := congrArg (fun T : F →L[ℂ] F => T x) P.compression_eq
  simp only [residual, ContinuousLinearMap.comp_apply, sub_apply,
    map_sub, zero_apply]
  rw [adjoint_apply_isometry_apply P.X P.isometric]
  apply sub_eq_zero.mpr
  simpa only [ContinuousLinearMap.comp_apply] using hM.symm

/-- The range projection annihilates the Ritz residual. -/
theorem rangeProjection_comp_residual_eq_zero
    {A : H →L[ℂ] H} (P : IsometricRitzPair (F := F) A) :
    letI := rangeHasOrthogonalProjection P.X P.isometric
    let V : Submodule ℂ H := LinearMap.range P.X.toLinearMap
    V.starProjection ∘L residual A P.X P.M = 0 := by
  letI := rangeHasOrthogonalProjection P.X P.isometric
  change (LinearMap.range P.X.toLinearMap).starProjection ∘L
    residual A P.X P.M = 0
  rw [starProjection_range_eq_comp_adjoint P.X P.isometric,
    ContinuousLinearMap.comp_assoc, P.adjoint_comp_residual_eq_zero,
    ContinuousLinearMap.comp_zero]

/-- The residual is exactly its complementary-range projection. -/
theorem complementaryProjection_comp_residual_eq
    {A : H →L[ℂ] H} (P : IsometricRitzPair (F := F) A) :
    letI := rangeHasOrthogonalProjection P.X P.isometric
    let V : Submodule ℂ H := LinearMap.range P.X.toLinearMap
    Vᗮ.starProjection ∘L residual A P.X P.M = residual A P.X P.M := by
  letI := rangeHasOrthogonalProjection P.X P.isometric
  change (LinearMap.range P.X.toLinearMap)ᗮ.starProjection ∘L
    residual A P.X P.M = residual A P.X P.M
  rw [Submodule.starProjection_orthogonal', ContinuousLinearMap.sub_comp,
    P.rangeProjection_comp_residual_eq_zero, sub_zero]
  change ContinuousLinearMap.id ℂ H ∘L residual A P.X P.M =
    residual A P.X P.M
  rw [ContinuousLinearMap.id_comp]

/-- The ambient cross block factors through the Ritz residual with no extra
projection on the residual side. -/
theorem crossBlock_eq_residual_comp_adjoint
    {A : H →L[ℂ] H} (P : IsometricRitzPair (F := F) A) :
    isometricRangeCrossBlock A P.X P.isometric =
      residual A P.X P.M ∘L P.X.adjoint := by
  rw [isometricRangeCrossBlock_eq_projectedResidual_comp_adjoint
    A P.X P.M P.isometric]
  letI := rangeHasOrthogonalProjection P.X P.isometric
  let V : Submodule ℂ H := LinearMap.range P.X.toLinearMap
  rw [P.complementaryProjection_comp_residual_eq]

end IsometricRitzPair

end SharedFoundations
end Scratch
end Experimental
end DavisKahan
end TauCeti