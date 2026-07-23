/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSelectedReduction

/-!
# Audited bounded spectral selections

A spectral subspace cannot be defined from an arbitrary bounded operator and
an arbitrary set alone.  The reusable data must retain self-adjointness and
measurability.  This record packages the genuine PVM range, its projection,
and its reduction property for downstream sine, tangent, continuation, and
Riesz-projection campaigns.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace SharedFoundations

open scoped InnerProductSpace
open DavisKahanExt

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A certified measurable spectral selection for a bounded self-adjoint
operator. -/
structure BoundedSpectralSelection (A : H →L[ℂ] H) where
  carrier : Set ℝ
  measurable_carrier : MeasurableSet carrier
  selfAdjoint : IsSelfAdjointOperator A
  subspace : Submodule ℂ H
  projection : H →L[ℂ] H
  subspace_eq : subspace = boundedSelfAdjointSpectralSubspace A selfAdjoint
    carrier measurable_carrier
  projection_eq : projection = boundedSelfAdjointSpectralProjection A selfAdjoint
    carrier measurable_carrier
  reduces : Reduces A subspace

/-- Canonical PVM selection. -/
noncomputable def BoundedSpectralSelection.canonical
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) : BoundedSpectralSelection A where
  carrier := s
  measurable_carrier := hs
  selfAdjoint := hA
  subspace := boundedSelfAdjointSpectralSubspace A hA s hs
  projection := boundedSelfAdjointSpectralProjection A hA s hs
  subspace_eq := rfl
  projection_eq := rfl
  reduces := boundedSelfAdjointSpectralSubspace_reduces A hA s hs

namespace BoundedSpectralSelection

/-- A certified selection carries the canonical orthogonal projection. -/
noncomputable instance hasOrthogonalProjection
    {A : H →L[ℂ] H} (S : BoundedSpectralSelection A) :
    S.subspace.HasOrthogonalProjection := by
  rw [S.subspace_eq]
  infer_instance

/-- The stored projection is the star projection onto the stored subspace. -/
theorem projection_eq_starProjection
    {A : H →L[ℂ] H} (S : BoundedSpectralSelection A) :
    S.projection = S.subspace.starProjection := by
  rw [S.projection_eq, S.subspace_eq]
  exact boundedSelfAdjointSpectralProjection_eq_starProjection
    A S.selfAdjoint S.carrier S.measurable_carrier

/-- The stored projection commutes with the operator. -/
theorem projection_comp_comm
    {A : H →L[ℂ] H} (S : BoundedSpectralSelection A) :
    S.projection ∘L A = A ∘L S.projection := by
  apply ContinuousLinearMap.ext
  intro x
  rw [S.projection_eq]
  exact boundedSelfAdjointSpectralProjection_apply_comm
    A S.selfAdjoint S.carrier S.measurable_carrier x

/-- The selected complement also reduces the operator. -/
theorem orthogonal_reduces
    {A : H →L[ℂ] H} (S : BoundedSpectralSelection A) :
    Reduces A S.subspaceᗮ := S.reduces.orthogonalComplement

end BoundedSpectralSelection

end SharedFoundations
end Scratch
end Experimental
end DavisKahan
end ForMathlib
