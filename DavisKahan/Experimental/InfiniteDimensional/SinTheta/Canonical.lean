/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Unbounded

/-!
# Canonical Davis--Kahan 1970 single-angle target

This module owns the source-facing theorem shape while the analytic dependencies
remain experimental.  The root theorem is the generalized, domain-aware result
for self-adjoint closed operators that may be unbounded.  The isometric theorem
is a specialization.  Shared bounded-map geometry is reused, but the bounded
and finite-dimensional theorem endpoints are not logical parents of these
declarations.

The theorem is bundled as a problem structure so that compiler errors expose
which source assumption is missing instead of producing a long anonymous list
of arguments.  Promotion to the supported tree should preserve the theorem
shape even if the internal closed-operator representation changes.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Complete input package for the generalized Davis--Kahan 1970 sine theorem.

`data.A` is the ambient self-adjoint closed operator, `data.A₀` is the trial
block, and `data.Λ₁` is the complementary exact block.  The residual is bounded
on the ambient Hilbert spaces even when the diagonal operators are unbounded.
The lower frame bound permits a non-isometric trial map. -/
structure GeneralSinThetaProblem
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜)) where
  data : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G)
  exactMap : H →L[𝕜] E
  ambient_selfAdjoint : data.A.IsSelfAdjoint
  trial_selfAdjoint : data.A₀.IsSelfAdjoint
  complement_selfAdjoint : data.Λ₁.IsSelfAdjoint
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  gap : ℝ
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_gap : UnboundedSylvesterGap data.A₀ data.Λ₁ gap
  residual_mem : N.toRectangularSymmetricIdealFamily.Mem data.residual

namespace GeneralSinThetaProblem

/-- The canonical generalized source theorem. -/
theorem result
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (P : GeneralSinThetaProblem (𝕜 := 𝕜) (E := E) (F := F)
      (G := G) (H := H) N) :
    N.toRectangularSymmetricIdealFamily.Mem
        (directedSinThetaOperator P.data.X P.exactMap
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.toRectangularSymmetricIdealFamily.gauge
            (directedSinThetaOperator P.data.X P.exactMap
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.toRectangularSymmetricIdealFamily.gauge P.data.residual :=
  generalizedSinTheta_unbounded_exact
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.exact_decomposition P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

/-- The raw complementary-block form used before the final angle
identification. -/
theorem complementaryBlock_result
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (P : GeneralSinThetaProblem (𝕜 := 𝕜) (E := E) (F := F)
      (G := G) (H := H) N) :
    N.toRectangularSymmetricIdealFamily.Mem
        (sinThetaBlock P.data.X P.data.F₁
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.toRectangularSymmetricIdealFamily.gauge
            (sinThetaBlock P.data.X P.data.F₁
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.toRectangularSymmetricIdealFamily.gauge P.data.residual :=
  generalizedSinTheta_unbounded
    N P.data P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.exact_decomposition.isometry₁ P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

end GeneralSinThetaProblem

/-- Complete input package for the isometric specialization. -/
structure IsometricSinThetaProblem
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜)) where
  data : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G)
  exactMap : H →L[𝕜] E
  ambient_selfAdjoint : data.A.IsSelfAdjoint
  trial_selfAdjoint : data.A₀.IsSelfAdjoint
  complement_selfAdjoint : data.Λ₁.IsSelfAdjoint
  trial_isometry : IsometricEmbedding data.X
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  gap : ℝ
  gap_pos : 0 < gap
  spectral_gap : UnboundedSylvesterGap data.A₀ data.Λ₁ gap
  residual_mem : N.toRectangularSymmetricIdealFamily.Mem data.residual

namespace IsometricSinThetaProblem

/-- The source isometric theorem, derived from the generalized architecture. -/
theorem result
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (P : IsometricSinThetaProblem (𝕜 := 𝕜) (E := E) (F := F)
      (G := G) (H := H) N) :
    N.toRectangularSymmetricIdealFamily.Mem
        ((ContinuousLinearMap.id 𝕜 E -
          P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X) ∧
      P.gap * N.toRectangularSymmetricIdealFamily.gauge
          ((ContinuousLinearMap.id 𝕜 E -
            P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X)
        ≤ N.toRectangularSymmetricIdealFamily.gauge P.data.residual :=
  sinTheta_unbounded_exact
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.trial_isometry P.exact_decomposition
      P.gap_pos P.spectral_gap P.residual_mem

/-- The isometric theorem packaged as the generalized theorem with lower bound
one. -/
noncomputable def toGeneral
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (P : IsometricSinThetaProblem (𝕜 := 𝕜) (E := E) (F := F)
      (G := G) (H := H) N) :
    GeneralSinThetaProblem (𝕜 := 𝕜) (E := E) (F := F)
      (G := G) (H := H) N where
  data := P.data
  exactMap := P.exactMap
  ambient_selfAdjoint := P.ambient_selfAdjoint
  trial_selfAdjoint := P.trial_selfAdjoint
  complement_selfAdjoint := P.complement_selfAdjoint
  exact_decomposition := P.exact_decomposition
  gap := P.gap
  frameLowerBound := 1
  gap_pos := P.gap_pos
  frameLowerBound_pos := zero_lt_one
  lowerFrame := lowerFrameBound_one_of_isometry P.trial_isometry
  spectral_gap := P.spectral_gap
  residual_mem := P.residual_mem

end IsometricSinThetaProblem

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
