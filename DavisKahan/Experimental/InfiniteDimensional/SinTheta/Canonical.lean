/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.GenuineIntervalExterior
import DavisKahan.SinTheta.Unbounded.LegacyGap

/-!
# Canonical Davis--Kahan 1970 single-angle targets

This module owns the source-facing theorem shapes while the analytic
implementations remain experimental.

There are two generalized endpoints:

* `FiniteIntervalGeneralSinThetaProblem` is the completed finite
  interval/exterior theorem.  Its spectral assumptions use the genuine
  `Spectra` spectrum and its proof goes through the clean mixed
  bounded--unbounded Sylvester engine.
* `GeneralSinThetaProblem` retains the historical complete 1970 statement,
  including the two ordered half-line orientations.  Its clean complex proof
  is supplied by `SinTheta.LegacyGapCompletion`, above the foundational import
  cone.

The generalized lower-frame package in this module is complex.  The explicit
polar-data algebra is scalar-generic, and `RealCanonical` supplies the real
selection and source-shaped problem.  The isometric input package remains
generic over `RCLike`.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

section ComplexGeneralized

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Complete input package for the generalized Davis--Kahan 1970 sine theorem.

`data.A` is the ambient self-adjoint closed operator, `data.A₀` is the trial
block, and `data.Λ₁` is the complementary exact block.  The residual is bounded
on the ambient Hilbert spaces even when the diagonal operators are unbounded.
The lower frame bound permits a non-isometric trial map. -/
structure GeneralSinThetaProblem
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ)) where
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  exactMap : H →L[ℂ] E
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

/-- The complete generalized source target. -/
theorem result
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (P : GeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.toRectangularSymmetricIdealFamily.Mem
        (directedSinThetaOperator P.data.X P.exactMap
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.toRectangularSymmetricIdealFamily.gauge
            (directedSinThetaOperator P.data.X P.exactMap
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.toRectangularSymmetricIdealFamily.gauge P.data.residual :=
  generalizedSinTheta_unbounded_exact_complex
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.exact_decomposition P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

/-- The raw complementary-block form used before the final angle
identification. -/
theorem complementaryBlock_result
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (P : GeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.toRectangularSymmetricIdealFamily.Mem
        (sinThetaBlock P.data.X P.data.F₁
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.toRectangularSymmetricIdealFamily.gauge
            (sinThetaBlock P.data.X P.data.F₁
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.toRectangularSymmetricIdealFamily.gauge P.data.residual :=
  generalizedSinTheta_unbounded_complex
    N P.data P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.exact_decomposition.isometry₁ P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

end GeneralSinThetaProblem

/-- Complete source-shaped package for the proved finite interval/exterior
branch.  Unlike `GeneralSinThetaProblem.spectral_gap`, this uses the genuine
`Spectra` spectrum and does not pass through the ordered half-line engine. -/
structure FiniteIntervalGeneralSinThetaProblem
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ)) where
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  exactMap : H →L[ℂ] E
  ambient_selfAdjoint : data.A.IsSelfAdjoint
  trial_selfAdjoint : data.A₀.IsSelfAdjoint
  complement_selfAdjoint : data.Λ₁.IsSelfAdjoint
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  intervalLower : ℝ
  intervalUpper : ℝ
  gap : ℝ
  frameLowerBound : ℝ
  interval_order : intervalLower ≤ intervalUpper
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_gap : GenuineUnboundedIntervalExteriorGap data.A₀ data.Λ₁
    intervalLower intervalUpper gap
  residual_mem : N.toRectangularSymmetricIdealFamily.Mem data.residual

namespace FiniteIntervalGeneralSinThetaProblem

/-- Completed generalized finite interval/exterior theorem with the exact
source-facing directed sine operator. -/
theorem result
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (P : FiniteIntervalGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.toRectangularSymmetricIdealFamily.Mem
        (directedSinThetaOperator P.data.X P.exactMap
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.toRectangularSymmetricIdealFamily.gauge
            (directedSinThetaOperator P.data.X P.exactMap
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.toRectangularSymmetricIdealFamily.gauge P.data.residual :=
  generalizedSinTheta_unbounded_exact_of_genuineIntervalExteriorGap
    N.toRectangularSymmetricIdealFamily P.data P.exactMap
      P.ambient_selfAdjoint P.trial_selfAdjoint P.complement_selfAdjoint
      P.exact_decomposition P.interval_order P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

/-- Complementary-overlap form of the completed finite interval/exterior
branch. -/
theorem complementaryBlock_result
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (P : FiniteIntervalGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.toRectangularSymmetricIdealFamily.Mem
        (sinThetaBlock P.data.X P.data.F₁
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.toRectangularSymmetricIdealFamily.gauge
            (sinThetaBlock P.data.X P.data.F₁
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.toRectangularSymmetricIdealFamily.gauge P.data.residual :=
  generalizedSinTheta_unbounded_of_genuineIntervalExteriorGap
    N.toRectangularSymmetricIdealFamily P.data
      P.ambient_selfAdjoint P.trial_selfAdjoint P.complement_selfAdjoint
      P.exact_decomposition.isometry₁ P.interval_order P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

end FiniteIntervalGeneralSinThetaProblem

end ComplexGeneralized

section GenericIsometric

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

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

/-- Scalar-generic historical isometric theorem shape.  The manuscript
surface selects the direct complex proof, while `RealCanonical` supplies the
parallel real proof. -/
theorem result
    [HasApproximationNumberStrongCutoff.{u, v, 0} 𝕜]
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
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

end IsometricSinThetaProblem

end GenericIsometric

section ComplexIsometricBridge

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsometricSinThetaProblem

/-- Complex specialization of the source-shaped isometric problem, routed
through the direct manuscript gap engine. -/
theorem result_complex
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (P : IsometricSinThetaProblem (𝕜 := ℂ) (E := E) (F := F)
      (G := G) (H := H) N) :
    N.toRectangularSymmetricIdealFamily.Mem
        ((ContinuousLinearMap.id ℂ E -
          P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X) ∧
      P.gap * N.toRectangularSymmetricIdealFamily.gauge
          ((ContinuousLinearMap.id ℂ E -
            P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X)
        ≤ N.toRectangularSymmetricIdealFamily.gauge P.data.residual :=
  sinTheta_unbounded_exact_complex
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.trial_isometry P.exact_decomposition
      P.gap_pos P.spectral_gap P.residual_mem

/-- Package a complex isometric problem as the generalized theorem with lower
frame bound one. -/
noncomputable def toGeneral
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    (P : IsometricSinThetaProblem (𝕜 := ℂ) (E := E) (F := F)
      (G := G) (H := H) N) :
    GeneralSinThetaProblem (E := E) (F := F)
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

end ComplexIsometricBridge

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
