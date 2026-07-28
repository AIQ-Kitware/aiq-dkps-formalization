/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.DavisKahan.SharpIdeal
import DavisKahan.Sources.DavisKahan1970.RemainingSourceSurface
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalRiccati

/-!
# Sharp unbounded spectral-subspace `tan 2 Theta`

This file states the final source-strength endpoint.  The existing unbounded
wrapper obtains tangent by dividing the `sin 2 Theta` block by the extended
cosine and therefore carries an extra denominator.  Here the selected
quarter-acute spectral subspace is put directly into contractive graph
coordinates and the sharp Riccati theorem is applied to its canonical
`Tan2(X)` operator.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

open scoped InnerProductSpace ENNReal
open Set
open DavisKahanExt
open Experimental.ExactSinTheta
open Experimental.SpectraBridge

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]


/-- Canonical double-angle tangent of a quarter-acute graph coordinate. -/
noncomputable def quarterAcuteDoubleAngleTangent
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    U →L[ℂ] Uᗮ :=
  TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator
    (quarterAcuteAngularCoordinate U V hquarter)
    (norm_quarterAcuteAngularCoordinate_lt_one U V hquarter)

/-- **Sharp unbounded `tan 2 Theta` theorem for every standard symmetric
ideal.**

The conclusion is formulated for the canonical graph-coordinate tangent
operator.  A separate unitary-compression identification transfers it to the
paper's ambient reflected-overlap block. -/
theorem sharp_unbounded_offDiagonal_standardIdeal
    (N : TauCeti.FinishTanTwoTheta.StandardSymmetricIdealFamily.{0, v} ℂ)
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {beta alpha delta : ℝ} (hba : beta ≤ alpha) (hdelta : 0 < delta)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) beta)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) alpha)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (beta - delta) (alpha + delta),
      lam ∉ Spectra.Resolvent.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hEmem : E ∈ N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.carrier)
    (hoff : IsOffDiagonal (selfAdjointSpectralSubspace A hA B hB) E)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    let U := selfAdjointSpectralSubspace A hA B hB
    let V := selfAdjointSpectralSubspace (A.addBounded E)
      (addBounded_isSelfAdjoint A hA E hE) S hS
    quarterAcuteDoubleAngleTangent U V hquarter ∈
        N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.carrier ∧
      delta *
        (N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge
          (quarterAcuteDoubleAngleTangent U V hquarter)).toReal ≤
        2 *
          (N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge E).toReal := by
  /-
  Proof architecture:

  1. Let `U` and `V` be the two genuine spectral subspaces and let `X` be the
     unique contractive coordinate graph supplied by quarter-acuteness.
  2. Use the current spectral-restriction bridge to show that `V` reduces
     `A+E`, hence `X` solves the bounded Riccati equation for the shifted
     diagonal restrictions.
  3. Shift by `beta` so the `U` diagonal form is `<=0`; the spectral exclusion
     and the lower restriction bound put the complementary diagonal form
     above `delta`.
  4. Off-diagonality identifies the coupling block with
     `P_U E |_(U^perp)`.
  5. The operator-ideal composition law gives membership of this block and
     gauge at most the gauge of `E`.
  6. Apply `sharp_standardIdeal_toReal` to the block Riccati data.

  No division by the double-angle cosine occurs, so the denominator from the
  previous unbounded wrapper disappears.
  -/
  sorry

/-- The graph-coordinate tangent is unitarily equivalent to the source-facing
ambient tangent block on the active subspaces.  Consequently every symmetric
ideal gauge agrees on the two operators. -/
theorem graphTangent_gauge_eq_sourceBlock
    (N : TauCeti.FinishTanTwoTheta.StandardSymmetricIdealFamily.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) :
    N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge
        (quarterAcuteDoubleAngleTangent U V hquarter) =
      N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge
        (tanTwoThetaIdealBlock U V hquarter) := by
  /-
  Construct the canonical isometric identifications of the source and target
  coordinate spaces with the active off-diagonal ambient blocks.  The two
  operators differ by left and right unitary maps; apply the ideal law in both
  directions.  This is geometric bookkeeping, not a new perturbation bound.
  -/
  sorry

/-- Source-facing sharp endpoint without the former cosine denominator. -/
theorem sharp_unbounded_offDiagonal_sourceBlock_standardIdeal
    (N : TauCeti.FinishTanTwoTheta.StandardSymmetricIdealFamily.{0, v} ℂ)
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {beta alpha delta : ℝ} (hba : beta ≤ alpha) (hdelta : 0 < delta)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) beta)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) alpha)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (beta - delta) (alpha + delta),
      lam ∉ Spectra.Resolvent.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hEmem : E ∈ N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.carrier)
    (hoff : IsOffDiagonal (selfAdjointSpectralSubspace A hA B hB) E)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    tanTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (A.addBounded E)
        (addBounded_isSelfAdjoint A hA E hE) S hS) hquarter ∈
        N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.carrier ∧
      delta *
        (N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge
          (tanTwoThetaIdealBlock
            (selfAdjointSpectralSubspace A hA B hB)
            (selfAdjointSpectralSubspace (A.addBounded E)
              (addBounded_isSelfAdjoint A hA E hE) S hS) hquarter)).toReal ≤
        2 *
          (N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge E).toReal := by
  /- Combine `sharp_unbounded_offDiagonal_standardIdeal` with
  `graphTangent_gauge_eq_sourceBlock`, transporting membership as well as the
  gauge equality through the unitary equivalence. -/
  sorry

end FinishTanTwoTheta
end DavisKahan
end TauCeti
