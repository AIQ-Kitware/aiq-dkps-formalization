/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.BoundedOperator.IsometricRangeProjection
import DavisKahan.Sylvester.GenuineSpectrum
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily

/-!
# Trial residual and exact-range cross blocks

This file isolates the algebra shared by generalized tangent estimates,
reflection-defect residual estimates, and Ritz-pair perturbation theory.
For an isometric trial map `X`, the orthogonal projection onto its range is
`X X*`; consequently the ambient off-diagonal block factors through the trial
residual and `X*`.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace SharedFoundations

open scoped InnerProductSpace
open ExactSinTheta
open DavisKahanExt

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The canonical residual of a closed trial subspace, viewed as a map from
that subspace into the ambient Hilbert space. -/
noncomputable def trialResidualCore
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] : Z →L[ℂ] H :=
  Zᗮ.starProjection ∘L T ∘L Z.subtypeL

/-- The trial residual is the difference between the ambient action and the
lifted Ritz compression. -/
theorem trialResidualCore_eq_ritzDifference
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] [CompleteSpace Z] :
    trialResidualCore T Z =
      T ∘L Z.subtypeL - Z.subtypeL ∘L compressOperator Z T := by
  apply ContinuousLinearMap.ext
  intro z
  change Zᗮ.starProjection (T (z : H)) =
    T (z : H) - (Z.subtypeL (Z.orthogonalProjectionOnto (T (z : H))))
  rw [Submodule.starProjection_orthogonal_apply]
  rfl

/-- Every trial residual vector lies in the orthogonal complement of the trial
space. -/
theorem trialResidualCore_apply_mem_orthogonal
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] (z : Z) :
    trialResidualCore T Z z ∈ Zᗮ := by
  exact Zᗮ.starProjection_apply_mem _

/-- Ambient projection onto the range of an isometric trial map. -/
noncomputable def isometricRangeProjection
    (X : F →L[ℂ] H) (hX : IsometricEmbedding X) : H →L[ℂ] H := by
  letI := rangeHasOrthogonalProjection X hX
  exact (LinearMap.range X.toLinearMap).starProjection

/-- The ambient complementary cross block of `A` relative to the range of an
isometric trial map. -/
noncomputable def isometricRangeCrossBlock
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (hX : IsometricEmbedding X) :
    H →L[ℂ] H := by
  letI := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  exact Vᗮ.starProjection ∘L A ∘L V.starProjection

/-- The range projection has the expected explicit factorization. -/
theorem isometricRangeProjection_eq_comp_adjoint
    (X : F →L[ℂ] H) (hX : IsometricEmbedding X) :
    isometricRangeProjection X hX = X ∘L X.adjoint := by
  unfold isometricRangeProjection
  letI := rangeHasOrthogonalProjection X hX
  exact starProjection_range_eq_comp_adjoint X hX

/-- The cross block factors exactly through any residual `A X - X M`.
The term involving `M` disappears because the complementary range projection
annihilates `X`. -/
theorem isometricRangeCrossBlock_eq_projectedResidual_comp_adjoint
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) :
    isometricRangeCrossBlock A X hX =
      ((by
        letI := rangeHasOrthogonalProjection X hX
        let V : Submodule ℂ H := LinearMap.range X.toLinearMap
        exact Vᗮ.starProjection ∘L residual A X M) : F →L[ℂ] H) ∘L X.adjoint := by
  letI := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  have hP : V.starProjection = X ∘L X.adjoint :=
    starProjection_range_eq_comp_adjoint X hX
  have hQX : Vᗮ.starProjection ∘L X = 0 :=
    complementaryProjection_range_comp_isometry X hX
  unfold isometricRangeCrossBlock
  dsimp only
  rw [hP, ← ContinuousLinearMap.comp_assoc]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply, residual, sub_apply]
  have hzero : Vᗮ.starProjection (X (M (X.adjoint y))) = 0 := by
    have h := congrArg (fun L : F →L[ℂ] H => L (M (X.adjoint y))) hQX
    simpa using h
  rw [map_sub, hzero, sub_zero]

/-- The exact-range cross block is bounded by the residual norm. -/
theorem norm_isometricRangeCrossBlock_le_residual
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) :
    ‖isometricRangeCrossBlock A X hX‖ ≤ ‖residual A X M‖ := by
  letI := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  rw [isometricRangeCrossBlock_eq_projectedResidual_comp_adjoint A X M hX]
  calc
    ‖(Vᗮ.starProjection ∘L residual A X M) ∘L X.adjoint‖
        ≤ ‖Vᗮ.starProjection‖ * ‖residual A X M‖ * ‖X.adjoint‖ := by
      calc
        ‖(Vᗮ.starProjection ∘L residual A X M) ∘L X.adjoint‖
            ≤ ‖Vᗮ.starProjection ∘L residual A X M‖ * ‖X.adjoint‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖Vᗮ.starProjection‖ * ‖residual A X M‖) * ‖X.adjoint‖ := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖residual A X M‖ * 1 := by
      gcongr
      · exact Vᗮ.starProjection_norm_le
      · exact (isometry_and_adjoint_norm_le_one X hX).2
    _ = ‖residual A X M‖ := by ring

/-- Rectangular ideal membership of a residual implies membership of the exact
range cross block. -/
theorem RectangularSymmetricIdealFamily.isometricRangeCrossBlock_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) (hR : N.Mem (residual A X M)) :
    N.Mem (isometricRangeCrossBlock A X hX) := by
  letI := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  rw [isometricRangeCrossBlock_eq_projectedResidual_comp_adjoint A X M hX]
  exact N.comp_mem Vᗮ.starProjection X.adjoint hR

/-- Rectangular ideal gauge of the exact-range cross block is bounded by the
trial residual gauge. -/
theorem RectangularSymmetricIdealFamily.gauge_isometricRangeCrossBlock_le
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) (hR : N.Mem (residual A X M)) :
    N.gauge (isometricRangeCrossBlock A X hX) ≤
      N.gauge (residual A X M) := by
  letI := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  rw [isometricRangeCrossBlock_eq_projectedResidual_comp_adjoint A X M hX]
  exact N.gauge_comp_le_of_contractions Vᗮ.starProjection X.adjoint hR
    Vᗮ.starProjection_norm_le (isometry_and_adjoint_norm_le_one X hX).2

end SharedFoundations
end Scratch
end Experimental
end DavisKahan
end TauCeti