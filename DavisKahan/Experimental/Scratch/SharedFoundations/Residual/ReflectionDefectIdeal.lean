/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.Scratch.SharedFoundations.Residual.TrialResidual
import DavisKahan.Experimental.InfiniteDimensional.DoubleAngleGenuine

/-!
# Ideal-gauge residual control for reflection defects

The elementary rectangular-ideal axioms give a robust factor-four estimate.
Obtaining the sharp factor two for arbitrary symmetric gauges requires an
additional off-diagonal block theorem and should not be hidden in the basic
ideal interface.
-/

namespace ForMathlib
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

/-- A trial residual in a rectangular symmetric ideal forces the associated
reflection defect into the square member of the same family. -/
theorem RectangularSymmetricIdealFamily.reflectionDefect_isometricRange_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) (hR : N.Mem (residual A X M)) :
    letI := rangeHasOrthogonalProjection X hX
    let V : Submodule ℂ H := LinearMap.range X.toLinearMap
    N.Mem (reflectionDefect V A) := by
  letI := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  change N.Mem (reflectionDefect V A)
  let T : H →L[ℂ] H := Vᗮ.starProjection ∘L A ∘L V.starProjection
  have hT : N.Mem T := by
    simpa [T, isometricRangeCrossBlock] using
      RectangularSymmetricIdealFamily.isometricRangeCrossBlock_mem
        N A X M hX hR
  have hTa : N.Mem T.adjoint := N.adjoint_mem hT
  have hblock : V.starProjection ∘L A ∘L Vᗮ.starProjection = T.adjoint := by
    change V.starProjection ∘L A ∘L Vᗮ.starProjection =
      (Vᗮ.starProjection ∘L A ∘L V.starProjection).adjoint
    exact (offdiag_adjoint V hA).symm
  rw [reflectionDefect_eq_neg_two_smul_offdiag, hblock]
  exact N.smul_mem (-2 : ℂ) (N.add_mem hT hTa)

/-- The basic rectangular ideal axioms yield a factor-four reflection-defect
bound through the trial residual. -/
theorem RectangularSymmetricIdealFamily.gauge_reflectionDefect_isometricRange_le_four_mul
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) (hR : N.Mem (residual A X M)) :
    letI := rangeHasOrthogonalProjection X hX
    let V : Submodule ℂ H := LinearMap.range X.toLinearMap
    N.gauge (reflectionDefect V A) ≤ 4 * N.gauge (residual A X M) := by
  letI := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  change N.gauge (reflectionDefect V A) ≤
    4 * N.gauge (residual A X M)
  let T : H →L[ℂ] H := Vᗮ.starProjection ∘L A ∘L V.starProjection
  have hT : N.Mem T := by
    simpa [T, isometricRangeCrossBlock] using
      RectangularSymmetricIdealFamily.isometricRangeCrossBlock_mem
        N A X M hX hR
  have hTa : N.Mem T.adjoint := N.adjoint_mem hT
  have hTg : N.gauge T ≤ N.gauge (residual A X M) := by
    simpa [T, isometricRangeCrossBlock] using
      RectangularSymmetricIdealFamily.gauge_isometricRangeCrossBlock_le
        N A X M hX hR
  have hblock : V.starProjection ∘L A ∘L Vᗮ.starProjection = T.adjoint := by
    change V.starProjection ∘L A ∘L Vᗮ.starProjection =
      (Vᗮ.starProjection ∘L A ∘L V.starProjection).adjoint
    exact (offdiag_adjoint V hA).symm
  rw [reflectionDefect_eq_neg_two_smul_offdiag, hblock,
    N.gauge_smul (-2 : ℂ) (N.add_mem hT hTa)]
  have hadd := N.gauge_add_le hT hTa
  have hadj := N.gauge_adjoint hT
  calc
    ‖(-2 : ℂ)‖ * N.gauge (T + T.adjoint)
        ≤ 2 * (N.gauge T + N.gauge T.adjoint) := by
          norm_num
          gcongr
    _ = 4 * N.gauge T := by rw [hadj]; ring
    _ ≤ 4 * N.gauge (residual A X M) := by gcongr

end SharedFoundations
end Scratch
end Experimental
end DavisKahan
end ForMathlib
