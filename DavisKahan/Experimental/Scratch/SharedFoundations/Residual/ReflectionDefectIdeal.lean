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

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- A trial residual in a rectangular symmetric ideal forces the associated
reflection defect into the square member of the same family. -/
theorem RectangularSymmetricIdealFamily.reflectionDefect_isometricRange_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (A : H →L[ℂ] H) (X : F →L[ℂ] H) (M : F →L[ℂ] F)
    (hX : IsometricEmbedding X) (hR : N.Mem (residual A X M)) :
    letI := rangeHasOrthogonalProjection X hX
    let V : Submodule ℂ H := LinearMap.range X.toLinearMap
    N.Mem (reflectionDefect V A) := by
  letI := rangeHasOrthogonalProjection X hX
  let V : Submodule ℂ H := LinearMap.range X.toLinearMap
  let T : H →L[ℂ] H := Vᗮ.starProjection ∘L A ∘L V.starProjection
  have hT : N.Mem T := by
    simpa [T, isometricRangeCrossBlock] using
      N.isometricRangeCrossBlock_mem A X M hX hR
  have hTa : N.Mem T.adjoint := N.adjoint_mem hT
  have hoff : V.starProjection ∘L A.adjoint ∘L Vᗮ.starProjection = T.adjoint := by
    simp [T, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
  rw [reflectionDefect_eq_neg_two_smul_offdiag]
  apply N.smul_mem
  apply N.add_mem hT
  rw [← hoff]
  exact hTa

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
  let T : H →L[ℂ] H := Vᗮ.starProjection ∘L A ∘L V.starProjection
  have hT : N.Mem T := by
    simpa [T, isometricRangeCrossBlock] using
      N.isometricRangeCrossBlock_mem A X M hX hR
  have hTa : N.Mem T.adjoint := N.adjoint_mem hT
  have hTg : N.gauge T ≤ N.gauge (residual A X M) := by
    simpa [T, isometricRangeCrossBlock] using
      N.gauge_isometricRangeCrossBlock_le A X M hX hR
  have hblock : V.starProjection ∘L A ∘L Vᗮ.starProjection = T.adjoint := by
    rw [← offdiag_adjoint V hA]
    rfl
  rw [reflectionDefect_eq_neg_two_smul_offdiag, hblock, N.gauge_smul]
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
