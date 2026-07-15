/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.DoubleAngle.SinTheta
import DavisKahan.FiniteDimensional.Residual.Ritz
import DavisKahan.Experimental.FiniteDimensional.Residual.AngleEmbeddings

/-!
# Residual `sin (2Θ)` theorem

The proof eliminates the represented operator from the two projected residual
equations.  This produces a separated Sylvester equation for the double-angle
sine block.  The internal gap supplies the inverse bound and Fan dominance
passes the resulting singular-value inequalities to every rectangular UI norm.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Residual form of the `sin 2Θ` theorem for an isometric trial map. -/
theorem sinTwoTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
  classical
  let C := cosThetaEmbedding U X
  let S := sinThetaEmbedding U X
  let R := residual A X M
  have hblocks := projectedResidualEquations hA hM hU X
  have hdouble :
      doubleAngleSylvesterOperator A U (sinTwoThetaEmbedding U X) =
        (2 : 𝕜) •
          (complementaryProjection U ∘ₗ R ∘ₗ LinearMap.adjoint C -
            projection U ∘ₗ R ∘ₗ LinearMap.adjoint S) := by
    ext x
    simp [sinTwoThetaEmbedding, C, S, R, hblocks.1, hblocks.2,
      LinearMap.comp_apply, LinearMap.adjoint_comp]
    module
  have hrhs :
      N ((2 : 𝕜) •
          (complementaryProjection U ∘ₗ R ∘ₗ LinearMap.adjoint C -
            projection U ∘ₗ R ∘ₗ LinearMap.adjoint S)) ≤
        2 * N R := by
    rw [N.smul]
    have hC : ‖C.toContinuousLinearMap‖ ≤ 1 := cosThetaEmbedding_contraction U X
    have hS : ‖S.toContinuousLinearMap‖ ≤ 1 := sinThetaEmbedding_contraction U X
    exact doubleAngleResidual_rhs_uiNorm_le N R hC hS
  have hsolve := internalGap_doubleAngleSylvester_uiNorm_le
    N hA hU hδ hgap (sinTwoThetaEmbedding U X) hdouble
  exact (mul_le_mul_of_nonneg_left hsolve (le_of_lt hδ)).trans hrhs

end DavisKahanTheory
end ForMathlib
