/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.DoubleAngle.SinTheta
import DavisKahan.FiniteDimensional.Residual.Ritz
import DavisKahan.Experimental.FiniteDimensional.Residual.AngleEmbeddings

/-!
# Experimental residual `sin (2 Theta)` interface

The proof-complete perturbation, mirror-defect, spectral-subspace, and concrete
norm wrappers now live in `DavisKahan.FiniteDimensional.DoubleAngle.SinTheta`.
This module retains only the coordinate residual formulation, whose canonical
double-angle embedding and proof are not yet complete.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- The residual `sin 2 Theta` formulation for an isometric trial map. -/
theorem sinTwoTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
  sorry

end DavisKahanTheory
end ForMathlib
