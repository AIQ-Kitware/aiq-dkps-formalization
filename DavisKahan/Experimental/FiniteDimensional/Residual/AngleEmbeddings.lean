/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Residual.AngleEmbedding

/-!
# Coordinate angle maps for trial embeddings

For an isometric trial map `X : F → E`, the cosine and sine blocks are
`P_U X` and `P_{Uᗮ} X`.  The tangent is the sine block composed with the
Moore--Penrose inverse of the cosine block.  The double-angle maps are the
corresponding polynomial/rational functions of the cosine and sine blocks.
The Moore--Penrose inverse totalizes the definitions; transversality and
quarter-turn avoidance identify it with the ordinary inverse on the relevant
range.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Tangent block in trial coordinates, totalized by the Moore--Penrose inverse
of the cosine block. -/
noncomputable def tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  sinThetaEmbedding U X ∘ₗ
    FiniteDimensional.moorePenroseInverse (cosThetaEmbedding U X)

/-- Double-angle sine block `2 S C`, written in trial coordinates. -/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  (2 : 𝕜) •
    (sinThetaEmbedding U X ∘ₗ
      LinearMap.adjoint (cosThetaEmbedding U X)) ∘ₗ X.toLinearMap

/-- Double-angle tangent block, totalized by the Moore--Penrose inverse of the
double-angle cosine block. -/
noncomputable def tanTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  sinTwoThetaEmbedding U X ∘ₗ
    FiniteDimensional.moorePenroseInverse
      (FiniteDimensional.cosTwoThetaEmbedding U X)

/-- Under transversality, the singular values of the trial-coordinate tangent
are the tangents of the principal angles. -/
theorem singularValues_tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverseEmbedding U X) (i : ℕ) :
    (tanThetaEmbedding U X).singularValues i =
      Real.tan (principalAngles U (approximateSubspace X) i) := by
  classical
  let C := cosThetaEmbedding U X
  let S := sinThetaEmbedding U X
  have hCinj : Function.Injective C := htrans.cosThetaEmbedding_injective
  have hCS := simultaneousSingularValueDecomposition_cos_sin U X
  obtain ⟨eF, eU, eP, c, s, hc, hs, hC, hS⟩ := hCS
  rw [tanThetaEmbedding, hC, hS,
    FiniteDimensional.moorePenroseInverse_diagonal hCinj]
  simp [LinearMap.singularValues_diagonal, Real.tan_eq_sin_div_cos,
    hc, hs]

/-- Under quarter-turn avoidance, the singular values of the totalized
double-angle tangent are `|tan (2θ_i)|`. -/
theorem singularValues_tanTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (havoid : AvoidsQuarterTurnEmbedding U X) (i : ℕ) :
    (tanTwoThetaEmbedding U X).singularValues i =
      |Real.tan (2 * principalAngles U (approximateSubspace X) i)| := by
  classical
  let θ := principalAngles U (approximateSubspace X) i
  have hcos : Real.cos (2 * θ) ≠ 0 := havoid.cos_two_ne_zero i
  obtain ⟨eF, eE, s2, c2, hS2, hC2⟩ :=
    simultaneousSingularValueDecomposition_doubleAngle U X
  rw [tanTwoThetaEmbedding, hS2, hC2,
    FiniteDimensional.moorePenroseInverse_diagonal_of_ne_zero hcos]
  simp [LinearMap.singularValues_diagonal, Real.tan_eq_sin_div_cos,
    abs_div]

end DavisKahanTheory
end ForMathlib
