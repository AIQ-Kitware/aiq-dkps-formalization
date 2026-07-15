/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Core.AngleGeometry

/-!
# Finite-dimensional angle operators

These definitions use finite self-adjoint functional calculus and the
Moore--Penrose inverse.  The safe tangent convention is zero on a pole; all
analytic tangent theorems carry transversality or quarter-turn avoidance, so
the pole branch is never observed there.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The one-sided tangent cross-map `S C†`. -/
noncomputable def tanThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  sinThetaMap U V ∘ₗ FiniteDimensional.moorePenroseInverse (cosThetaMap U V)

/-- Scalar tangent with the Moore--Penrose convention at poles. -/
noncomputable def safeTan (theta : ℝ) : ℝ :=
  if Real.cos theta = 0 then 0 else Real.sin theta / Real.cos theta

/-- Scalar double tangent with the Moore--Penrose convention at quarter turns. -/
noncomputable def safeTanTwo (theta : ℝ) : ℝ :=
  if Real.cos (2*theta) = 0 then 0 else
    Real.sin (2*theta) / Real.cos (2*theta)

/-- Canonical ambient angle operator obtained from the positive sine operator. -/
noncomputable def angleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  FiniteDimensional.selfAdjointFunctionalCalculus Real.arcsin
    (sinAngleOperator U V)

/-- `tan Θ` on the full ambient space. -/
noncomputable def tanAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  FiniteDimensional.selfAdjointFunctionalCalculus safeTan (angleOperator U V)

/-- `tan (2Θ)` on the full ambient space. -/
noncomputable def tanTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  FiniteDimensional.selfAdjointFunctionalCalculus safeTanTwo (angleOperator U V)

/-- On transverse pairs, the tangent map is the sine block followed by the
true inverse of the cosine block. -/
theorem tanThetaMap_eq_sin_comp_inv
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (htrans : IsTransverse U V) :
    tanThetaMap U V = sinThetaMap U V ∘ₗ
      (cosThetaMap U V).inverseOnRange := by
  rw [tanThetaMap,
    FiniteDimensional.moorePenroseInverse_eq_inverseOnRange htrans]

/-- Orthogonal complements preserve the principal-angle sequence at equal rank. -/
theorem principalAngles_orthogonal (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hrank : finrank 𝕜 U = finrank 𝕜 V) :
    principalAngles Uᗮ Vᗮ = principalAngles U V := by
  rw [principalAngles, principalAngles]
  congr 1
  change
    (complementaryProjection (Vᗮ) ∘ₗ projection (Uᗮ)).singularValues =
      (complementaryProjection V ∘ₗ projection U).singularValues
  rw [Submodule.orthogonal_orthogonal,
    Submodule.starProjection_orthogonal',
    Submodule.starProjection_orthogonal']
  have hCS := singularValues_complementary_cross_blocks U V hrank
  simpa [sinThetaMap] using hCS

/-- The spectrum of the ambient angle operator is the principal-angle
multiset, with the canonical ambient multiplicity. -/
theorem eigenvalues_angleOperator
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (angleOperator U V).eigenvalues =
      (sinAngleOperator U V).eigenvalues.map Real.arcsin := by
  exact FiniteDimensional.eigenvalues_functionalCalculus _ _

end DavisKahanTheory
end ForMathlib
