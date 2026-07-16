/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Residual.Ritz

/-!
# Residuals of arbitrary trial maps

General trial-map residuals, complementary blocks, and the projected Sylvester
identity before orthonormalization.
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
/-- Residual of a general, not necessarily isometric, trial map. -/
noncomputable def generalResidual (A : E →ₗ[𝕜] E) (X : F →ₗ[𝕜] E)
    (M : F →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  A ∘ₗ X - X ∘ₗ M

/-- The raw complementary block of an arbitrary trial map.  For an isometric
embedding this specializes to `sinThetaEmbedding`; without normalization it is
the algebraic block bounded first in the generalized sine and tangent proofs. -/
noncomputable def complementaryTrialBlock (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗ[𝕜] E) : F →ₗ[𝕜] E :=
  complementaryProjection U ∘ₗ X

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp] theorem generalResidual_toLinearMap (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    generalResidual A X.toLinearMap M = residual A X M :=
  rfl
omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- **The arbitrary-trial-map projected-residual Sylvester identity.**

For a symmetric operator `A`, an `A`-reducing subspace `U`, an arbitrary trial
map `X`, and an arbitrary coordinate map `M`, the raw complementary block
`Y = P_{Uᗮ} X` satisfies

`A Y - Y M = P_{Uᗮ} (A X - X M)`.

This statement deliberately assumes no isometry, injectivity, frame bound,
or symmetry of `M`, and it does not require finite-dimensional trial
coordinates.  It is the shared algebraic root of the ordinary and generalized
residual sine bounds and of the graph-operator tangent development. -/
theorem sylvester_complementaryTrialBlock_eq_projectedGeneralResidual
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗ[𝕜] E) (M : F →ₗ[𝕜] F) :
    A ∘ₗ complementaryTrialBlock U X - complementaryTrialBlock U X ∘ₗ M =
      complementaryProjection U ∘ₗ generalResidual A X M := by
  ext x
  simp only [complementaryTrialBlock, generalResidual, LinearMap.comp_apply,
    LinearMap.sub_apply, map_sub]
  rw [complementaryProjection_apply_comm_of_reduces hA hU (X x)]

end DavisKahanTheory
end ForMathlib
