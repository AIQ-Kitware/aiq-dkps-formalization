/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
import ForTauCeti.Analysis.InnerProductSpace.QuadraticFormBounds
import ForTauCeti.Analysis.InnerProductSpace.ProjectionGap
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Operator

/-!
# Supported bounded Davis--Kahan vocabulary

This module is the scalar-generic `RCLike` surface for the supported bounded
Davis--Kahan theory.  Spectral implementations and long-horizon literature
scaffolds live in separate modules.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/BoundedOperator/Basic.lean`
until 2026-07-29, when lane Y3(b3) moved the dependency-closed base of the sin-Θ core
into the staging layer.  Statements, proofs, signatures and namespaces are
unchanged; the declarations already lived in `TauCeti.DavisKahan*`, so the move
was a path change and an import repoint and nothing else.

The move became possible only once Y3(b2) took the `ForMathlib`
inner-product-space component into `ForTauCeti`: before that this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Compatibility-friendly name for symmetry of a bounded operator. -/
abbrev IsSelfAdjointOperator (A : E →L[𝕜] E) : Prop := A.IsSymmetric

/-- Compatibility-friendly name for a reducing subspace. -/
abbrev Reduces (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop := A.Reduces U

/-- Orthogonal projection onto a subspace. -/
noncomputable abbrev projection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E := U.starProjection

/-- Orthogonal projection onto the orthogonal complement. -/
noncomputable abbrev complementaryProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E := Uᗮ.starProjection

/-- Reflection through a subspace. -/
noncomputable abbrev reflectionOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E := U.reflectionOperator

/-- Diagonal block extraction. -/
noncomputable abbrev diagonalPart (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  U.diagonalPart A

/-- Symmetric projection gap. -/
noncomputable abbrev subspaceGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  U.projectionGap V

/-- Directed projection gap. -/
noncomputable abbrev directedGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  U.directedProjectionGap V

/-- The two subspaces are in the acute case. -/
def IsAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  subspaceGap U V < 1

/-- The projection gap lies below the quarter-angle threshold. -/
def IsQuarterAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  subspaceGap U V < Real.sqrt 2 / 2

/-- An isometric bounded embedding. -/
def IsometricEmbedding (X : F →L[𝕜] E) : Prop := ∀ x, ‖X x‖ = ‖x‖

/-- Residual of an approximate invariant pair. -/
def residual (A : E →L[𝕜] E) (X : F →L[𝕜] E)
    (M : F →L[𝕜] F) : F →L[𝕜] E := A ∘L X - X ∘L M

/-- Directed sine block for an approximate subspace embedding. -/
noncomputable def sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) : F →L[𝕜] E :=
  Uᗮ.starProjection ∘L X

/-- A symmetric invariant subspace is reducing. -/
theorem reduces_orthogonalComplement {A : E →L[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) : Reduces A U :=
  ContinuousLinearMap.IsSymmetric.reduces_of_invariant hA hU

/-- Projection commutation for a reducing subspace. -/
theorem projection_comp_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) :
    projection U ∘L A = A ∘L projection U :=
  ContinuousLinearMap.starProjection_comp_comm_of_reduces A U hU

/-- Pointwise projection commutation for a reducing subspace. -/
theorem projection_apply_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) (x : E) :
    projection U (A x) = A (projection U x) :=
  ContinuousLinearMap.starProjection_apply_comm_of_reduces A U hU x

/-- Reflection commutes with an operator reduced by the subspace. -/
theorem reflectionOperator_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) :
    reflectionOperator U ∘L A = A ∘L reflectionOperator U :=
  Submodule.reflectionOperator_comm_of_reduces A U hU

/-- Reflection is involutive. -/
theorem reflectionOperator_involutive (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    reflectionOperator U ∘L reflectionOperator U = ContinuousLinearMap.id 𝕜 E :=
  U.reflectionOperator_involutive

/-- Reflection has operator norm at most one. -/
theorem norm_reflectionOperator_le_one (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : ‖reflectionOperator U‖ ≤ 1 :=
  U.norm_reflectionOperator_le_one

/-- Constant-one separated-form Sylvester estimate. -/
theorem norm_sylvester_le_of_coercive
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) :
    ‖X‖ ≤ ‖C‖ / g :=
  TauCeti.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq hA hB hg hAc hBc hEq

end DavisKahan
end TauCeti
