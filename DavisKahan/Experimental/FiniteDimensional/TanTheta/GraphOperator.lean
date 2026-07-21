/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Experimental.FiniteDimensional.Residual.AngleEmbeddings
import DavisKahan.FiniteDimensional.Core.OperatorBlocks
import DavisKahan.FiniteDimensional.SinTheta.UnitarilyInvariant
import DavisKahan.Experimental.FiniteDimensional.Core.AngleOperators

/-!
# Unresolved ambient tangent perturbation proposals

These declarations are retained as proof-plan archaeology, but are deliberately
separated from the completed coordinate graph and residual layer.  Their old
bodies depend on a graph/Riccati API that has not yet been constructed, and the
all-UI comparison with the full positive tangent operator additionally requires
careful multiplicity accounting.  This module remains an independent
experimental repair root rather than blocking coordinate tangent results.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Davis--Kahan `tan Θ`, perturbation form, every UI norm.**

Lean proof route for a weaker agent:

1. Convert the reducing subspace of `B` into a graph over `U`, use the zero-compression hypothesis to obtain the tangent Sylvester equation, and apply the residual theorem.
2. Reuse the experimental graph/Riccati geometry for the operator-norm skeleton; keep UI singular values finite.

Signature audit: `hacute` now supplies the domain on which the full finite tangent operator
represents the principal tangents without a `π/2` pole.
-/
theorem tanTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (tanAngleOperator U V) ≤ N (B - A) := by
  classical
  let T := angularOperator U V hacute
  have hgraph : V = graphSubspace U T := graphSubspace_angularOperator U V hacute
  have hriccati :
      compression B Vᗮ ∘ₗ T - T ∘ₗ compression A U =
        complementaryProjection V ∘ₗ (B - A) ∘ₗ projection U := by
    exact tangentSylvesterEquation_of_reduces_zeroCompression
      hA hB hU hV hzero hacute
  have hsolve := uiNorm_sylvester_le_of_orderedGap
    N hA hB hδ hgap T
      (complementaryProjection V ∘ₗ (B - A) ∘ₗ projection U) hriccati
  have hrhs :
      N (complementaryProjection V ∘ₗ (B - A) ∘ₗ projection U) ≤ N (B - A) :=
    N.projection_comp_projection_le _
  have hsing : N T = N (tanAngleOperator U V) := by
    exact N.eq_of_same_singularValues
      (singularValues_angularOperator_eq_tanAngleOperator U V hacute)
  simpa [hsing] using hsolve.trans hrhs

/-- Cross/graph form of the perturbation theorem.

Lean proof route for a weaker agent:

1. Convert the reducing subspace of `B` into a graph over `U`, use the zero-compression hypothesis to obtain the tangent Sylvester equation, and apply the residual theorem.
2. Reuse the experimental graph/Riccati geometry for the operator-norm skeleton; keep UI singular values finite.
-/
theorem tanThetaMap_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (htrans : IsTransverse U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (tanThetaMap U V) ≤ N (B - A) := by
  classical
  let T := graphMapOfTransverse U V htrans
  have hriccati := tangentSylvesterEquation_of_transverse
    hA hB hU hV hzero htrans
  have hsolve := uiNorm_sylvester_le_of_orderedGap
    N hA hB hδ hgap T
      (complementaryProjection V ∘ₗ (B - A) ∘ₗ projection U) hriccati
  have hrhs := N.projection_comp_projection_le (B - A) Vᗮ U
  have hsame : N T = N (tanThetaMap U V) := by
    exact N.eq_of_same_singularValues
      (singularValues_graphMap_eq_tanThetaMap U V htrans)
  simpa [T, hsame] using hsolve.trans hrhs

/-- Canonical spectral-subspace version.

Signature audit: `hacute` explicitly selects the transverse spectral branch.  A later
continuation theorem may derive this premise in common applications.
-/
theorem tanTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hzero : HasZeroCompression (spectralSubspace A (Set.Icc a b)) (B - A))
    (hacute : IsAcute (spectralSubspace A (Set.Icc a b))
      (spectralSubspace B (Set.Icc a b)))
    (hgap : OrderedGap A (spectralSubspace A (Set.Icc a b))
      B (spectralSubspace B (Set.Icc a b))ᗮ δ) :
    δ * N (tanAngleOperator (spectralSubspace A (Set.Icc a b))
        (spectralSubspace B (Set.Icc a b))) ≤ N (B - A) :=
  tanTheta_perturbation_le N hA hB
    (reduces_spectralSubspace A (Set.Icc a b))
    (reduces_spectralSubspace B (Set.Icc a b))
    hzero hacute hδ hgap

/-- Operator-norm largest-angle form.

Signature audit: The explicit `hacute` premise makes the full-space tangent operator a valid
finite principal-angle object.
-/
theorem opNorm_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * ‖(tanAngleOperator U V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  exact tanTheta_perturbation_le (UnitarilyInvariantNorm.opNorm 𝕜 E)
    hA hB hU hV hzero hacute hδ hgap

/-- Frobenius `tan Θ` form.

Signature audit: The explicit `hacute` premise rules out tangent poles and makes the
one-sided graph singular values well-defined.
-/
theorem frobenius_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * UnitarilyInvariantNorm.frobenius 𝕜 E (tanAngleOperator U V) ≤
      UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  exact tanTheta_perturbation_le (UnitarilyInvariantNorm.frobenius 𝕜 E)
    hA hB hU hV hzero hacute hδ hgap

/-- Ky Fan `tan Θ` form.

Signature audit: The explicit `hacute` premise rules out tangent poles and makes the
one-sided graph singular values well-defined.
-/
theorem kyFan_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) (k : ℕ) :
    δ * kyFanSum k (tanAngleOperator U V) ≤ kyFanSum k (B - A) := by
  let NK : UnitarilyInvariantNorm 𝕜 E :=
    (RectangularUnitarilyInvariantNorm.kyFan
      (𝕜 := 𝕜) (E := E) (F := E) k).toSquare
  have h := tanTheta_perturbation_le NK hA hB hU hV hzero hacute hδ hgap
  simpa [NK, RectangularUnitarilyInvariantNorm.toSquare,
    RectangularUnitarilyInvariantNorm.kyFan_apply,
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum,
    kyFanSum_eq_sum_fin] using h

end DavisKahanTheory
end ForMathlib
