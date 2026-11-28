/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.PositiveTrace
import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison

/-!
# Trace norm of two projection differences and their directed sine maps

The symmetric full-space sine `|P_U - P_V|` counts contributions from both
halves of a principal plane.  The two one-sided cross projections
`P_{Vᗮ} P_U` and `P_{Uᗮ} P_V` count one contribution each.

This file proves the trace-norm identity **without** assuming equal subspace
ranks or choosing principal planes:

`‖P_U-P_V‖₁ = ‖P_{Vᗮ}P_U‖₁ + ‖P_{Uᗮ}P_V‖₁`.

The two compressions of TauCeti's symmetric sine operator to `U` and `Uᗮ`
are the directed moduli. Additivity of the trace on positive operators
then gives the formula for any two subspace dimensions.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A two-projection Gram identity.  The second term is a *left* Gram
operator, because the complementary block is supported on `Uᗮ`. -/
theorem projectionDifference_sq_eq_directed_gram_sum
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (U.starProjection.toLinearMap - V.starProjection.toLinearMap) ∘ₗ (U.starProjection.toLinearMap
        - V.starProjection.toLinearMap) =
      ((U.sinThetaMap V).toLinearMap).adjoint ∘ₗ (U.sinThetaMap V).toLinearMap +
        (V.sinThetaMap U).toLinearMap ∘ₗ ((V.sinThetaMap U).toLinearMap).adjoint := by
  let p : E →ₗ[𝕜] E := U.starProjection.toLinearMap
  let q : E →ₗ[𝕜] E := V.starProjection.toLinearMap
  have hq : q * q = q := by
    ext x
    change V.starProjection.toLinearMap (V.starProjection.toLinearMap x) =
        V.starProjection.toLinearMap x
    exact Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
  have hleft : (U.sinThetaMap V).toLinearMap = (1 - q) * p := by
    rw [Submodule.sinThetaMap_def]
    change Vᗮ.starProjection.toLinearMap ∘ₗ U.starProjection.toLinearMap = _
    rw [Submodule.starProjection_orthogonal V, ContinuousLinearMap.toLinearMap_sub,
        ContinuousLinearMap.coe_id]
    rfl
  have hright : (V.sinThetaMap U).toLinearMap = (1 - p) * q := by
    rw [Submodule.sinThetaMap_def]
    change Uᗮ.starProjection.toLinearMap ∘ₗ V.starProjection.toLinearMap = _
    rw [Submodule.starProjection_orthogonal U, ContinuousLinearMap.toLinearMap_sub,
        ContinuousLinearMap.coe_id]
    rfl
  have hleftAdj : ((U.sinThetaMap V).toLinearMap).adjoint = p * (1 - q) := by
    rw [Submodule.sinThetaMap_def]
    change (Vᗮ.starProjection.toLinearMap ∘ₗ U.starProjection.toLinearMap).adjoint = _
    rw [LinearMap.adjoint_comp, (Submodule.starProjection_isSymmetric _).adjoint_eq,
        Submodule.starProjection_orthogonal V, ContinuousLinearMap.toLinearMap_sub,
        ContinuousLinearMap.coe_id]
    rw [map_sub, LinearMap.adjoint_id, (Submodule.starProjection_isSymmetric _).adjoint_eq]
    rfl
  have hrightAdj : ((V.sinThetaMap U).toLinearMap).adjoint = q * (1 - p) := by
    rw [Submodule.sinThetaMap_def]
    change (Uᗮ.starProjection.toLinearMap ∘ₗ V.starProjection.toLinearMap).adjoint = _
    rw [LinearMap.adjoint_comp, (Submodule.starProjection_isSymmetric _).adjoint_eq,
        Submodule.starProjection_orthogonal U, ContinuousLinearMap.toLinearMap_sub,
        ContinuousLinearMap.coe_id]
    rw [map_sub, LinearMap.adjoint_id, (Submodule.starProjection_isSymmetric _).adjoint_eq]
    rfl
  rw [hleftAdj, hrightAdj, hleft, hright]
  change (p - q) * (p - q) = p * (1 - q) * ((1 - q) * p) +
    ((1 - p) * q) * (q * (1 - p))
  -- Expand the two Gram blocks before collecting terms.  In particular,
  -- reduce the nested `q * (q * p)` using `q² = q` before polynomial
  -- normalization; `noncomm_ring` does not perform this reduction by itself.
  have hcomp : (1 - q) * (1 - q) = 1 - q := by
    calc
      (1 - q) * (1 - q) = 1 - q - q + q * q := by noncomm_ring
      _ = 1 - q := by rw [hq]; noncomm_ring
  have hfirst : p * (1 - q) * ((1 - q) * p) = p * p - p * q * p := by
    calc
      _ = p * ((1 - q) * (1 - q)) * p := by simp only [mul_assoc]
      _ = p * (1 - q) * p := by rw [hcomp]
      _ = p * p - p * q * p := by noncomm_ring
  have hsecond : ((1 - p) * q) * (q * (1 - p)) =
      q - p * q - q * p + p * q * p := by
    calc
      _ = (1 - p) * (q * q) * (1 - p) := by simp only [mul_assoc]
      _ = (1 - p) * q * (1 - p) := by rw [hq]
      _ = q - p * q - q * p + p * q * p := by noncomm_ring
  calc
    (p - q) * (p - q) = p * p - p * q - q * p + q := by
      calc
        _ = p * p - p * q - q * p + q * q := by noncomm_ring
        _ = p * p - p * q - q * p + q := by rw [hq]
    _ = p * (1 - q) * ((1 - q) * p) +
        ((1 - p) * q) * (q * (1 - p)) := by
      rw [hfirst, hsecond]
      noncomm_ring

open ContinuousLinearMap in
/-- **Positive sine-modulus splitting of the projector difference.**

`|P_U-P_V| = |P_{Vᗮ}P_U| + |(P_{Uᗮ}P_V)⋆|`.

The second modulus must be formed *after* taking the adjoint: this puts
its support in `Uᗮ` instead of `V`. -/
theorem operatorAbs_projectionDifference_eq_directed_sine_sum
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    LinearMap.operatorAbs (U.starProjection.toLinearMap - V.starProjection.toLinearMap) =
      LinearMap.operatorAbs ((U.sinThetaMap V).toLinearMap) +
        LinearMap.operatorAbs (((V.sinThetaMap U).toLinearMap).adjoint) := by
  let := FiniteDimensional.completeSpace 𝕜 E
  have hreverse : Uᗮ.sinThetaMap Vᗮ = (V.sinThetaMap U).adjoint := by
    simp only [Submodule.sinThetaMap_def, adjoint_comp, Submodule.orthogonal_orthogonal,
      (isSelfAdjoint_starProjection V).adjoint_eq,
      (isSelfAdjoint_starProjection Uᗮ).adjoint_eq]
  have hcomplement :
      U.sinAngleOperator V * Uᗮ.starProjection = ((V.sinThetaMap U).adjoint).modulus := by
    rw [← U.sinAngleOperator_orthogonal V, Uᗮ.sinAngleOperator_mul_starProjection Vᗮ, hreverse]
  have hsplit :
      U.sinAngleOperator V = (U.sinThetaMap V).modulus + ((V.sinThetaMap U).adjoint).modulus := by
    rw [← U.sinAngleOperator_mul_starProjection V, ← hcomplement, ← mul_add,
      ← U.id_eq_sum_starProjection_self_orthogonalComplement,
      ← ContinuousLinearMap.one_def, mul_one]
  rw [ContinuousLinearMap.adjoint_toLinearMap]
  apply LinearMap.toContinuousLinearMap.injective
  rw [map_add, LinearMap.toContinuousLinearMap_operatorAbs_eq_modulus,
    LinearMap.toContinuousLinearMap_operatorAbs_eq_modulus,
    LinearMap.toContinuousLinearMap_operatorAbs_eq_modulus]
  rw [Submodule.sinAngleOperator_def] at hsplit
  exact hsplit

/-- **Trace-norm decomposition for any two projections.**

Unlike the squared Frobenius identity, this is an `ℓ¹` singular-value
identity.  No dimension matching or acute-angle assumption is needed. -/
theorem kyFanSum_projectionDifference_eq_directed_sines
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (U.starProjection.toLinearMap - V.starProjection.toLinearMap).kyFanSum (finrank 𝕜 E) =
      ((U.sinThetaMap V).toLinearMap).kyFanSum (finrank 𝕜 E) +
        ((V.sinThetaMap U).toLinearMap).kyFanSum (finrank 𝕜 E) := by
  let A : E →ₗ[𝕜] E := LinearMap.operatorAbs ((U.sinThetaMap V).toLinearMap)
  let B : E →ₗ[𝕜] E := LinearMap.operatorAbs (((V.sinThetaMap U).toLinearMap).adjoint)
  have hA : A.IsPositive := LinearMap.isPositive_operatorAbs _
  have hB : B.IsPositive := LinearMap.isPositive_operatorAbs _
  have hD : (U.starProjection.toLinearMap - V.starProjection.toLinearMap).kyFanSum (finrank 𝕜 E) =
      (A + B).kyFanSum (finrank 𝕜 E) := by
    change (U.starProjection.toLinearMap - V.starProjection.toLinearMap).kyFanSum (finrank 𝕜 E) =
      (LinearMap.operatorAbs ((U.sinThetaMap V).toLinearMap) +
          LinearMap.operatorAbs (((V.sinThetaMap U).toLinearMap).adjoint)).kyFanSum (finrank 𝕜 E)
    rw [← operatorAbs_projectionDifference_eq_directed_sine_sum U V]
    simp only [LinearMap.kyFanSum_def, ← Fin.sum_univ_eq_sum_range,
      LinearMap.singularValues_operatorAbs]
  have hleft : A.kyFanSum (finrank 𝕜 E) =
      ((U.sinThetaMap V).toLinearMap).kyFanSum (finrank 𝕜 E) := by
    simp only [A, LinearMap.kyFanSum_def, ← Fin.sum_univ_eq_sum_range,
      LinearMap.singularValues_operatorAbs]
  have hright : B.kyFanSum (finrank 𝕜 E) =
      ((V.sinThetaMap U).toLinearMap).kyFanSum (finrank 𝕜 E) := by
    simp only [B, LinearMap.kyFanSum_def, ← Fin.sum_univ_eq_sum_range,
      LinearMap.singularValues_operatorAbs,
      LinearMap.singularValues_adjoint]
  calc
    (U.starProjection.toLinearMap - V.starProjection.toLinearMap).kyFanSum (finrank 𝕜 E) =
        (A + B).kyFanSum (finrank 𝕜 E) := hD
    _ = A.kyFanSum (finrank 𝕜 E) + B.kyFanSum (finrank 𝕜 E) :=
      kyFanSum_add_of_isPositive A B hA hB
    _ = ((U.sinThetaMap V).toLinearMap).kyFanSum (finrank 𝕜 E) +
          ((V.sinThetaMap U).toLinearMap).kyFanSum (finrank 𝕜 E) := by
      rw [hleft, hright]

end TauCeti

end
