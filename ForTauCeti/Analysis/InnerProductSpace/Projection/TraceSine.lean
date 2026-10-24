/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.PositiveTrace

/-!
# Trace norm of two projection differences and their directed sine maps

The symmetric full-space sine `|P_U - P_V|` counts contributions from both
halves of a principal plane.  The two one-sided cross projections
`P_{Vᗮ} P_U` and `P_{Uᗮ} P_V` count one contribution each.

This file proves the trace-norm identity **without** assuming equal subspace
ranks or choosing principal planes:

`‖P_U-P_V‖₁ = ‖P_{Vᗮ}P_U‖₁ + ‖P_{Uᗮ}P_V‖₁`.

The proof splits `(P_U-P_V)²` into two orthogonally supported Gram operators,
uses uniqueness of the positive square root to split the modulus, and then
uses additivity of the trace on positive operators.  The two directed terms
need not be equal when the subspaces have different dimensions.
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
    (projection U - projection V) ∘ₗ (projection U - projection V) =
      (sinThetaMap U V).adjoint ∘ₗ sinThetaMap U V +
        sinThetaMap V U ∘ₗ (sinThetaMap V U).adjoint := by
  let p : E →ₗ[𝕜] E := projection U
  let q : E →ₗ[𝕜] E := projection V
  have hq : q * q = q := by
    ext x
    change projection V (projection V x) = projection V x
    exact Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
  have hleft : sinThetaMap U V = (1 - q) * p := by
    rw [sinThetaMap, complementaryProjection_eq_id_sub V]
    rfl
  have hright : sinThetaMap V U = (1 - p) * q := by
    rw [sinThetaMap, complementaryProjection_eq_id_sub U]
    rfl
  have hleftAdj : (sinThetaMap U V).adjoint = p * (1 - q) := by
    rw [sinThetaMap, LinearMap.adjoint_comp, projection_adjoint,
      complementaryProjection_eq_id_sub V]
    rw [map_sub, LinearMap.adjoint_id, projection_adjoint]
    rfl
  have hrightAdj : (sinThetaMap V U).adjoint = q * (1 - p) := by
    rw [sinThetaMap, LinearMap.adjoint_comp, projection_adjoint,
      complementaryProjection_eq_id_sub U]
    rw [map_sub, LinearMap.adjoint_id, projection_adjoint]
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

/-- The initial-space modulus of the reverse adjoint sine maps into `Uᗮ`. -/
private theorem operatorAbs_adjoint_reverse_sine_mem_complement
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (x : E) :
    operatorAbs ((sinThetaMap V U).adjoint) x ∈ Uᗮ := by
  have hmem := operatorAbs_apply_mem_orthogonal_ker ((sinThetaMap V U).adjoint) x
  -- `U` is in the kernel of the reversed sine adjoint. Orthogonality
  -- reverses inclusions, so the modulus image belongs to `Uᗮ`.
  have hUker : U ≤ LinearMap.ker ((sinThetaMap V U).adjoint) := by
    intro y hy
    change (sinThetaMap V U).adjoint y = 0
    rw [sinThetaMap, LinearMap.adjoint_comp, projection_adjoint,
      complementaryProjection, projection_adjoint]
    change V.starProjection (Uᗮ.starProjection y) = 0
    have hzero : Uᗮ.starProjection y = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr (by
        simpa only [Submodule.orthogonal_orthogonal] using hy)
    rw [hzero, map_zero]
  exact (Submodule.orthogonal_le hUker) hmem

/-- The positive moduli of the two directed Gram blocks have disjoint
support. This is the operative orthogonality in the square-root splitting. -/
private theorem operatorAbs_directed_mul_operatorAbs_reverse_adjoint_eq_zero
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    operatorAbs (sinThetaMap U V) ∘ₗ
        operatorAbs ((sinThetaMap V U).adjoint) = 0 := by
  apply LinearMap.ext
  intro x
  change operatorAbs (sinThetaMap U V)
    (operatorAbs ((sinThetaMap V U).adjoint) x) = 0
  have hperp := operatorAbs_adjoint_reverse_sine_mem_complement U V x
  have hker : operatorAbs ((sinThetaMap V U).adjoint) x ∈
      LinearMap.ker (sinThetaMap U V) := by
    change sinThetaMap U V (operatorAbs ((sinThetaMap V U).adjoint) x) = 0
    change Vᗮ.starProjection
      (U.starProjection (operatorAbs ((sinThetaMap V U).adjoint) x)) = 0
    rw [(Submodule.starProjection_apply_eq_zero_iff U).mpr hperp, map_zero]
  rw [← ker_operatorAbs (sinThetaMap U V)] at hker
  exact LinearMap.mem_ker.mp hker

/-- **Positive sine-modulus splitting of the projector difference.**

`|P_U-P_V| = |P_{Vᗮ}P_U| + |(P_{Uᗮ}P_V)⋆|`.

The second modulus must be formed *after* taking the adjoint: this puts
its support in `Uᗮ` instead of `V`. -/
theorem operatorAbs_projectionDifference_eq_directed_sine_sum
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    operatorAbs (projection U - projection V) =
      operatorAbs (sinThetaMap U V) +
        operatorAbs ((sinThetaMap V U).adjoint) := by
  let D : E →ₗ[𝕜] E := projection U - projection V
  let A : E →ₗ[𝕜] E := operatorAbs (sinThetaMap U V)
  let B : E →ₗ[𝕜] E := operatorAbs ((sinThetaMap V U).adjoint)
  have hA : A.IsPositive := isPositive_operatorAbs _
  have hB : B.IsPositive := isPositive_operatorAbs _
  have hAB : A * B = 0 :=
    operatorAbs_directed_mul_operatorAbs_reverse_adjoint_eq_zero U V
  have hBA : B * A = 0 := by
    have h := congrArg LinearMap.adjoint hAB
    change LinearMap.adjoint (A ∘ₗ B) =
      LinearMap.adjoint (0 : E →ₗ[𝕜] E) at h
    rw [LinearMap.adjoint_comp, map_zero, hA.adjoint_eq, hB.adjoint_eq] at h
    exact h
  have hDstar : D.adjoint = D := by
    dsimp [D]
    rw [map_sub, projection_adjoint, projection_adjoint]
  have hgram : A * A + B * B = D.adjoint * D := by
    change operatorAbs (sinThetaMap U V) ∘ₗ operatorAbs (sinThetaMap U V) +
        operatorAbs ((sinThetaMap V U).adjoint) ∘ₗ
          operatorAbs ((sinThetaMap V U).adjoint) =
        D.adjoint ∘ₗ D
    rw [operatorAbs_mul_self, operatorAbs_mul_self,
      LinearMap.adjoint_adjoint, hDstar]
    exact (projectionDifference_sq_eq_directed_gram_sum U V).symm
  have hsq : (A + B) * (A + B) = D.adjoint * D := by
    calc
      (A + B) * (A + B) = A * A + B * B := by
        noncomm_ring [hAB, hBA]
      _ = D.adjoint * D := hgram
  have hsqrt : operatorAbs D = A + B := by
    symm
    exact (LinearMap.isPositive_adjoint_comp_self D).sqrt_unique
      (hA.add hB) hsq
  exact hsqrt

/-- **Trace-norm decomposition for any two projections.**

Unlike the squared Frobenius identity, this is an `ℓ¹` singular-value
identity.  No dimension matching or acute-angle assumption is needed. -/
theorem kyFanSum_projectionDifference_eq_directed_sines
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    kyFanSum (finrank 𝕜 E) (projection U - projection V) =
      kyFanSum (finrank 𝕜 E) (sinThetaMap U V) +
        kyFanSum (finrank 𝕜 E) (sinThetaMap V U) := by
  let A : E →ₗ[𝕜] E := operatorAbs (sinThetaMap U V)
  let B : E →ₗ[𝕜] E := operatorAbs ((sinThetaMap V U).adjoint)
  have hA : A.IsPositive := isPositive_operatorAbs _
  have hB : B.IsPositive := isPositive_operatorAbs _
  have hD : kyFanSum (finrank 𝕜 E) (projection U - projection V) =
      kyFanSum (finrank 𝕜 E) (A + B) := by
    change kyFanSum (finrank 𝕜 E) (projection U - projection V) =
      kyFanSum (finrank 𝕜 E)
        (operatorAbs (sinThetaMap U V) +
          operatorAbs ((sinThetaMap V U).adjoint))
    rw [← operatorAbs_projectionDifference_eq_directed_sine_sum U V]
    simp only [kyFanSum_eq_sum_fin, singularValues_operatorAbs]
  have hleft : kyFanSum (finrank 𝕜 E) A =
      kyFanSum (finrank 𝕜 E) (sinThetaMap U V) := by
    simp only [A, kyFanSum_eq_sum_fin, singularValues_operatorAbs]
  have hright : kyFanSum (finrank 𝕜 E) B =
      kyFanSum (finrank 𝕜 E) (sinThetaMap V U) := by
    simp only [B, kyFanSum_eq_sum_fin, singularValues_operatorAbs,
      LinearMap.singularValues_adjoint]
  calc
    kyFanSum (finrank 𝕜 E) (projection U - projection V) =
        kyFanSum (finrank 𝕜 E) (A + B) := hD
    _ = kyFanSum (finrank 𝕜 E) A + kyFanSum (finrank 𝕜 E) B :=
      kyFanSum_add_of_isPositive A B hA hB
    _ = kyFanSum (finrank 𝕜 E) (sinThetaMap U V) +
          kyFanSum (finrank 𝕜 E) (sinThetaMap V U) := by
      rw [hleft, hright]

end TauCeti

end
