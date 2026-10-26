/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.PairedPhase
public import ForTauCeti.Analysis.OperatorIdeal.Family.UnitaryTransport
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport

/-!
# Completed direct rotations in operator ideals

The canonical rotation displacement is the projection difference times
a bounded operator. Its finite ideal membership is therefore equivalent
to that of the projection difference, for every accepted operator-ideal
family, over both fields and in arbitrary Hilbert dimension.

The factorization uses `(I-R)(I+R)=2(I-S)`, the canonical intertwiner
factorization, and invertibility of `I+R` from the nonnegative Hermitian
part of a completed direct rotation. These are classical operator-ideal
consequences; no independent novelty claim is made.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped InnerProductSpace ENNReal

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A completed direct rotation has no singularity at phase `pi`:
adding identity gives a bounded invertible operator. -/
theorem isUnit_one_add_nonacuteDirectRotation
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    IsUnit (1 + nonacuteDirectRotation K L J) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ (c := 1) one_pos
  intro x
  rw [NNReal.coe_one, mul_one]
  calc
    ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 ((1 + nonacuteDirectRotation K L J) x) x) := by
      rw [add_apply, one_apply_eq_self, inner_add_left, map_add,
        inner_self_eq_norm_sq,
        re_inner_nonacuteDirectRotation_eq_absoluteValue K L J]
      exact le_add_of_nonneg_right
        ((spectraCanonicalIntertwiner K L).isPositive_modulus.re_inner_nonneg_left x)
    _ ≤ _ := RCLike.re_le_norm _

/-- The completed canonical displacement has a bounded right factor
through the actual projection difference. No compactness is assumed. -/
theorem exists_nonacuteDirectRotation_displacement_factor
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    ∃ B : H →L[𝕜] H, 1 - nonacuteDirectRotation K L J =
      (K.starProjection - L.starProjection) ∘L B := by
  let R := nonacuteDirectRotation K L J
  let S := spectraCanonicalIntertwiner K L
  let C := (spectraCanonicalIntertwiner K L).modulus
  have hRC : R * C = S := by
    rw [show C = Proposition35.section3CosAngleOperator K L from
      (Proposition35.section3CosAngleOperator_eq_canonicalAbsoluteValue K L).symm]
    exact nonacuteDirectRotation_mul_cosine_eq_canonicalIntertwiner K L J
  have hsum : R + star R = C + C :=
    nonacuteDirectRotation_add_star_eq_two_absoluteValue K L J
  have hunit : R * star R = 1 :=
    Unitary.mul_star_self_of_mem (nonacuteDirectRotation_mem_unitary K L J)
  have hsq : R * R = S + S - 1 := by
    have h : R * R + 1 = S + S := by
      calc
        _ = R * (R + star R) := by rw [mul_add, hunit]
        _ = R * (C + C) := by rw [hsum]
        _ = _ := by rw [mul_add, hRC]
    exact eq_sub_of_add_eq h
  have hS : 1 - S = (K.starProjection - L.starProjection) * K.reflectionOperator := by
    calc
      _ = -(S - 1) := by abel
      _ = -((L.starProjection - K.starProjection) * K.reflectionOperator) :=
        congrArg Neg.neg (spectraCanonicalIntertwiner_sub_one K L)
      _ = _ := by rw [← neg_mul, neg_sub]
  have hmul : (1 - R) * (1 + R) =
      (2 : 𝕜) • ((K.starProjection - L.starProjection) * K.reflectionOperator) := by
    calc
      _ = 1 - R * R := by noncomm_ring
      _ = (1 - S) + (1 - S) := by rw [hsq]; abel
      _ = _ := by rw [hS, two_smul]
  let u := (isUnit_one_add_nonacuteDirectRotation K L J).unit
  have hu : (u : H →L[𝕜] H) = 1 + R :=
    (isUnit_one_add_nonacuteDirectRotation K L J).unit_spec
  let B : H →L[𝕜] H := (2 : 𝕜) • (K.reflectionOperator * (↑u⁻¹ : H →L[𝕜] H))
  refine ⟨B, ?_⟩
  change 1 - R = (K.starProjection - L.starProjection) * B
  calc
    _ = (1 - R) * ((1 + R) * (↑u⁻¹ : H →L[𝕜] H)) := by rw [← hu, Units.mul_inv, mul_one]
    _ = ((1 - R) * (1 + R)) * (↑u⁻¹ : H →L[𝕜] H) := (mul_assoc _ _ _).symm
    _ = ((2 : 𝕜) • ((K.starProjection - L.starProjection) * K.reflectionOperator)) *
        (↑u⁻¹ : H →L[𝕜] H) := by rw [hmul]
    _ = _ := by
      ext x
      change (2 : 𝕜) • ((K.starProjection - L.starProjection)
        (K.reflectionOperator ((↑u⁻¹ : H →L[𝕜] H) x))) =
          (K.starProjection - L.starProjection)
            ((2 : 𝕜) • K.reflectionOperator ((↑u⁻¹ : H →L[𝕜] H) x))
      rw [map_smul]

/-- A completed direct rotation belongs to an accepted operator ideal
exactly when the projection difference does, including nonacute pairs
and arbitrary Hilbert dimensions. -/
theorem gauge_nonacuteDirectRotation_ne_top_iff_projection_sub
    (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    Φ.gauge (1 - nonacuteDirectRotation K L J) ≠ ∞ ↔
      Φ.gauge (K.starProjection - L.starProjection) ≠ ∞ := by
  constructor
  · intro hR
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
        unitary (H →L[𝕜] H))
    have hmap : K.map R.toLinearMap = L := by
      apply (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
      exact nonacuteDirectRotation_reflection_intertwines K L J
    have h := Φ.gauge_projection_sub_le_unitary_displacement K L R hmap
    exact ne_top_of_le_ne_top hR h
  · intro hD
    obtain ⟨B, hB⟩ := exists_nonacuteDirectRotation_displacement_factor K L J
    rw [hB]
    have hfinite : Φ.gauge (K.starProjection - L.starProjection) * ‖B‖ₑ ≠ ∞ :=
      ENNReal.mul_ne_top hD enorm_ne_top
    exact ne_top_of_le_ne_top hfinite (Φ.gauge_comp_right_le _ B)

end TauCeti.DavisKahan
