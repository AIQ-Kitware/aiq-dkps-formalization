/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.PairedPhase
public import ForTauCeti.Analysis.OperatorIdeal.Family.UnitaryTransport
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport
public import ForTauCeti.Analysis.InnerProductSpace.Projection.CompactTransportDefects
public import DavisKahan.Geometry.Halmos.CompactDefects

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

/-- The completed canonical displacement factors through the actual
projection difference with a factor of norm at most `sqrt 2`.
No compactness is assumed. -/
theorem exists_nonacuteDirectRotation_displacement_factor
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    ∃ B : H →L[𝕜] H, 1 - nonacuteDirectRotation K L J =
      (K.starProjection - L.starProjection) ∘L B ∧ ‖B‖ ≤ Real.sqrt 2 := by
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
  have hBbound : ‖B‖ ≤ Real.sqrt 2 := by
    apply B.opNorm_le_bound (Real.sqrt_nonneg 2)
    intro x
    let y := (↑u⁻¹ : H →L[𝕜] H) x
    have hxy : y + R y = x := by
      change ((1 + R) * (↑u⁻¹ : H →L[𝕜] H)) x = x
      rw [← hu, Units.mul_inv]
      rfl
    have hRnorm : ‖R y‖ = ‖y‖ :=
      Unitary.norm_map ⟨R, nonacuteDirectRotation_mem_unitary K L J⟩ y
    have hre : 0 ≤ RCLike.re (inner 𝕜 y (R y)) := by
      rw [inner_re_symm]
      rw [re_inner_nonacuteDirectRotation_eq_absoluteValue K L J]
      exact S.isPositive_modulus.re_inner_nonneg_left y
    have hsq : 2 * ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [← hxy, norm_add_sq (𝕜 := 𝕜), hRnorm]
      nlinarith
    have hBnorm : ‖B x‖ = 2 * ‖y‖ := by
      change ‖(2 : 𝕜) • K.reflectionOperator y‖ = 2 * ‖y‖
      rw [norm_smul, K.reflectionOperator_norm_map]
      norm_num
    rw [hBnorm]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  refine ⟨B, ?_, hBbound⟩
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

/-- Universal quantitative comparison of completed canonical displacement
with the projection difference, for every accepted operator-ideal gauge. -/
theorem gauge_nonacuteDirectRotation_le_sqrt_two_mul_projection_sub
    (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    Φ.gauge (1 - nonacuteDirectRotation K L J) ≤
      ENNReal.ofReal (Real.sqrt 2) * Φ.gauge (K.starProjection - L.starProjection) := by
  obtain ⟨B, hB, hnorm⟩ := exists_nonacuteDirectRotation_displacement_factor K L J
  rw [hB]
  calc
    _ ≤ Φ.gauge (K.starProjection - L.starProjection) * ‖B‖ₑ := Φ.gauge_comp_right_le _ B
    _ ≤ Φ.gauge (K.starProjection - L.starProjection) *
        ENNReal.ofReal (Real.sqrt 2) := by
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hnorm
    _ = _ := mul_comm _ _

/-- A completed direct rotation is within a factor `sqrt 2` of every
ambient unitary transporter in every accepted operator-ideal gauge.
Both fields and infinite objective values are included. -/
theorem gauge_nonacuteDirectRotation_le_sqrt_two_mul_transport
    (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (U : H ≃ₗᵢ[𝕜] H) (hmap : K.map U.toLinearMap = L) :
    Φ.gauge (1 - nonacuteDirectRotation K L J) ≤
      ENNReal.ofReal (Real.sqrt 2) * Φ.gauge (1 - (U : H →L[𝕜] H)) := by
  apply (gauge_nonacuteDirectRotation_le_sqrt_two_mul_projection_sub Φ K L J).trans
  gcongr
  exact Φ.gauge_projection_sub_le_unitary_displacement K L U hmap

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
    obtain ⟨B, hB, _⟩ := exists_nonacuteDirectRotation_displacement_factor K L J
    rw [hB]
    have hfinite : Φ.gauge (K.starProjection - L.starProjection) * ‖B‖ₑ ≠ ∞ :=
      ENNReal.mul_ne_top hD enorm_ne_top
    exact ne_top_of_le_ne_top hfinite (Φ.gauge_comp_right_le _ B)

/-- **Compact restricted-unitary feasibility.** A compact-displacement
unitary transports a pair exactly when its projection difference is
compact and its finite crossed defects are balanced. No finite-rank or
separability hypothesis is imposed. -/
theorem compact_transport_iff_compact_projection_sub_and_defect_balance
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃ U : H ≃ₗᵢ[𝕜] H, K.map U.toLinearMap = L ∧
      IsCompactOperator (((U : H →L[𝕜] H) - 1) : H →L[𝕜] H)) ↔
    IsCompactOperator ((K.starProjection - L.starProjection) : H →L[𝕜] H) ∧
      Module.finrank 𝕜 (halmosSourceDefect K L) =
        Module.finrank 𝕜 (halmosTargetDefect K L) := by
  constructor
  · rintro ⟨U, hmap, hU⟩
    refine ⟨K.isCompactOperator_projection_sub_of_compact_transport L U hmap hU, ?_⟩
    have hbalance := (K.finite_crossedDefect_balance_of_compact_transport L U hmap hU).2.2
    change Module.finrank 𝕜 (K ⊓ Lᗮ : Submodule 𝕜 H) =
      Module.finrank 𝕜 (Kᗮ ⊓ L : Submodule 𝕜 H)
    rwa [inf_comm Kᗮ L]
  · rintro ⟨hD, hbalance⟩
    obtain ⟨J⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq K L hD hbalance
    let U := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
        unitary (H →L[𝕜] H))
    refine ⟨U, ?_, ?_⟩
    · apply (Submodule.map_eq_iff_intertwines_reflection K L U).mpr
      exact nonacuteDirectRotation_reflection_intertwines K L J
    · obtain ⟨B, hB, _⟩ := exists_nonacuteDirectRotation_displacement_factor K L J
      have hcompact : IsCompactOperator ((1 - (U : H →L[𝕜] H)) : H →L[𝕜] H) := by
        change IsCompactOperator ((1 - nonacuteDirectRotation K L J) : H →L[𝕜] H)
        rw [hB]
        exact hD.comp_clm B
      rw [← neg_sub 1 (U : H →L[𝕜] H)]
      exact hcompact.neg

end TauCeti.DavisKahan
