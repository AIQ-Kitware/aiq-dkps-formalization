/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearOptimizerCertificate
public import ForTauCeti.Analysis.InnerProductSpace.UnitaryPositiveAverage

/-!
# Spectral structure of every nuclear transport optimizer

The actual dual certificate implies a positive-average identity for
the relative unitary and its conjugated adjoint. This gives intrinsic
cosine preservation before choosing principal-angle coordinates. The
argument retains the full common sector and arbitrary right defects.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Self-adjointness of the nuclear dual displacement, together with
fixation of the full common sector, forces an exact positive average.
This algebraic step needs neither a trace-class nor a reflection
commutation assumption on Z. -/
theorem nuclearTransportDual_relative_positive_average
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (Z : E ≃ₗᵢ[𝕜] E)
    (hfix : (1 - (Z : E →L[𝕜] E)) *
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker.starProjection = 0)
    (hself : IsSelfAdjoint (star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E)))) :
    (Z : E →L[𝕜] E) + star (nuclearTransportDual K L D : E →L[𝕜] E) *
      star (Z : E →L[𝕜] E) * (nuclearTransportDual K L D : E →L[𝕜] E) =
        Proposition35.section3CosAngleOperator K L + Proposition35.section3CosAngleOperator K L := by
  let R := nonacuteDirectRotation K L D
  let V := nuclearTransportDual K L D
  let B := R - Proposition35.section3CosAngleOperator K L
  let Q := B.ker.starProjection
  have hQ : IsSelfAdjoint Q := isSelfAdjoint_starProjection B.ker
  have hRQ : R * Q = Q := nonacuteDirectRotation_mul_skew_ker_projection K L D
  have hZQ : (Z : E →L[𝕜] E) * Q = Q := by
    change (1 - (Z : E →L[𝕜] E)) * Q = 0 at hfix
    rw [sub_mul, one_mul, sub_eq_zero] at hfix
    exact hfix.symm
  have hQstarR : Q * star R = Q := by
    simpa only [star_mul, hQ.star_eq] using congrArg star hRQ
  have hQstarZ : Q * star (Z : E →L[𝕜] E) = Q := by
    simpa only [star_mul, hQ.star_eq] using congrArg star hZQ
  have hQzero : Q * (star R - star (Z : E →L[𝕜] E)) = 0 := by
    rw [mul_sub, hQstarR, hQstarZ, sub_self]
  have hVsum : (V : E →L[𝕜] E) + star (V : E →L[𝕜] E) = Q + Q :=
    nuclearTransportDual_add_star K L D
  have hanti : (V : E →L[𝕜] E) * (star R - star (Z : E →L[𝕜] E)) =
      -(star (V : E →L[𝕜] E) * (star R - star (Z : E →L[𝕜] E))) := by
    apply add_eq_zero_iff_eq_neg.mp
    rw [← add_mul, hVsum, add_mul, hQzero, add_zero]
  have hRV := nonacuteDirectRotation_comm_nuclearTransportDual K L D
  have hstarRV : star (V : E →L[𝕜] E) * star R = star R * star (V : E →L[𝕜] E) := by
    simpa only [star_mul] using congrArg star hRV.eq
  have hVm : (V : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) :=
    (Unitary.linearIsometryEquiv.symm V).property
  have hconjR : star (V : E →L[𝕜] E) * star R * (V : E →L[𝕜] E) = star R := by
    rw [hstarRV, mul_assoc, Unitary.star_mul_self_of_mem hVm,
      mul_one]
  have heq : star (V : E →L[𝕜] E) * (R - (Z : E →L[𝕜] E)) =
      (star R - star (Z : E →L[𝕜] E)) * (V : E →L[𝕜] E) := by
    simpa only [star_mul, star_sub, star_star] using hself.star_eq.symm
  have htrans : R - (Z : E →L[𝕜] E) = -star R +
      star (V : E →L[𝕜] E) * star (Z : E →L[𝕜] E) * (V : E →L[𝕜] E) := by
    calc
      _ = ((V : E →L[𝕜] E) * star (V : E →L[𝕜] E)) * (R - (Z : E →L[𝕜] E)) := by
        rw [Unitary.mul_star_self_of_mem hVm, one_mul]
      _ = (V : E →L[𝕜] E) * (star (V : E →L[𝕜] E) * (R - (Z : E →L[𝕜] E))) := mul_assoc _ _ _
      _ = (V : E →L[𝕜] E) * ((star R - star (Z : E →L[𝕜] E)) * (V : E →L[𝕜] E)) := by rw [heq]
      _ = ((V : E →L[𝕜] E) * (star R - star (Z : E →L[𝕜] E))) * (V : E →L[𝕜] E) := (mul_assoc _ _ _).symm
      _ = _ := by rw [hanti, neg_mul, mul_sub, sub_mul, hconjR]; abel
  have hW : star (V : E →L[𝕜] E) * star (Z : E →L[𝕜] E) * (V : E →L[𝕜] E) =
      (R - (Z : E →L[𝕜] E)) + star R := by rw [htrans]; abel
  change (Z : E →L[𝕜] E) + _ = _
  rw [hW]
  calc
    _ = R + star R := by abel
    _ = _ := nonacuteDirectRotation_add_star_eq_two_cosine K L D

/-- The dual's self-adjointness forces preservation of the intrinsic
cosine and commutation with the dual on the positive-cosine support.
The right-angle kernel is retained as an explicit exceptional sector. -/
theorem nuclearTransportDual_relative_cosine_structure
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (Z : E ≃ₗᵢ[𝕜] E)
    (hfix : (1 - (Z : E →L[𝕜] E)) *
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L).ker.starProjection = 0)
    (hself : IsSelfAdjoint (star (nuclearTransportDual K L D : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D - (Z : E →L[𝕜] E)))) :
    Commute (Z : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L) ∧
      ∀ x ∈ (Proposition35.section3CosAngleOperator K L).kerᗮ,
        Z (nuclearTransportDual K L D x) = nuclearTransportDual K L D (Z x) := by
  let C := Proposition35.section3CosAngleOperator K L
  let V := nuclearTransportDual K L D
  let W := (V.trans Z.symm).trans V.symm
  have hW : (W : E →L[𝕜] E) =
      star (V : E →L[𝕜] E) * star (Z : E →L[𝕜] E) * (V : E →L[𝕜] E) := by
    rw [V.star_eq_symm, Z.star_eq_symm]
    ext x
    rfl
  have hsum : (Z : E →L[𝕜] E) + (W : E →L[𝕜] E) = C + C := by
    rw [hW]
    exact nuclearTransportDual_relative_positive_average K L D Z hfix hself
  have hC : C.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)
  have hstruct := TauCeti.ContinuousLinearMap.unitary_positive_average_structure
    C (Z : E →L[𝕜] E) (W : E →L[𝕜] E) hC
      (Unitary.linearIsometryEquiv.symm Z).property (Unitary.linearIsometryEquiv.symm W).property hsum
  refine ⟨hstruct.1.symm, ?_⟩
  intro x hx
  have hsupport := TauCeti.ContinuousLinearMap.unitary_positive_average_adjoint_on_support
    C (Z : E →L[𝕜] E) (W : E →L[𝕜] E) hC
      (Unitary.linearIsometryEquiv.symm Z).property (Unitary.linearIsometryEquiv.symm W).property hsum x hx
  rw [W.star_eq_symm] at hsupport
  change Z x = V.symm (Z (V x)) at hsupport
  have h := congrArg V hsupport
  rw [V.apply_symm_apply] at h
  exact h.symm

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **No unequal-angle mixing for any Hilbert nuclear optimizer.**
Every globally minimizing ambient complex transporter commutes with
the intrinsic cosine, including fixed directions and right-angle
multiplicities. No invariant-block assumption is imposed on T. -/
theorem nuclear_minimizer_comm_cosine_complex
    (K L : Submodule ℂ H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : H ≃ₗᵢ[ℂ] H) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ W : H ≃ₗᵢ[ℂ] H, K.map W.toLinearMap = L →
      (1 - (T : H →L[ℂ] H)).nuclearENorm ≤ (1 - (W : H →L[ℂ] H)).nuclearENorm) :
    Commute (T : H →L[ℂ] H) (Proposition35.section3CosAngleOperator K L) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (H →L[ℂ] H))
  let Z := R.trans T.symm
  let C := Proposition35.section3CosAngleOperator K L
  let B := nonacuteDirectRotation K L D - C
  let Q := B.ker.starProjection
  have hcert := (nuclear_isMin_iff_certificate_complex K L D hΔ T hT).mp hmin
  have hfix : (1 - (Z : H →L[ℂ] H)) * Q = 0 := by
    ext x
    have hx := B.ker.starProjection_apply_mem x
    change Q x ∈ B.ker at hx
    rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub] at hx
    change K.starProjection (Q x) - L.starProjection (Q x) = 0 at hx
    have hR : R (Q x) = Q x :=
      nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D _ (sub_eq_zero.mp hx)
    have hTQ := hcert.2.1 (Q x) (sub_eq_zero.mp hx)
    have hZQ : Z (Q x) = Q x := by
      apply T.injective
      change T (T.symm (R (Q x))) = T (Q x)
      rw [T.apply_symm_apply, hR, hTQ]
    change Q x - Z (Q x) = 0
    rw [hZQ, sub_self]
  have hpos : (star (nuclearTransportDual K L D : H →L[ℂ] H) *
      (nonacuteDirectRotation K L D - (Z : H →L[ℂ] H))).IsPositive := hcert.2.2
  have hZC := (nuclearTransportDual_relative_cosine_structure K L D Z hfix hpos.isSelfAdjoint).1
  have hC : IsSelfAdjoint C := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hZstar : Commute (star (Z : H →L[ℂ] H)) C := by
    change star (Z : H →L[ℂ] H) * C = C * star (Z : H →L[ℂ] H)
    have h := congrArg star hZC.eq
    rw [star_mul, star_mul] at h
    change star C * star (Z : H →L[ℂ] H) = star (Z : H →L[ℂ] H) * star C at h
    simpa only [hC.star_eq] using h.symm
  have hfactor : (T : H →L[ℂ] H) = (R : H →L[ℂ] H) * star (Z : H →L[ℂ] H) := by
    rw [Z.star_eq_symm]
    ext x
    change T x = R (R.symm (T x))
    exact (R.apply_symm_apply _).symm
  rw [hfactor]
  exact (Proposition35.nonacuteDirectRotation_comm_cosine K L D).mul_left hZstar

/-- Every Hilbert nuclear optimizer also preserves the intrinsic sine;
thus all principal-angle spectral spaces are reducing for the optimizer. -/
theorem nuclear_minimizer_comm_sinAngleOperator_complex
    (K L : Submodule ℂ H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : H ≃ₗᵢ[ℂ] H) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ W : H ≃ₗᵢ[ℂ] H, K.map W.toLinearMap = L →
      (1 - (T : H →L[ℂ] H)).nuclearENorm ≤ (1 - (W : H →L[ℂ] H)).nuclearENorm) :
    Commute (T : H →L[ℂ] H) (K.sinAngleOperator L) :=
  Proposition35.commute_sinAngleOperator_of_commute_section3CosAngleOperator K L T
    (nuclear_minimizer_comm_cosine_complex K L D hΔ T hT hmin)

end Complex

end TauCeti.DavisKahan
