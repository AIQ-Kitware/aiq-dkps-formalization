/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearRootAntipode
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-!
# Every Schatten cost of a nuclear optimizer

All nuclear optimizers have the same Schatten-q displacement for every
finite q at least one. The exact factor relative to the projection
difference is 2^(1-1/q). The statement includes infinite gauge values
for constructed roots; the all-optimizer theorem retains finite native
nuclear projection difference and balanced crossed defects.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The displacement gauge of a reconstructed root is exactly that
of its positive modulus split, for every symmetric ideal family. -/
theorem nuclearSignedSineTransport_gauge_displacement
    (Φ : SymmetricOperatorIdealFamily 𝕜)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L)) :
    Φ.gauge (1 - (nuclearSignedSineTransport K L D A hA hmod hcomm : E →L[𝕜] E)) =
      Φ.gauge (K.sinAngleOperator L - A) := by
  let Ψ := Φ.toOperatorIdealFamily
  let T := nuclearSignedSineTransport K L D A hA hmod hcomm
  let V := nuclearTransportDual K L D
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[𝕜] E))
  have hg : Ψ.gauge (star (V : E →L[𝕜] E) *
      (nonacuteDirectRotation K L D - (T.symm : E →L[𝕜] E) * nonacuteDirectRotation K L D)) =
        Ψ.gauge (1 - (T : E →L[𝕜] E)) := by
    calc
      _ = Ψ.gauge (nonacuteDirectRotation K L D - (T.symm : E →L[𝕜] E) * nonacuteDirectRotation K L D) := by
        rw [V.star_eq_symm]
        exact Ψ.gauge_comp_linearIsometryEquiv_left _ V.symm
      _ = Ψ.gauge ((1 - (T.symm : E →L[𝕜] E)) * (R : E →L[𝕜] E)) := by congr 1
      _ = Ψ.gauge (1 - (T.symm : E →L[𝕜] E)) := Ψ.gauge_comp_linearIsometryEquiv_right _ R
      _ = _ := by
        have h := Φ.gauge_adjoint (1 - (T : E →L[𝕜] E))
        change Ψ.gauge (star (1 - (T : E →L[𝕜] E))) = _ at h
        rwa [star_sub, star_one, T.star_eq_symm] at h
  rw [nuclearSignedSineTransport_dual_displacement] at hg
  exact hg.symm

/-- The exact scaled Schatten power identity of every reconstructed
reflection-odd root, over either field and including infinite costs. -/
theorem nuclearSignedSineTransport_schatten_power
    (q : ℝ) (hq : 1 ≤ q)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L))
    (hodd : K.reflection.conjStarAlgEquiv A = -A) :
    2 * (OperatorIdealFamily.schatten 𝕜 q hq).gauge
      (1 - (nuclearSignedSineTransport K L D A hA hmod hcomm : E →L[𝕜] E)) ^ q =
        (2 * (OperatorIdealFamily.schatten 𝕜 q hq).gauge (K.starProjection - L.starProjection)) ^ q := by
  let Φ := OperatorIdealFamily.schatten 𝕜 q hq
  have hc := nuclearSignedSineTransport_gauge_displacement (SymmetricOperatorIdealFamily.schatten 𝕜 q hq)
    K L D A hA hmod hcomm
  change (SymmetricOperatorIdealFamily.schatten 𝕜 q hq).toOperatorIdealFamily.gauge _ =
    (SymmetricOperatorIdealFamily.schatten 𝕜 q hq).toOperatorIdealFamily.gauge _ at hc
  rw [SymmetricOperatorIdealFamily.schatten_toOperatorIdealFamily] at hc
  have hneg : K.reflection.conjStarAlgEquiv (-A) = -(-A) := by rw [map_neg, hodd]
  have hs := ContinuousLinearMap.gauge_schatten_rpow_modulus_add_of_unitary_odd q hq (-A) hA.neg K.reflection hneg
  rw [ContinuousLinearMap.modulus_neg, hmod, ← sub_eq_add_neg, smul_neg, Φ.gauge_neg] at hs
  have hAg : Φ.gauge A = Φ.gauge (K.starProjection - L.starProjection) := by
    calc
      _ = Φ.gauge A.modulus := by
        simp only [Φ, OperatorIdealFamily.gauge_schatten, ContinuousLinearMap.singularValue_modulus]
      _ = _ := by
        rw [hmod, Submodule.sinAngleOperator_def]
        simp only [Φ, OperatorIdealFamily.gauge_schatten, ContinuousLinearMap.singularValue_modulus]
  rw [Φ.gauge_smul, ← ofReal_norm, RCLike.norm_two, ENNReal.ofReal_ofNat, hAg, ← hc] at hs
  exact hs.symm

/-- **Exact Schatten profile of an admissible nuclear root.** The
factor is 2^(1-1/q), uniformly in angles, multiplicities and dimension.
This generic theorem allows infinite values and needs no trace-class
hypothesis; existence of an admissible real root remains explicit. -/
theorem nuclearSignedSineTransport_schatten_profile
    (q : ℝ) (hq : 1 ≤ q)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : E →L[𝕜] E) *
      Proposition35.section3CosAngleOperator K L))
    (hodd : K.reflection.conjStarAlgEquiv A = -A) :
    (OperatorIdealFamily.schatten 𝕜 q hq).gauge
      (1 - (nuclearSignedSineTransport K L D A hA hmod hcomm : E →L[𝕜] E)) =
        (2 : ℝ≥0∞) ^ (1 - 1 / q) *
          (OperatorIdealFamily.schatten 𝕜 q hq).gauge (K.starProjection - L.starProjection) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hp := nuclearSignedSineTransport_schatten_power q hq K L D A hA hmod hcomm hodd
  apply ENNReal.rpow_left_injective hq0.ne'
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  have hexp : (1 - 1 / q) * q = q - 1 := by
    rw [sub_mul, one_mul, one_div_mul_cancel hq0.ne']
  have hcoeff : (2 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ (q - 1) = (2 : ℝ≥0∞) ^ q := by
    calc
      _ = (2 : ℝ≥0∞) ^ (1 + (q - 1)) := by
        rw [ENNReal.rpow_add _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]
      _ = _ := by congr 1; ring
  calc
    _ = (2 * (OperatorIdealFamily.schatten 𝕜 q hq).gauge (K.starProjection - L.starProjection)) ^ q := hp
    _ = (2 : ℝ≥0∞) ^ q * (OperatorIdealFamily.schatten 𝕜 q hq).gauge (K.starProjection - L.starProjection) ^ q :=
      ENNReal.mul_rpow_of_nonneg _ _ hq0.le
    _ = _ := by
      dsimp only
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, hexp, ← mul_assoc, hcoeff]

section Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The operator-norm endpoint of the exact nuclear-root profile.
The displacement is twice the projection gap, including right angles. -/
theorem nuclearSignedSineTransport_operatorNorm_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) (hmod : A.modulus = K.sinAngleOperator L)
    (hcomm : Commute A ((nuclearTransportDual K L D : F →L[ℂ] F) *
      Proposition35.section3CosAngleOperator K L))
    (hodd : K.reflection.conjStarAlgEquiv A = -A) :
    ‖1 - (nuclearSignedSineTransport K L D A hA hmod hcomm : F →L[ℂ] F)‖ =
      2 * ‖K.starProjection - L.starProjection‖ := by
  let S := K.sinAngleOperator L
  let Φ := OperatorIdealFamily.opNorm ℂ
  have hS : IsSelfAdjoint S := (K.isPositive_sinAngleOperator L).isSelfAdjoint
  have hSS : S * S = A * A := by
    have h := A.modulus_comp_modulus
    change A.modulus * A.modulus = star A * A at h
    rw [hmod, hA.star_eq] at h
    exact h
  have hAS : Commute A S := by
    change Commute A (K.sinAngleOperator L)
    rw [← hmod]
    apply ContinuousLinearMap.commute_modulus_of_commute
    rw [hA.adjoint_eq]
    exact (Commute.refl A).mul_right (Commute.refl A)
  have hzero : (S + A) * (S - A) = 0 := by
    calc
      _ = S * S - A * A := by noncomm_ring [hAS.eq]
      _ = 0 := by rw [hSS, sub_self]
  have hgram : K.reflection.conjStarAlgEquiv (A.adjoint ∘L A) = (-A).adjoint ∘L (-A) := by
    change K.reflection.conjStarAlgEquiv (star A * A) = star (-A) * (-A)
    rw [map_mul, map_star, hodd]
  have hSj : K.reflection.conjStarAlgEquiv S = S := by
    have h := ContinuousLinearMap.conjStarAlgEquiv_modulus K.reflection hgram
    rw [ContinuousLinearMap.modulus_neg, hmod] at h
    exact h
  have hsameGauge : Φ.gauge (S - A) = Φ.gauge (S + A) := by
    calc
      _ = Φ.gauge (K.reflection.conjStarAlgEquiv (S + A)) := by rw [map_add, hSj, hodd, ← sub_eq_add_neg]
      _ = _ := by
        rw [LinearIsometryEquiv.conjStarAlgEquiv_apply,
          Φ.gauge_comp_linearIsometryEquiv_left, Φ.gauge_comp_linearIsometryEquiv_right]
  have hsame : ‖S - A‖ = ‖S + A‖ := by
    have h := congrArg ENNReal.toReal hsameGauge
    simpa only [Φ, OperatorIdealFamily.gauge_opNorm, toReal_enorm] using h
  have hadd := (hS.add hA).norm_add_eq_max (hS.sub hA) hzero
  have hsum : (S + A) + (S - A) = (2 : ℂ) • S := by rw [two_smul]; abel
  rw [hsum, norm_smul, Complex.norm_two, ← hsame, max_self] at hadd
  have hc := nuclearSignedSineTransport_gauge_displacement (SymmetricOperatorIdealFamily.opNorm ℂ)
    K L D A hA hmod hcomm
  change (SymmetricOperatorIdealFamily.opNorm ℂ).toOperatorIdealFamily.gauge _ =
    (SymmetricOperatorIdealFamily.opNorm ℂ).toOperatorIdealFamily.gauge _ at hc
  rw [SymmetricOperatorIdealFamily.opNorm_toOperatorIdealFamily] at hc
  simp only [OperatorIdealFamily.gauge_opNorm] at hc
  have hcost := congrArg ENNReal.toReal hc
  simp only [toReal_enorm] at hcost
  have hSnorm : ‖S‖ = ‖K.starProjection - L.starProjection‖ := by
    rw [show S = (K.starProjection - L.starProjection).modulus from K.sinAngleOperator_def L,
      ContinuousLinearMap.norm_modulus]
  exact hcost.trans (hadd.symm.trans (congrArg (fun r : ℝ => 2 * r) hSnorm))

/-- **Every complex nuclear optimizer has this entire Schatten profile.**
The competitor was not restricted to principal-angle blocks; the exact
all-optimizer parametrization supplies the root. -/
theorem nuclear_optimizer_schatten_profile_complex
    (q : ℝ) (hq : 1 ≤ q)
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L) :
    (OperatorIdealFamily.schatten ℂ q hq).gauge (1 - (T.val : F →L[ℂ] F)) =
      (2 : ℝ≥0∞) ^ (1 - 1 / q) *
        (OperatorIdealFamily.schatten ℂ q hq).gauge (K.starProjection - L.starProjection) := by
  let e := nuclearSignedSineEquivOptimizers_complex K L D hΔ
  let A := e.symm T
  have hp := (mem_nuclearSignedSineParameters K L D A.val).mp A.property
  have h := nuclearSignedSineTransport_schatten_profile q hq K L D A.val hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  change (OperatorIdealFamily.schatten ℂ q hq).gauge (1 - ((e A).val : F →L[ℂ] F)) = _ at h
  have hAT : e A = T := e.apply_symm_apply T
  rwa [hAT] at h

/-- Every complex nuclear optimizer has displacement operator norm
exactly twice the projection gap. -/
theorem nuclear_optimizer_operatorNorm_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L) :
    ‖1 - (T.val : F →L[ℂ] F)‖ = 2 * ‖K.starProjection - L.starProjection‖ := by
  let e := nuclearSignedSineEquivOptimizers_complex K L D hΔ
  let A := e.symm T
  have hp := (mem_nuclearSignedSineParameters K L D A.val).mp A.property
  have h := nuclearSignedSineTransport_operatorNorm_complex K L D A.val hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  change ‖1 - ((e A).val : F →L[ℂ] F)‖ = _ at h
  have hAT : e A = T := e.apply_symm_apply T
  rwa [hAT] at h

/-- A nuclear optimizer is uniformly within the explicit factor
2^(1-1/q) of every ambient competitor's Schatten-q cost. This is a
mathematical comparison guarantee, with no numerical-performance claim. -/
theorem nuclear_optimizer_schatten_comparison_complex
    (q : ℝ) (hq : 1 ≤ q)
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L)
    (W : F ≃ₗᵢ[ℂ] F) (hW : K.map W.toLinearMap = L) :
    (OperatorIdealFamily.schatten ℂ q hq).gauge (1 - (T.val : F →L[ℂ] F)) ≤
      (2 : ℝ≥0∞) ^ (1 - 1 / q) * (OperatorIdealFamily.schatten ℂ q hq).gauge (1 - (W : F →L[ℂ] F)) := by
  rw [nuclear_optimizer_schatten_profile_complex q hq K L D hΔ T]
  simpa only [mul_comm] using mul_le_mul_left
    ((OperatorIdealFamily.schatten ℂ q hq).gauge_projection_sub_le_unitary_displacement K L W hW)
      ((2 : ℝ≥0∞) ^ (1 - 1 / q))

/-- The operator-norm endpoint of the simultaneous comparison guarantee. -/
theorem nuclear_optimizer_operatorNorm_comparison_complex
    (K L : Submodule ℂ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : nuclearTransportOptimizers K L)
    (W : F ≃ₗᵢ[ℂ] F) (hW : K.map W.toLinearMap = L) :
    ‖1 - (T.val : F →L[ℂ] F)‖ ≤ 2 * ‖1 - (W : F →L[ℂ] F)‖ := by
  rw [nuclear_optimizer_operatorNorm_complex K L D hΔ T]
  have h := (OperatorIdealFamily.opNorm ℂ).gauge_projection_sub_le_unitary_displacement K L W hW
  simp only [OperatorIdealFamily.gauge_opNorm] at h
  have hr := ENNReal.toReal_mono (by finiteness : ‖1 - (W : F →L[ℂ] F)‖ₑ ≠ ∞) h
  simp only [toReal_enorm] at hr
  linarith

end Complex

end TauCeti.DavisKahan
