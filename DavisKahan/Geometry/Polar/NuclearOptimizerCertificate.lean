/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearDual
public import DavisKahan.Geometry.Polar.NuclearPhase
public import ForTauCeti.Analysis.OperatorIdeal.Nuclear.Trace

/-!
# Nuclear transport calibration in arbitrary Hilbert dimension

The actual dual defined from completed direct rotation calibrates every
trace-class relative competitor commuting with the source reflection.
All nuclear norms here are native approximation-number sums.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem nuclear_mul_finite (A B : E →L[ℂ] E) (hA : A.nuclearENorm ≠ ∞) :
    (A * B).nuclearENorm ≠ ∞ ∧ (B * A).nuclearENorm ≠ ∞ := by
  constructor
  · have h := ContinuousLinearMap.nuclearENorm_comp_comp_le (1 : E →L[ℂ] E) A B
    change (A * B).nuclearENorm ≤ ‖(1 : E →L[ℂ] E)‖ₑ * A.nuclearENorm * ‖B‖ₑ at h
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) hA) (by finiteness)) h
  · have h := ContinuousLinearMap.nuclearENorm_comp_comp_le B A (1 : E →L[ℂ] E)
    change (B * A).nuclearENorm ≤ ‖B‖ₑ * A.nuclearENorm * ‖(1 : E →L[ℂ] E)‖ₑ at h
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) hA) (by finiteness)) h

/-- **Exact infinite-dimensional nuclear calibration.** The excess of
real dual trace over the sine minimum is precisely half the squared
Hilbert–Schmidt displacement on the full fixed sector. Z may mix all
principal-angle spaces; only source-reflection commutation is assumed. -/
theorem nuclearTransportDual_trace_calibration_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (Z : E ≃ₗᵢ[ℂ] E)
    (hZ : ∀ x, Z (K.reflection x) = K.reflection (Z x))
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (hfinite : (nonacuteDirectRotation K L D - (Z : E →L[ℂ] E)).nuclearENorm ≠ ∞) :
    let R := nonacuteDirectRotation K L D
    let B := R - Proposition35.section3CosAngleOperator K L
    let G := (1 - (Z : E →L[ℂ] E)) * B.ker.starProjection
    (star (nuclearTransportDual K L D : E →L[ℂ] E) *
        (R - (Z : E →L[ℂ] E))).nuclearTrace.re =
      (K.starProjection - L.starProjection).nuclearENorm.toReal +
        G.hilbertSchmidtNorm ^ 2 / 2 := by
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let B := R - C
  let Q := B.ker.starProjection
  let F := B.polarFactor
  let X := R - (Z : E →L[ℂ] E)
  let S := K.sinAngleOperator L
  let G := (1 - (Z : E →L[ℂ] E)) * Q
  have hSnorm : S.nuclearENorm = (K.starProjection - L.starProjection).nuclearENorm := by
    simp only [S, Submodule.sinAngleOperator_def, ContinuousLinearMap.nuclearENorm_def,
      ContinuousLinearMap.singularValue_modulus]
  have hSfinite : S.nuclearENorm ≠ ∞ := by rwa [hSnorm]
  have hBnorm : B.nuclearENorm = S.nuclearENorm := by
    have hmod := Proposition35.modulus_nonacuteDirectRotation_sub_cosine K L D
    have hmod' : B.modulus = S := by
      rw [show S = (K.starProjection - L.starProjection).modulus from K.sinAngleOperator_def L]
      exact hmod
    rw [← hmod', ContinuousLinearMap.nuclearENorm_def, ContinuousLinearMap.nuclearENorm_def]
    simp only [ContinuousLinearMap.singularValue_modulus]
  have hBfinite : B.nuclearENorm ≠ ∞ := by rwa [hBnorm]
  have hCZ : C - (Z : E →L[ℂ] E) = X + -B := by dsimp only [X, B]; abel
  have hCZfinite : (C - (Z : E →L[ℂ] E)).nuclearENorm ≠ ∞ := by
    rw [hCZ]
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨hfinite, by rwa [ContinuousLinearMap.nuclearENorm_neg]⟩)
      (X.nuclearENorm_add_le (-B))
  have hRQ : R * Q = Q := by
    ext x
    exact nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D _
      (by
        have hx := B.ker.starProjection_apply_mem x
        change Q x ∈ B.ker at hx
        rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub] at hx
        change K.starProjection _ - L.starProjection _ = 0 at hx
        exact sub_eq_zero.mp hx)
  have hG : G = X * Q := by
    dsimp only [G, X]
    rw [sub_mul, sub_mul, one_mul, hRQ]
  have hGfinite : G.nuclearENorm ≠ ∞ := by
    rw [hG]
    exact (nuclear_mul_finite X Q hfinite).1
  have hQCZ : Q * (1 - (Z : E →L[ℂ] E)) = Q * (C - (Z : E →L[ℂ] E)) := by
    have hCQ : C * Q = Q := by
      ext x
      exact cosine_apply_eq_self_of_mem_nonacute_skew_ker K L D _
        (B.ker.starProjection_apply_mem x)
    have hC : IsSelfAdjoint C := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
    have h := congrArg star hCQ
    have hQ : IsSelfAdjoint Q := isSelfAdjoint_starProjection B.ker
    have hQC : Q * C = Q := by
      simpa only [star_mul, hC.star_eq, hQ.star_eq] using h
    rw [mul_sub, mul_sub, hQC, mul_one]
  have hQCZfinite := (nuclear_mul_finite _ Q hCZfinite).2
  have hoddFinite := (nuclear_mul_finite _ (star F) hCZfinite).2
  have hCeven : K.reflection.conjStarAlgEquiv C = C := by
    have hc := (K.commute_reflection_iff.mpr
      (Proposition35.section3CosAngleOperator_comm_projection K L).symm).eq
    ext x
    have h := congrArg (fun A : E →L[ℂ] E => A (K.reflection.symm x)) hc
    change K.reflection (C (K.reflection.symm x)) = C (K.reflection (K.reflection.symm x)) at h
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      K.reflection.apply_symm_apply] using h
  have hZeven : K.reflection.conjStarAlgEquiv (Z : E →L[ℂ] E) = (Z : E →L[ℂ] E) := by
    ext x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    change K.reflection (Z (K.reflection.symm x)) = Z x
    rw [← hZ, K.reflection.apply_symm_apply]
  have hFodd : K.reflection.conjStarAlgEquiv F = -F :=
    reflection_conj_polarFactor_nonacuteDirectRotation_sub_cosine K L D
  have hodd : K.reflection.conjStarAlgEquiv (star F * (C - (Z : E →L[ℂ] E))) =
      -(star F * (C - (Z : E →L[ℂ] E))) := by
    rw [map_mul, map_star, map_sub, hFodd, hCeven, hZeven, star_neg, neg_mul]
  have hTrOdd := ContinuousLinearMap.nuclearTrace_eq_zero_of_conjStarAlgEquiv_eq_neg_complex
    _ K.reflection hoddFinite hodd
  have hQCfinite : (Q * (1 - (Z : E →L[ℂ] E))).nuclearENorm ≠ ∞ := by
    rwa [hQCZ]
  have hTrQ : (Q * (1 - (Z : E →L[ℂ] E))).nuclearTrace = G.nuclearTrace := by
    rw [hQCZ, ← ContinuousLinearMap.nuclearTrace_mul_comm_complex _ Q hCZfinite]
    have hCQ : C * Q = Q := by
      ext x
      exact cosine_apply_eq_self_of_mem_nonacute_skew_ker K L D _
        (B.ker.starProjection_apply_mem x)
    congr 1
    dsimp only [G]
    rw [sub_mul, sub_mul, hCQ, one_mul]
  have hsumfinite : (S + Q * (1 - (Z : E →L[ℂ] E))).nuclearENorm ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hSfinite, hQCfinite⟩)
      (S.nuclearENorm_add_le _)
  have hSpos : S.IsPositive := by
    rw [show S = (K.starProjection - L.starProjection).modulus from
      K.sinAngleOperator_def L]
    exact (K.starProjection - L.starProjection).isPositive_modulus
  have hTrS := (ContinuousLinearMap.re_nuclearTrace_eq_nuclearENorm_iff_isPositive_complex
    S hSfinite).mpr hSpos
  have hslack := ContinuousLinearMap.two_mul_re_nuclearTrace_unitary_projection_defect_complex
    Z Q (isStarProjection_starProjection (U := B.ker)) hGfinite
  change 2 * G.nuclearTrace.re = G.hilbertSchmidtNorm ^ 2 at hslack
  change (star (nuclearTransportDual K L D : E →L[ℂ] E) * X).nuclearTrace.re = _
  rw [nuclearTransportDual_adjoint_mul_displacement,
    ContinuousLinearMap.nuclearTrace_add_complex _ _ hsumfinite hoddFinite,
    ContinuousLinearMap.nuclearTrace_add_complex _ _ hSfinite hQCfinite,
    hTrOdd, add_zero, hTrQ, Complex.add_re, hTrS, hSnorm]
  linarith

/-- Every trace-class relative competitor attains the sine bound exactly
when it fixes the whole skew kernel and its dual displacement is positive.
No invariant-angle-block assumption is imposed. -/
theorem nuclear_eq_projection_sub_iff_relative_certificate_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (Z : E ≃ₗᵢ[ℂ] E)
    (hZ : ∀ x, Z (K.reflection x) = K.reflection (Z x))
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (hfinite : (nonacuteDirectRotation K L D - (Z : E →L[ℂ] E)).nuclearENorm ≠ ∞) :
    let R := nonacuteDirectRotation K L D
    let B := R - Proposition35.section3CosAngleOperator K L
    (R - (Z : E →L[ℂ] E)).nuclearENorm =
        (K.starProjection - L.starProjection).nuclearENorm ↔
      (1 - (Z : E →L[ℂ] E)) * B.ker.starProjection = 0 ∧
        (star (nuclearTransportDual K L D : E →L[ℂ] E) *
          (R - (Z : E →L[ℂ] E))).IsPositive := by
  let R := nonacuteDirectRotation K L D
  let B := R - Proposition35.section3CosAngleOperator K L
  let Q := B.ker.starProjection
  let X := R - (Z : E →L[ℂ] E)
  let G := (1 - (Z : E →L[ℂ] E)) * Q
  let Y := star (nuclearTransportDual K L D : E →L[ℂ] E) * X
  let Φ := OperatorIdealFamily.schatten ℂ 1 (by norm_num)
  have hnorm (A : E →L[ℂ] E) : Φ.gauge A = A.nuclearENorm := by
    simp only [Φ, OperatorIdealFamily.gauge_schatten, one_div_one,
      ENNReal.rpow_one, ContinuousLinearMap.nuclearENorm_def]
  have hYnorm : Y.nuclearENorm = X.nuclearENorm := by
    rw [← hnorm Y, ← hnorm X]
    change Φ.gauge (star (nuclearTransportDual K L D : E →L[ℂ] E) * X) = _
    rw [LinearIsometryEquiv.star_eq_symm]
    exact Φ.gauge_comp_linearIsometryEquiv_left X (nuclearTransportDual K L D).symm
  have hYfinite : Y.nuclearENorm ≠ ∞ := by rwa [hYnorm]
  have htrace := nuclearTransportDual_trace_calibration_complex K L D Z hZ hΔ hfinite
  change Y.nuclearTrace.re = (K.starProjection - L.starProjection).nuclearENorm.toReal +
    G.hilbertSchmidtNorm ^ 2 / 2 at htrace
  have hbound : Y.nuclearTrace.re ≤ X.nuclearENorm.toReal := by
    calc
      _ ≤ ‖Y.nuclearTrace‖ := Complex.re_le_norm _
      _ ≤ Y.nuclearENorm.toReal := ContinuousLinearMap.norm_nuclearTrace_le_nuclearENorm_complex Y hYfinite
      _ = _ := congrArg ENNReal.toReal hYnorm
  have hpos := ContinuousLinearMap.re_nuclearTrace_eq_nuclearENorm_iff_isPositive_complex Y hYfinite
  rw [hYnorm] at hpos
  have hRQ : R * Q = Q := by
    ext x
    apply nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D
    have hx := B.ker.starProjection_apply_mem x
    change Q x ∈ B.ker at hx
    rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub] at hx
    change K.starProjection _ - L.starProjection _ = 0 at hx
    exact sub_eq_zero.mp hx
  have hGfinite : G.nuclearENorm ≠ ∞ := by
    have hG : G = X * Q := by
      dsimp only [G, X]
      rw [sub_mul, sub_mul, one_mul, hRQ]
    rw [hG]
    exact (nuclear_mul_finite X Q hfinite).1
  have hslack := ContinuousLinearMap.two_mul_re_nuclearTrace_unitary_projection_defect_complex
    Z Q (isStarProjection_starProjection (U := B.ker)) hGfinite
  change 2 * G.nuclearTrace.re = G.hilbertSchmidtNorm ^ 2 at hslack
  have hzero := (ContinuousLinearMap.re_nuclearTrace_unitary_projection_defect_nonneg_and_eq_zero_iff_complex
    Z Q (isStarProjection_starProjection (U := B.ker)) hGfinite).2
  change G.nuclearTrace.re = 0 ↔ G = 0 at hzero
  change X.nuclearENorm = _ ↔ G = 0 ∧ Y.IsPositive
  constructor
  · intro hcost
    have heq := congrArg ENNReal.toReal hcost
    have hGzero : G.nuclearTrace.re = 0 := by nlinarith [sq_nonneg G.hilbertSchmidtNorm]
    exact ⟨hzero.mp hGzero, hpos.mp (by linarith)⟩
  · rintro ⟨hfix, hpositive⟩
    have hGzero := hzero.mpr hfix
    have hsaturate := hpos.mpr hpositive
    apply (ENNReal.toReal_eq_toReal_iff' hfinite hΔ).mp
    linarith

/-- **Every nuclear optimizer, in arbitrary complex Hilbert dimension.**
For a trace-class projection difference and balanced crossed defects,
an ambient transporter is globally optimal exactly when its displacement
is trace class, it fixes every vector on which the projections agree,
and its actual dual displacement is positive. The competing unitary is
otherwise unrestricted, and may have infinite nuclear cost. -/
theorem nuclear_isMin_iff_certificate_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L) :
    let R := nonacuteDirectRotation K L D
    (∀ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L →
      (1 - (T : E →L[ℂ] E)).nuclearENorm ≤ (1 - (W : E →L[ℂ] E)).nuclearENorm) ↔
      (1 - (T : E →L[ℂ] E)).nuclearENorm ≠ ∞ ∧
        (∀ x, K.starProjection x = L.starProjection x → T x = x) ∧
          (star (nuclearTransportDual K L D : E →L[ℂ] E) *
            (R - (T.symm : E →L[ℂ] E) * R)).IsPositive := by
  let Φ := OperatorIdealFamily.schatten ℂ 1 (by norm_num)
  have hnorm (A : E →L[ℂ] E) : Φ.gauge A = A.nuclearENorm := by
    simp only [Φ, OperatorIdealFamily.gauge_schatten, one_div_one,
      ENNReal.rpow_one, ContinuousLinearMap.nuclearENorm_def]
  let W := nuclearPhaseRotation_complex K L D
  have hWmap : K.map W.toLinearMap = L := nuclearPhaseRotation_map_complex K L D
  have hWcost : (1 - (W : E →L[ℂ] E)).nuclearENorm =
      (K.starProjection - L.starProjection).nuclearENorm := by
    rw [← hnorm _, ← hnorm _]
    exact gauge_nuclear_nuclearPhaseRotation_complex K L D
  have hbound (U : E ≃ₗᵢ[ℂ] E) (hU : K.map U.toLinearMap = L) :
      (K.starProjection - L.starProjection).nuclearENorm ≤
        (1 - (U : E →L[ℂ] E)).nuclearENorm := by
    rw [← hWcost, ← hnorm _, ← hnorm _]
    exact nuclearPhaseRotation_isMin_complex K L D U hU
  have hminiff : (∀ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L →
      (1 - (T : E →L[ℂ] E)).nuclearENorm ≤ (1 - (U : E →L[ℂ] E)).nuclearENorm) ↔
      (1 - (T : E →L[ℂ] E)).nuclearENorm =
        (K.starProjection - L.starProjection).nuclearENorm := by
    constructor
    · intro hmin
      exact le_antisymm ((hmin W hWmap).trans_eq hWcost) (hbound T hT)
    · intro hcost U hU
      rw [hcost]
      exact hbound U hU
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  let Z := R.trans T.symm
  let B := nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L
  let Q := B.ker.starProjection
  have hRref (x : E) : R (K.reflection x) = L.reflection (R x) :=
    nonacuteDirectRotation_reflection_intertwines K L D x
  have hTref := (K.map_eq_iff_intertwines_reflection L T).mp hT
  have hZ (x : E) : Z (K.reflection x) = K.reflection (Z x) := by
    apply T.injective
    change T (T.symm (R (K.reflection x))) = T (K.reflection (T.symm (R x)))
    rw [T.apply_symm_apply, hTref, T.apply_symm_apply, hRref]
  have hfactor : nonacuteDirectRotation K L D - (Z : E →L[ℂ] E) =
      ((T : E →L[ℂ] E) - 1) * (Z : E →L[ℂ] E) := by
    ext x
    change R x - T.symm (R x) = T (T.symm (R x)) - T.symm (R x)
    rw [T.apply_symm_apply]
  have hN : (nonacuteDirectRotation K L D - (Z : E →L[ℂ] E)).nuclearENorm =
      (1 - (T : E →L[ℂ] E)).nuclearENorm := by
    rw [← hnorm _, hfactor]
    change Φ.gauge (((T : E →L[ℂ] E) - 1) ∘L (Z : E →L[ℂ] E)) = _
    rw [Φ.gauge_comp_linearIsometryEquiv_right]
    rw [show (T : E →L[ℂ] E) - 1 = -(1 - (T : E →L[ℂ] E)) from (neg_sub _ _).symm,
      Φ.gauge_neg, hnorm]
  have hfix : (1 - (Z : E →L[ℂ] E)) * Q = 0 ↔
      ∀ x, K.starProjection x = L.starProjection x → T x = x := by
    constructor
    · intro hzero x hx
      have hxker : x ∈ B.ker := by
        rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub]
        change K.starProjection x - L.starProjection x = 0
        exact sub_eq_zero.mpr hx
      have hQx : Q x = x := B.ker.starProjection_eq_self_iff.mpr hxker
      have hZx := congrArg (fun A : E →L[ℂ] E => A x) hzero
      change Q x - Z (Q x) = 0 at hZx
      rw [hQx] at hZx
      have hRx : R x = x := nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D x hx
      have h := congrArg T (sub_eq_zero.mp hZx)
      change T x = T (T.symm (R x)) at h
      rwa [T.apply_symm_apply, hRx] at h
    · intro hfixed
      ext x
      have hx := B.ker.starProjection_apply_mem x
      change Q x ∈ B.ker at hx
      rw [ker_nonacuteDirectRotation_sub_cosine_eq_projection_sub] at hx
      change K.starProjection (Q x) - L.starProjection (Q x) = 0 at hx
      have hR : R (Q x) = Q x :=
        nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D _ (sub_eq_zero.mp hx)
      have hTQ := hfixed (Q x) (sub_eq_zero.mp hx)
      change Q x - Z (Q x) = 0
      apply sub_eq_zero.mpr
      apply T.injective
      change T (Q x) = T (T.symm (R (Q x)))
      rw [T.apply_symm_apply, hR, hTQ]
  rw [hminiff]
  constructor
  · intro hcost
    have hfinite : (1 - (T : E →L[ℂ] E)).nuclearENorm ≠ ∞ := by rwa [hcost]
    have hXfinite : (nonacuteDirectRotation K L D - (Z : E →L[ℂ] E)).nuclearENorm ≠ ∞ := by
      rwa [hN]
    have hcert := nuclear_eq_projection_sub_iff_relative_certificate_complex K L D Z hZ hΔ hXfinite
    dsimp only at hcert
    rw [hN, hfix] at hcert
    exact ⟨hfinite, hcert.mp hcost⟩
  · rintro ⟨hfinite, hfixed, hpositive⟩
    have hXfinite : (nonacuteDirectRotation K L D - (Z : E →L[ℂ] E)).nuclearENorm ≠ ∞ := by
      rwa [hN]
    have hcert := nuclear_eq_projection_sub_iff_relative_certificate_complex K L D Z hZ hΔ hXfinite
    dsimp only at hcert
    rw [hN, hfix] at hcert
    exact hcert.mpr ⟨hfixed, hpositive⟩

/-- Every global nuclear minimizer fixes the entire projection-agreement
sector, including infinite-dimensional common and ambient directions. -/
theorem nuclear_minimizer_apply_eq_self_of_projections_eq_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hΔ : (K.starProjection - L.starProjection).nuclearENorm ≠ ∞)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L →
      (1 - (T : E →L[ℂ] E)).nuclearENorm ≤ (1 - (W : E →L[ℂ] E)).nuclearENorm)
    (x : E) (hx : K.starProjection x = L.starProjection x) : T x = x :=
  ((nuclear_isMin_iff_certificate_complex K L D hΔ T hT).mp hmin).2.1 x hx

end TauCeti.DavisKahan
