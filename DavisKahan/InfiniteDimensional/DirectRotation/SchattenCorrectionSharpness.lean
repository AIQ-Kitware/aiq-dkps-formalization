/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCorrectionDataStability
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseTransport

/-!
# Sharp input conditioning of nearest commuting corrections

A complex two-dimensional equality case for the dimension-free correction
estimate. The diagonal line is fixed and both inputs are genuine unitaries.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open FiniteDimensional.ComplexTraceOptimality
open TauCeti.DavisKahan1970.Section4Examples
open scoped InnerProductSpace ENNReal

private theorem source_projection_zero (x : ComplexPlane) :
    sourceLine.starProjection x 0 = (x 0 + x 1) / 2 :=
  projection_sourceLine_zero x

private theorem source_projection_one (x : ComplexPlane) :
    sourceLine.starProjection x 1 = (x 0 + x 1) / 2 :=
  projection_sourceLine_one x

private theorem source_reflection_zero (x : ComplexPlane) :
    sourceLine.reflection x 0 = x 1 := by
  rw [Submodule.reflection_apply]
  simp only [PiLp.sub_apply, PiLp.smul_apply, source_projection_zero]
  ring

private theorem source_reflection_one (x : ComplexPlane) :
    sourceLine.reflection x 1 = x 0 := by
  rw [Submodule.reflection_apply]
  simp only [PiLp.sub_apply, PiLp.smul_apply, source_projection_one]
  ring

/-- Pinching the canonical planar rotation onto the diagonal line gives
exactly the scalar cosine times identity, for every real angle. -/
theorem diagBlock_scalarPhaseTransport_zero (theta : ℝ) :
    sourceLine.diagBlock (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane) =
      (Real.cos theta : ℂ) • (1 : ComplexPlane →L[ℂ] ComplexPlane) := by
  have h := sourceLine.two_smul_diagBlock
    (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane)
  apply (smul_right_injective (M := ComplexPlane →L[ℂ] ComplexPlane) (by norm_num : (2 : ℂ) ≠ 0))
  rw [← ofNat_smul_eq_nsmul ℂ] at h
  change (2 : ℂ) • sourceLine.diagBlock
    (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane) =
    (2 : ℂ) • ((Real.cos theta : ℂ) • (1 : ComplexPlane →L[ℂ] ComplexPlane))
  rw [h]
  ext x i
  fin_cases i <;>
    simp [source_reflection_zero, source_reflection_one,
      scalarPhaseTransport_apply_zero, scalarPhaseTransport_apply_one, example42Phase,
      Real.cos_neg, Real.sin_neg] <;> ring

/-- The commutator in this equality model is a scalar multiple of an
actual unitary, rather than merely a matrix with a norm upper bound. -/
theorem commutator_scalarPhaseTransport_zero (theta : ℝ) :
    (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
      sourceLine.starProjection * (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane) =
      (Real.sin theta : ℂ) •
        (sourceLine.reflection.trans (scalarPhaseTransport (Real.pi / 2) 0) :
          ComplexPlane →L[ℂ] ComplexPlane) := by
  ext x i
  fin_cases i <;>
    simp [source_projection_zero, source_projection_one,
      source_reflection_zero, source_reflection_one,
      scalarPhaseTransport_apply_zero, scalarPhaseTransport_apply_one, example42Phase,
      Real.cos_neg, Real.sin_neg] <;> ring

/-- Exact commutator norm for the sharpness family. -/
theorem norm_commutator_scalarPhaseTransport_zero (theta : ℝ) :
    ‖(scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
      sourceLine.starProjection * (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ =
      |Real.sin theta| := by
  rw [commutator_scalarPhaseTransport_zero, norm_smul,
    LinearIsometryEquiv.norm_toContinuousLinearMap, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Opposite diagonal polar factors can be reached while preserving the
commutator norm. Their input difference is exactly twice the cosine. -/
theorem scalarPhaseTransport_sub_supplement (theta : ℝ) :
    (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane) -
      (scalarPhaseTransport (Real.pi - theta) 0 : ComplexPlane →L[ℂ] ComplexPlane) =
      (2 * Real.cos theta : ℂ) • (1 : ComplexPlane →L[ℂ] ComplexPlane) := by
  ext x i
  fin_cases i <;>
    simp [scalarPhaseTransport_apply_zero, scalarPhaseTransport_apply_one, example42Phase,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub] <;> ring

private theorem gauge_planar_ne_top (p : ℝ) (hp : 1 ≤ p)
    (T : ComplexPlane →L[ℂ] ComplexPlane) :
    (OperatorIdealFamily.schatten ℂ p hp).gauge T ≠ ∞ := by
  apply OperatorIdealFamily.gauge_schatten_ne_top_of_rank_le p hp T (Module.finrank ℂ ComplexPlane)
  simpa only [Module.finrank_eq_rank] using LinearMap.rank_le_domain T.toLinearMap

private theorem unitary_eq_scalar_factor (c : ℝ) (hc : 0 < c)
    (U : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane) :
    (U : ComplexPlane →L[ℂ] ComplexPlane) =
      ((c : ℂ) • (U : ComplexPlane →L[ℂ] ComplexPlane)).factorThru
        ((c : ℂ) • (U : ComplexPlane →L[ℂ] ComplexPlane)).modulus := by
  apply ContinuousLinearMap.eq_factorThru_modulus_of_unitary_factorization_of_coercive
    _ ((c : ℂ) • (1 : ComplexPlane →L[ℂ] ComplexPlane)) U
    (by simp) (ContinuousLinearMap.isPositive_one.smul_of_nonneg
      (RCLike.ofReal_nonneg.mpr hc.le)) c hc
  intro x
  change c * ‖x‖ ^ 2 ≤ RCLike.re ⟪(c : ℂ) • x, x⟫_ℂ
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- Both inputs in the equality model have the claimed global nearest
commuting corrections, including at the exact critical angle. -/
theorem planar_nearest_schatten_corrections
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (theta : ℝ) (hθ : theta ∈ Set.Icc 0 (criticalAngle p.toReal)) :
    IsMinOn (fun W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane =>
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        ((scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane) -
          (W : ComplexPlane →L[ℂ] ComplexPlane)))
      {W | Commute (W : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection}
      (LinearIsometryEquiv.refl ℂ ComplexPlane) ∧
    IsMinOn (fun W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane =>
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        ((scalarPhaseTransport (Real.pi - theta) 0 : ComplexPlane →L[ℂ] ComplexPlane) -
          (W : ComplexPlane →L[ℂ] ComplexPlane)))
      {W | Commute (W : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection}
      (LinearIsometryEquiv.neg ℂ) := by
  have hcrit := criticalAngle_mem p.toReal hp1 hp2
  have hθpi : theta < Real.pi / 2 := hθ.2.trans_lt hcrit.2
  have hcos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθpi⟩
  have hsin : 0 ≤ Real.sin theta := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos])
  have hsinle : Real.sin theta ≤ Real.sin (criticalAngle p.toReal) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos, hθ.1]) hcrit.2.le hθ.2
  have hnorm : ‖(scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane) *
      sourceLine.starProjection - sourceLine.starProjection *
      (scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ ≤
      Real.sin (criticalAngle p.toReal) := by
    rw [norm_commutator_scalarPhaseTransport_zero, abs_of_nonneg hsin]
    exact hsinle
  have hnormB : ‖(scalarPhaseTransport (Real.pi - theta) 0 : ComplexPlane →L[ℂ] ComplexPlane) *
      sourceLine.starProjection - sourceLine.starProjection *
      (scalarPhaseTransport (Real.pi - theta) 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ ≤
      Real.sin (criticalAngle p.toReal) := by
    rw [norm_commutator_scalarPhaseTransport_zero, Real.sin_pi_sub, abs_of_nonneg hsin]
    exact hsinle
  constructor
  · apply ((schatten_correction_isMin_iff_eq_diagBlock_factorThru_modulus p hp hp1 hp2
      sourceLine (scalarPhaseTransport theta 0) (gauge_planar_ne_top _ hp1.le _) hnorm
      (LinearIsometryEquiv.refl ℂ ComplexPlane)).mpr ?_).2
    rw [diagBlock_scalarPhaseTransport_zero]
    exact unitary_eq_scalar_factor _ hcos (LinearIsometryEquiv.refl ℂ ComplexPlane)
  · apply ((schatten_correction_isMin_iff_eq_diagBlock_factorThru_modulus p hp hp1 hp2
      sourceLine (scalarPhaseTransport (Real.pi - theta) 0) (gauge_planar_ne_top _ hp1.le _) hnormB
      (LinearIsometryEquiv.neg ℂ)).mpr ?_).2
    have hdiag : sourceLine.diagBlock
        (scalarPhaseTransport (Real.pi - theta) 0 : ComplexPlane →L[ℂ] ComplexPlane) =
        (Real.cos theta : ℂ) • ((LinearIsometryEquiv.neg ℂ : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane) : ComplexPlane →L[ℂ] ComplexPlane) := by
      rw [diagBlock_scalarPhaseTransport_zero, Real.cos_pi_sub]
      ext x
      simp
    rw [hdiag]
    exact unitary_eq_scalar_factor _ hcos (LinearIsometryEquiv.neg ℂ)

/-- The exact input distance in the equality model is twice the cosine. -/
theorem norm_scalarPhaseTransport_sub_supplement (theta : ℝ)
    (hcos : 0 ≤ Real.cos theta) :
    ‖(scalarPhaseTransport theta 0 : ComplexPlane →L[ℂ] ComplexPlane) -
      (scalarPhaseTransport (Real.pi - theta) 0 : ComplexPlane →L[ℂ] ComplexPlane)‖ =
      2 * Real.cos theta := by
  rw [scalarPhaseTransport_sub_supplement, norm_smul, norm_one, mul_one, norm_mul]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcos]
  norm_num

private theorem norm_refl_sub_neg :
    ‖(LinearIsometryEquiv.refl ℂ ComplexPlane : ComplexPlane →L[ℂ] ComplexPlane) -
      ((LinearIsometryEquiv.neg ℂ : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane) : ComplexPlane →L[ℂ] ComplexPlane)‖ = 2 := by
  have h : (LinearIsometryEquiv.refl ℂ ComplexPlane : ComplexPlane →L[ℂ] ComplexPlane) -
      ((LinearIsometryEquiv.neg ℂ : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane) : ComplexPlane →L[ℂ] ComplexPlane) =
      (2 : ℂ) • (1 : ComplexPlane →L[ℂ] ComplexPlane) := by
    ext x
    simp [two_smul]
  rw [h, norm_smul, norm_one, mul_one]
  norm_num

/-- Every angle in the closed canonical regime attains the correction
Lipschitz constant `1/cos(theta)`. All four maps are actual unitaries;
both corrections minimize over every ambient commuting competitor. -/
theorem exists_nearest_schatten_corrections_attaining_cosine_ratio
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (theta : ℝ) (hθ : theta ∈ Set.Icc 0 (criticalAngle p.toReal)) :
    let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
    ∃ A B C D : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane,
      Commute (C : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection ∧
      Commute (D : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection ∧
      Φ.gauge ((A : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (A : ComplexPlane →L[ℂ] ComplexPlane)) ≠ ∞ ∧
      Φ.gauge ((B : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (B : ComplexPlane →L[ℂ] ComplexPlane)) ≠ ∞ ∧
      ‖(A : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (A : ComplexPlane →L[ℂ] ComplexPlane)‖ = Real.sin theta ∧
      ‖(B : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (B : ComplexPlane →L[ℂ] ComplexPlane)‖ = Real.sin theta ∧
      IsMinOn (fun W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane =>
        Φ.gauge ((A : ComplexPlane →L[ℂ] ComplexPlane) - (W : ComplexPlane →L[ℂ] ComplexPlane)))
        {W | Commute (W : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection} C ∧
      IsMinOn (fun W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane =>
        Φ.gauge ((B : ComplexPlane →L[ℂ] ComplexPlane) - (W : ComplexPlane →L[ℂ] ComplexPlane)))
        {W | Commute (W : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection} D ∧
      0 < ‖(A : ComplexPlane →L[ℂ] ComplexPlane) - (B : ComplexPlane →L[ℂ] ComplexPlane)‖ ∧
      ‖(C : ComplexPlane →L[ℂ] ComplexPlane) - (D : ComplexPlane →L[ℂ] ComplexPlane)‖ =
        (1 / Real.cos theta) *
          ‖(A : ComplexPlane →L[ℂ] ComplexPlane) - (B : ComplexPlane →L[ℂ] ComplexPlane)‖ := by
  have hcrit := criticalAngle_mem p.toReal hp1 hp2
  have hθpi : theta < Real.pi / 2 := hθ.2.trans_lt hcrit.2
  have hcos : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθpi⟩
  have hsin : 0 ≤ Real.sin theta :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos])
  obtain ⟨hminA, hminB⟩ := planar_nearest_schatten_corrections p hp hp1 hp2 theta hθ
  refine ⟨scalarPhaseTransport theta 0, scalarPhaseTransport (Real.pi - theta) 0,
    LinearIsometryEquiv.refl ℂ ComplexPlane, LinearIsometryEquiv.neg ℂ,
    ?_, ?_, gauge_planar_ne_top _ hp1.le _, gauge_planar_ne_top _ hp1.le _,
    ?_, ?_, hminA, hminB, ?_, ?_⟩
  · change (1 : ComplexPlane →L[ℂ] ComplexPlane) * _ = _ * 1
    simp
  · change (-1 : ComplexPlane →L[ℂ] ComplexPlane) * _ = _ * (-1)
    exact (Commute.neg_one_left sourceLine.starProjection).eq
  · rw [norm_commutator_scalarPhaseTransport_zero, abs_of_nonneg hsin]
  · rw [norm_commutator_scalarPhaseTransport_zero, Real.sin_pi_sub, abs_of_nonneg hsin]
  · rw [norm_scalarPhaseTransport_sub_supplement theta hcos.le]
    positivity
  · rw [norm_refl_sub_neg, norm_scalarPhaseTransport_sub_supplement theta hcos.le]
    field_simp

/-- The full commutator-conditioned constant `1/sqrt(1-gamma^2)`
is attained for every admissible commutator budget, including zero and
the critical endpoint, by actual global minimizers in dimension two. -/
theorem exists_nearest_schatten_corrections_attaining_commutator_ratio
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (gamma : ℝ) (hgamma : gamma ∈ Set.Icc 0 (Real.sin (criticalAngle p.toReal))) :
    let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
    ∃ A B C D : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane,
      Commute (C : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection ∧
      Commute (D : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection ∧
      Φ.gauge ((A : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (A : ComplexPlane →L[ℂ] ComplexPlane)) ≠ ∞ ∧
      Φ.gauge ((B : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (B : ComplexPlane →L[ℂ] ComplexPlane)) ≠ ∞ ∧
      ‖(A : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (A : ComplexPlane →L[ℂ] ComplexPlane)‖ = gamma ∧
      ‖(B : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (B : ComplexPlane →L[ℂ] ComplexPlane)‖ = gamma ∧
      IsMinOn (fun W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane =>
        Φ.gauge ((A : ComplexPlane →L[ℂ] ComplexPlane) - (W : ComplexPlane →L[ℂ] ComplexPlane)))
        {W | Commute (W : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection} C ∧
      IsMinOn (fun W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane =>
        Φ.gauge ((B : ComplexPlane →L[ℂ] ComplexPlane) - (W : ComplexPlane →L[ℂ] ComplexPlane)))
        {W | Commute (W : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection} D ∧
      0 < ‖(A : ComplexPlane →L[ℂ] ComplexPlane) - (B : ComplexPlane →L[ℂ] ComplexPlane)‖ ∧
      ‖(C : ComplexPlane →L[ℂ] ComplexPlane) - (D : ComplexPlane →L[ℂ] ComplexPlane)‖ =
        (1 / Real.sqrt (1 - gamma ^ 2)) *
          ‖(A : ComplexPlane →L[ℂ] ComplexPlane) - (B : ComplexPlane →L[ℂ] ComplexPlane)‖ := by
  have hcrit := criticalAngle_mem p.toReal hp1 hp2
  have hupper : Real.arcsin gamma ≤ criticalAngle p.toReal := by
    have h := Real.arcsin_le_arcsin hgamma.2
    rw [Real.arcsin_sin (by linarith [hcrit.1, Real.pi_pos]) hcrit.2.le] at h
    exact h
  have h := exists_nearest_schatten_corrections_attaining_cosine_ratio p hp hp1 hp2
    (Real.arcsin gamma) ⟨Real.arcsin_nonneg.mpr hgamma.1, hupper⟩
  simpa only [Real.sin_arcsin (by linarith [hgamma.1])
    (hgamma.2.trans (Real.sin_le_one _)), Real.cos_arcsin] using h

/-- The endpoint constant `p/(2-p)` is attained already in complex
Hilbert dimension two. Native membership, exact critical commutator
norms, feasibility and global minimizing properties are all included. -/
theorem exists_nearest_schatten_corrections_attaining_critical_ratio
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2) :
    let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
    ∃ A B C D : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane,
      Commute (C : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection ∧
      Commute (D : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection ∧
      Φ.gauge ((A : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (A : ComplexPlane →L[ℂ] ComplexPlane)) ≠ ∞ ∧
      Φ.gauge ((B : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (B : ComplexPlane →L[ℂ] ComplexPlane)) ≠ ∞ ∧
      ‖(A : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (A : ComplexPlane →L[ℂ] ComplexPlane)‖ =
        Real.sin (criticalAngle p.toReal) ∧
      ‖(B : ComplexPlane →L[ℂ] ComplexPlane) * sourceLine.starProjection -
        sourceLine.starProjection * (B : ComplexPlane →L[ℂ] ComplexPlane)‖ =
        Real.sin (criticalAngle p.toReal) ∧
      IsMinOn (fun W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane =>
        Φ.gauge ((A : ComplexPlane →L[ℂ] ComplexPlane) - (W : ComplexPlane →L[ℂ] ComplexPlane)))
        {W | Commute (W : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection} C ∧
      IsMinOn (fun W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane =>
        Φ.gauge ((B : ComplexPlane →L[ℂ] ComplexPlane) - (W : ComplexPlane →L[ℂ] ComplexPlane)))
        {W | Commute (W : ComplexPlane →L[ℂ] ComplexPlane) sourceLine.starProjection} D ∧
      0 < ‖(A : ComplexPlane →L[ℂ] ComplexPlane) - (B : ComplexPlane →L[ℂ] ComplexPlane)‖ ∧
      ‖(C : ComplexPlane →L[ℂ] ComplexPlane) - (D : ComplexPlane →L[ℂ] ComplexPlane)‖ =
        p.toReal / (2 - p.toReal) *
          ‖(A : ComplexPlane →L[ℂ] ComplexPlane) - (B : ComplexPlane →L[ℂ] ComplexPlane)‖ := by
  have hcrit := criticalAngle_mem p.toReal hp1 hp2
  have h := exists_nearest_schatten_corrections_attaining_cosine_ratio p hp hp1 hp2
    (criticalAngle p.toReal) ⟨hcrit.1.le, le_rfl⟩
  simpa only [cos_criticalAngle _ hp1 hp2, one_div_div] using h

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
