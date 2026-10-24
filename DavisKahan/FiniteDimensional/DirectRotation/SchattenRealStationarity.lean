/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenStationarity
public import ForTauCeti.Analysis.InnerProductSpace.Complexification.Schatten

/-!
# Stationarity under real orthogonal transport variations

Real operators are expressed as operators fixed by the canonical
conjugation on the established complexification. Their Schatten gradient
is reversed by conjugation. Testing only real unitary curves suffices to
make its two source-diagonal compressions vanish.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open TauCeti.RealComplexification
open scoped ENNReal RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

local notation "𝓔" => RealComplexification E

/-- The real transport first variation vanishes in every Hermitian
source-preserving direction that is reversed by conjugation. Multiplication
by `i` turns such a direction into a real skew-adjoint generator. -/
theorem re_trace_gradient_mul_eq_zero_of_isLocalMinOn_real_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (P Q : 𝓔 →L[ℂ] 𝓔) (U : unitary (𝓔 →L[ℂ] 𝓔))
    (hU : conjugateOperator (U : 𝓔 →L[ℂ] 𝓔) = U)
    (htrans : (U : 𝓔 →L[ℂ] 𝓔) * P * star (U : 𝓔 →L[ℂ] 𝓔) = Q)
    (hmin : IsLocalMinOn
      (fun W : 𝓔 →L[ℂ] 𝓔 => UnitarilyInvariantSeminorm.schatten ℂ 𝓔 𝓔 p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (𝓔 →L[ℂ] 𝓔) ∧ W * P * star W = Q ∧ conjugateOperator W = W}
      (U : 𝓔 →L[ℂ] 𝓔))
    (H : 𝓔 →L[ℂ] 𝓔) (hH : IsSelfAdjoint H) (hHP : Commute H P)
    (hHJ : conjugateOperator H = -H) :
    (LinearMap.trace ℂ 𝓔
      (schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔) * H).toLinearMap).re = 0 := by
  let +nondep : NormedAlgebra ℚ (𝓔 →L[ℂ] 𝓔) := .restrictScalars ℚ ℂ _
  let V : ℝ → 𝓔 →L[ℂ] 𝓔 := fun t => NormedSpace.exp ((t : ℂ) • (Complex.I • H))
  let a : ℝ → 𝓔 →L[ℂ] 𝓔 := fun t => (U : 𝓔 →L[ℂ] 𝓔) * V t
  have hVunit (t : ℝ) : V t ∈ unitary (𝓔 →L[ℂ] 𝓔) := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  have hVP (t : ℝ) : Commute (V t) P :=
    ((hHP.smul_left Complex.I).smul_left (t : ℂ)).exp_left
  have ha0 : a 0 = (U : 𝓔 →L[ℂ] 𝓔) := by
    simp only [a, V, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]
  have hfeasible (t : ℝ) : a t ∈
      {W | W ∈ unitary (𝓔 →L[ℂ] 𝓔) ∧ W * P * star W = Q ∧ conjugateOperator W = W} := by
    refine ⟨mul_mem U.2 (hVunit t), ?_, ?_⟩
    · change ((U : 𝓔 →L[ℂ] 𝓔) * V t) * P *
        star ((U : 𝓔 →L[ℂ] 𝓔) * V t) = Q
      rw [star_mul]
      calc
        _ = (U : 𝓔 →L[ℂ] 𝓔) * (V t * P) * star (V t) *
            star (U : 𝓔 →L[ℂ] 𝓔) := by simp only [mul_assoc]
        _ = (U : 𝓔 →L[ℂ] 𝓔) * (P * V t) * star (V t) *
            star (U : 𝓔 →L[ℂ] 𝓔) := by rw [(hVP t).eq]
        _ = (U : 𝓔 →L[ℂ] 𝓔) * P * (V t * star (V t)) *
            star (U : 𝓔 →L[ℂ] 𝓔) := by simp only [mul_assoc]
        _ = Q := by rw [(Unitary.mem_iff.mp (hVunit t)).2, mul_one, htrans]
    · change conjugateOperator ((U : 𝓔 →L[ℂ] 𝓔) * V t) = _
      rw [conjugateOperator_mul, hU, conjugateOperator_exp,
        conjugateOperator_complex_smul, conjugateOperator_complex_smul,
        Complex.conj_ofReal, Complex.conj_I, hHJ]
      simp only [neg_smul, smul_neg, neg_neg]
      rfl
  have ha : Continuous a := by
    exact continuous_const.mul (NormedSpace.exp_continuous.comp
      (Complex.continuous_ofReal.smul continuous_const))
  have hmin' := hmin
  rw [← ha0] at hmin'
  have hcurve := hmin'.comp_continuousOn
    (s := Set.univ) (fun t _ => hfeasible t) ha.continuousOn (Set.mem_univ 0)
  rw [isLocalMinOn_univ_iff] at hcurve
  exact re_trace_schattenUnitaryGradient_mul_eq_zero_of_isLocalMin p hp hp1 U H hH hcurve

private theorem real_projection_compression_eq_zero
    (G P : 𝓔 →L[ℂ] 𝓔) (hG : IsSelfAdjoint G) (hP : IsStarProjection P)
    (hGJ : conjugateOperator G = -G) (hPJ : conjugateOperator P = P)
    (hzero : ∀ H : 𝓔 →L[ℂ] 𝓔, IsSelfAdjoint H → Commute H P →
      conjugateOperator H = -H →
      (LinearMap.trace ℂ 𝓔 (G * H).toLinearMap).re = 0) : P * G * P = 0 := by
  let H := P * G * P
  have hHs : IsSelfAdjoint H := hG.conjugate_self hP.isSelfAdjoint
  have hHP : Commute H P := by
    change (P * G * P) * P = P * (P * G * P)
    simp only [mul_assoc, hP.isIdempotentElem.eq, hP.isIdempotentElem.mul_self_mul]
  have hHJ : conjugateOperator H = -H := by
    simp only [H, conjugateOperator_mul, hPJ, hGJ, mul_neg, neg_mul]
  apply ContinuousLinearMap.eq_zero_of_re_trace_adjoint_mul_self_eq_zero H
  have htrace := ContinuousLinearMap.trace_compression_mul_eq_trace_adjoint_square G P hG hP
  have hswap : LinearMap.trace ℂ 𝓔 (G * H).toLinearMap =
      LinearMap.trace ℂ 𝓔 (H * G).toLinearMap := by
    simp only [ContinuousLinearMap.toLinearMap_mul]
    exact LinearMap.trace_mul_comm ℂ _ _
  rw [← htrace, ← hswap]
  exact hzero H hHs hHP hHJ

/-- Source reflection reverses the Schatten gradient at every local
minimum among actual real unitary transporters. Complex variations are
not assumed to be feasible. -/
theorem gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_real_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (P Q : 𝓔 →L[ℂ] 𝓔) (hP : IsStarProjection P)
    (hPJ : conjugateOperator P = P)
    (U : unitary (𝓔 →L[ℂ] 𝓔))
    (hU : conjugateOperator (U : 𝓔 →L[ℂ] 𝓔) = U)
    (htrans : (U : 𝓔 →L[ℂ] 𝓔) * P * star (U : 𝓔 →L[ℂ] 𝓔) = Q)
    (hmin : IsLocalMinOn
      (fun W : 𝓔 →L[ℂ] 𝓔 => UnitarilyInvariantSeminorm.schatten ℂ 𝓔 𝓔 p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (𝓔 →L[ℂ] 𝓔) ∧ W * P * star W = Q ∧ conjugateOperator W = W}
      (U : 𝓔 →L[ℂ] 𝓔)) :
    ((2 : ℂ) • P - 1) * schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔) *
        ((2 : ℂ) • P - 1) = -schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔) := by
  let G := schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)
  have hG : IsSelfAdjoint G := isSelfAdjoint_schattenUnitaryGradient _ _
  have hGJ : conjugateOperator G = -G :=
    conjugateOperator_schattenUnitaryGradient _ _ hU
  have hstat (H : 𝓔 →L[ℂ] 𝓔) (hH : IsSelfAdjoint H) (hHP : Commute H P)
      (hHJ : conjugateOperator H = -H) :
      (LinearMap.trace ℂ 𝓔 (G * H).toLinearMap).re = 0 :=
    re_trace_gradient_mul_eq_zero_of_isLocalMinOn_real_transports
      p hp hp1 P Q U hU htrans hmin H hH hHP hHJ
  have hdiag := real_projection_compression_eq_zero G P hG hP hGJ hPJ hstat
  have hdiag' := real_projection_compression_eq_zero G (1 - P) hG hP.one_sub hGJ
    (by rw [conjugateOperator_sub, conjugateOperator_one, hPJ])
    (fun H hH hHP hHJ => hstat H hH (by
      have heq := hHP.eq
      simp only [mul_sub, sub_mul, mul_one, one_mul] at heq
      change H * P = P * H
      simpa only [sub_sub_cancel] using congrArg (fun A => H - A) heq) hHJ)
  change ((2 : ℂ) • P - 1) * G * ((2 : ℂ) • P - 1) = -G
  calc
    _ = -G + (P * G * P + P * G * P) +
        ((1 - P) * G * (1 - P) + (1 - P) * G * (1 - P)) := by
      simp only [two_smul]
      noncomm_ring
    _ = -G := by rw [hdiag, hdiag']; simp

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
