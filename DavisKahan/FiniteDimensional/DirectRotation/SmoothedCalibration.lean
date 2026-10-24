/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCanonicalOptimality

/-!
# Choosing the smoothing scale from principal angles

The exact canonical cutoff can be inverted: an acute angle `theta` is
canonical exactly when the smoothing scale is at least
`(1 - cos theta) / sqrt (cos theta)`. The global endpoint applies this test
to the accepted principal angles and all ambient complex unitary competitors.
This is a parameter-selection consequence of the exact minimum theorem,
not a separate priority claim.
-/

noncomputable section
namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

/-- The exact positive-cosine smoothing threshold for canonical transport. -/
def canonicalSmoothingThreshold (theta : ℝ) : ℝ :=
  (1 - Real.cos theta) / Real.sqrt (Real.cos theta)

/-- The angle criterion can be inverted to choose the smoothing parameter. -/
theorem canonical_cutoff_iff_smoothing_threshold (tau theta : ℝ) (htau : 0 < tau)
    (hcos : 0 < Real.cos theta) :
    ((smoothingRadius tau)⁻¹) ^ 2 ≤ Real.cos theta ↔
      canonicalSmoothingThreshold theta ≤ tau := by
  let a := smoothingRadius tau
  let b := a⁻¹
  let x := Real.sqrt (Real.cos theta)
  have ha : 0 < a := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hb : 0 < b := inv_pos.mpr ha
  have hx : 0 < x := Real.sqrt_pos.mpr hcos
  have hxsq : x ^ 2 = Real.cos theta := Real.sq_sqrt hcos.le
  have hab : a * b = 1 := mul_inv_cancel₀ ha.ne'
  have hdiff : a - b = tau := smoothingRadius_sub_inv tau htau
  have hfac : tau * x - (1 - Real.cos theta) = (a * x - 1) * (1 + b * x) := by
    rw [← hdiff, ← hxsq]
    nlinarith only [congrArg (fun t : ℝ => t * x ^ 2) hab]
  have hpos : 0 < 1 + b * x := by positivity
  have hcut : b ^ 2 ≤ Real.cos theta ↔ 1 ≤ a * x := by
    rw [← hxsq, sq_le_sq₀ hb.le hx.le]
    constructor
    · intro h
      have hh := mul_le_mul_of_nonneg_left h ha.le
      rwa [hab] at hh
    · intro h
      have hh := mul_le_mul_of_nonneg_left h hb.le
      nlinarith only [hh, congrArg (fun t : ℝ => t * x) hab]
  change b ^ 2 ≤ Real.cos theta ↔ (1 - Real.cos theta) / x ≤ tau
  rw [hcut, div_le_iff₀ hx]
  constructor
  · intro h
    have hh := mul_nonneg (sub_nonneg.mpr h) hpos.le
    rw [← hfac] at hh
    linarith
  · intro h
    have hh : 0 ≤ (a * x - 1) * (1 + b * x) := by rw [← hfac]; linarith
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hpos).mp hh)

/-- Increasing the smoothing scale preserves the canonical angle regime. -/
theorem canonical_cutoff_mono_smoothing (tau sigma theta : ℝ)
    (htau : 0 < tau) (hts : tau ≤ sigma) (hcos : 0 < Real.cos theta)
    (hcut : ((smoothingRadius tau)⁻¹) ^ 2 ≤ Real.cos theta) :
    ((smoothingRadius sigma)⁻¹) ^ 2 ≤ Real.cos theta := by
  apply (canonical_cutoff_iff_smoothing_threshold sigma theta (htau.trans_le hts) hcos).mpr
  exact ((canonical_cutoff_iff_smoothing_threshold tau theta htau hcos).mp hcut).trans hts


/-- The exact angle cutoff is equivalent to an explicit smoothing-scale test. -/
theorem angle_le_smoothedCriticalAngle_iff_threshold (tau theta : ℝ) (htau : 0 < tau)
    (hθ : theta ∈ Set.Icc 0 Real.pi) (hcos : 0 < Real.cos theta) :
    theta ≤ smoothedCriticalAngle tau ↔ canonicalSmoothingThreshold theta ≤ tau := by
  have hc := smoothedCriticalAngle_mem_Icc tau
  have hcp : smoothedCriticalAngle tau ∈ Set.Icc 0 Real.pi :=
    ⟨hc.1, by linarith [hc.2, Real.pi_pos]⟩
  have hi := Real.strictAntiOn_cos.le_iff_ge hcp hθ
  rw [cos_smoothedCriticalAngle tau htau] at hi
  exact hi.symm.trans (canonical_cutoff_iff_smoothing_threshold tau theta htau hcos)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- For an acute complex subspace pair, the explicit smoothing test decides
canonical global optimality against every ambient unitary transporter. -/
theorem smoothed_canonical_isMin_iff_smoothing_threshold
    (tau : ℝ) (htau : 0 < tau) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (hacute : ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i < Real.pi / 2) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    (∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      smoothedDisplacementCost tau R.toLinearMap ≤ smoothedDisplacementCost tau T.toLinearMap) ↔
      ∀ i : Fin (Module.finrank ℂ U), canonicalSmoothingThreshold (U.principalAngles V i) ≤ tau := by
  have hcan := smoothed_canonical_isMin_iff tau htau U V hUV
  dsimp only at hcan ⊢
  rw [hcan]
  apply forall_congr'
  intro i
  have hnonneg := U.principalAngles_nonneg V i
  have hπ : U.principalAngles V i ≤ Real.pi := by linarith [hacute i, Real.pi_pos]
  have hc : 0 < Real.cos (U.principalAngles V i) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hacute i⟩
  exact angle_le_smoothedCriticalAngle_iff_threshold tau _ htau ⟨hnonneg, hπ⟩ hc

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
