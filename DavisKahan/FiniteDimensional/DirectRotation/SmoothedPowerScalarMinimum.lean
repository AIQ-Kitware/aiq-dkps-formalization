/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerVariation
public import Mathlib.Topology.Order.Compact

/-!
# Attained scalar minima for smoothed-power transport

The literal planar phase cost has an attained minimum on `[0,theta]` for
`theta>=0`. This definition does not presuppose a critical-angle selection
formula or uniqueness of the minimizing phase. Those are separate results.
The interval is empty for negative theta, where no optimization claim is made.

Compact attainment, norm-power convexity and their scalar comparisons are
classical ingredients. The generalized Charbonnier penalty is prior art;
see S13 in the unification/provenance note. This module is the scalar input
for C1b, not the full C2 minimizing-phase law.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set

/-- The normalized generalized Charbonnier penalty, as a real scalar function. -/
@[expose] def penalty (p tau s : ℝ) : ℝ := (tau ^ 2 + s ^ 2) ^ (p / 2) - tau ^ p

/-- The literal planar cost of the common phase on a principal plane. -/
@[expose] def phaseCost (p tau theta delta : ℝ) : ℝ :=
  smoothedPowerPhaseCost p tau (theta + delta) + smoothedPowerPhaseCost p tau (theta - delta)

/-- The planar minimum on the nonnegative-phase interval. Attainment and
its intended meaning are proved for nonnegative physical angles. -/
@[expose] def phaseMinimum (p tau theta : ℝ) : ℝ :=
  sInf (phaseCost p tau theta '' Icc 0 theta)

private theorem rpow_sq_half (p tau : ℝ) (htau : 0 ≤ tau) :
    (tau ^ 2) ^ (p / 2) = tau ^ p := by
  rw [← Real.rpow_natCast_mul htau]
  congr 1
  ring

/-- Normalization at zero, including the zero-smoothing boundary. -/
theorem penalty_zero (p tau : ℝ) (htau : 0 ≤ tau) : penalty p tau 0 = 0 := by
  simp only [penalty, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  rw [rpow_sq_half p tau htau, sub_self]

theorem penalty_nonneg (p tau s : ℝ) (hp : 0 ≤ p) (htau : 0 ≤ tau) :
    0 ≤ penalty p tau s := by
  unfold penalty
  rw [← rpow_sq_half p tau htau]
  exact sub_nonneg.mpr (Real.rpow_le_rpow (sq_nonneg tau) (by nlinarith [sq_nonneg s])
    (by linarith))

theorem phaseCost_neg (p tau theta delta : ℝ) :
    phaseCost p tau theta (-delta) = phaseCost p tau theta delta := by
  simp only [phaseCost, sub_eq_add_neg, neg_neg, add_comm]

private theorem phase_zero (p tau : ℝ) (htau : 0 ≤ tau) :
    smoothedPowerPhaseCost p tau 0 = 0 := by
  simp only [smoothedPowerPhaseCost, Real.cos_zero, mul_one]
  rw [show tau ^ 2 + 2 - 2 = tau ^ 2 by ring, rpow_sq_half p tau htau, sub_self]

theorem phaseCost_zero_angle (p tau : ℝ) (htau : 0 ≤ tau) : phaseCost p tau 0 0 = 0 := by
  simp only [phaseCost, add_zero, sub_zero, phase_zero p tau htau, add_zero]

private theorem phase_nonneg (p tau t : ℝ) (hp : 0 ≤ p) (htau : 0 ≤ tau) :
    0 ≤ smoothedPowerPhaseCost p tau t := by
  unfold smoothedPowerPhaseCost
  rw [← rpow_sq_half p tau htau]
  exact sub_nonneg.mpr (Real.rpow_le_rpow (sq_nonneg tau)
    (by linarith [Real.cos_le_one t]) (by linarith))

theorem phaseCost_nonneg (p tau theta delta : ℝ) (hp : 0 ≤ p) (htau : 0 ≤ tau) :
    0 ≤ phaseCost p tau theta delta :=
  add_nonneg (phase_nonneg p tau _ hp htau) (phase_nonneg p tau _ hp htau)

private theorem continuous_phaseCost (p tau theta : ℝ) (htau : 0 < tau) :
    Continuous (phaseCost p tau theta) := by
  have hc : Continuous (smoothedPowerPhaseCost p tau) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_smoothedPowerPhaseCost p tau t htau).continuousAt
  exact (hc.comp (continuous_const.add continuous_id)).add
    (hc.comp (continuous_const.sub continuous_id))

/-- Every physical planar minimum is attained, independently of any
uniqueness or phase-transition claim. -/
theorem exists_attains_phaseMinimum (p tau theta : ℝ) (htau : 0 < tau) (hθ : 0 ≤ theta) :
    ∃ delta ∈ Icc 0 theta, phaseMinimum p tau theta = phaseCost p tau theta delta ∧
      IsMinOn (phaseCost p tau theta) (Icc 0 theta) delta := by
  obtain ⟨delta, hdelta, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hθ)
    (continuous_phaseCost p tau theta htau).continuousOn
  refine ⟨delta, hdelta, ?_, hmin⟩
  apply IsLeast.csInf_eq
  refine ⟨mem_image_of_mem _ hdelta, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  exact hmin hd

/-- For nonnegative powers the planar cost is continuous jointly in
smoothing and phase, including at zero smoothing. -/
theorem continuous_phaseCost_smoothing_phase (p theta : ℝ) (hp : 0 ≤ p) :
    Continuous (fun x : ℝ × ℝ => phaseCost p x.1 theta x.2) := by
  unfold phaseCost smoothedPowerPhaseCost
  have ht : Continuous (fun x : ℝ × ℝ => x.1 ^ p) :=
    continuous_fst.rpow_const (fun _ => Or.inr hp)
  have hplus : Continuous (fun x : ℝ × ℝ =>
      x.1 ^ 2 + 2 - 2 * Real.cos (theta + x.2)) :=
    ((continuous_fst.pow 2).add continuous_const).sub
      (continuous_const.mul (Real.continuous_cos.comp (continuous_const.add continuous_snd)))
  have hminus : Continuous (fun x : ℝ × ℝ =>
      x.1 ^ 2 + 2 - 2 * Real.cos (theta - x.2)) :=
    ((continuous_fst.pow 2).add continuous_const).sub
      (continuous_const.mul (Real.continuous_cos.comp (continuous_const.sub continuous_snd)))
  exact ((hplus.rpow_const (fun _ => Or.inr (by linarith : 0 ≤ p / 2))).sub ht).add
    ((hminus.rpow_const (fun _ => Or.inr (by linarith : 0 ≤ p / 2))).sub ht)

/-- Compact scalar attainment extends through the zero-smoothing boundary. -/
theorem exists_attains_phaseMinimum_of_nonneg (p tau theta : ℝ)
    (hp : 0 ≤ p) (hθ : 0 ≤ theta) :
    ∃ delta ∈ Icc 0 theta, phaseMinimum p tau theta = phaseCost p tau theta delta ∧
      IsMinOn (phaseCost p tau theta) (Icc 0 theta) delta := by
  have hc := (continuous_phaseCost_smoothing_phase p theta hp).comp
    (continuous_const.prodMk continuous_id : Continuous (fun d : ℝ => (tau, d)))
  obtain ⟨delta, hdelta, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hθ) hc.continuousOn
  refine ⟨delta, hdelta, ?_, hmin⟩
  apply IsLeast.csInf_eq
  refine ⟨mem_image_of_mem _ hdelta, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  exact hmin hd

/-- Scalar minimum values vary continuously with smoothing. This is
continuity of values, with no assertion about entire optimizer sets. -/
theorem continuous_phaseMinimum_smoothing (p theta : ℝ) (hp : 0 ≤ p) :
    Continuous (fun tau => phaseMinimum p tau theta) :=
  isCompact_Icc.continuous_sInf (continuous_phaseCost_smoothing_phase p theta hp)

/-- The scalar minimum bounds each admissible nonnegative phase. -/
theorem phaseMinimum_le_cost (p tau theta delta : ℝ)
    (hp : 0 ≤ p) (htau : 0 ≤ tau) (hdelta : delta ∈ Icc 0 theta) :
    phaseMinimum p tau theta ≤ phaseCost p tau theta delta := by
  apply csInf_le _ (mem_image_of_mem _ hdelta)
  refine ⟨0, ?_⟩
  rintro _ ⟨d, _, rfl⟩
  exact phaseCost_nonneg p tau theta d hp htau

/-- Negative phases have the same cost and obey the same lower bound. -/
theorem phaseMinimum_le_signed_cost (p tau theta delta : ℝ)
    (hp : 0 ≤ p) (htau : 0 ≤ tau) (hdelta : delta ∈ Icc (-theta) theta) :
    phaseMinimum p tau theta ≤ phaseCost p tau theta delta := by
  by_cases hd : 0 ≤ delta
  · exact phaseMinimum_le_cost p tau theta delta hp htau ⟨hd, hdelta.2⟩
  · have h := phaseMinimum_le_cost p tau theta (-delta) hp htau ⟨by linarith, by linarith [hdelta.1]⟩
    rwa [phaseCost_neg] at h

/-- The scalar phase minimum at a zero principal angle is zero. -/
theorem phaseMinimum_zero (p tau : ℝ) (htau : 0 ≤ tau) : phaseMinimum p tau 0 = 0 := by
  simp only [phaseMinimum, Icc_self, image_singleton, csInf_singleton]
  exact phaseCost_zero_angle p tau htau

/-- The cost of any nonnegative opposite phase pair dominates the scalar
minimum at its mean. No scalar critical-angle theorem is used. -/
theorem phaseMinimum_mean_le_sum (p tau a b : ℝ)
    (hp : 0 ≤ p) (htau : 0 ≤ tau) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    phaseMinimum p tau ((a + b) / 2) ≤
      smoothedPowerPhaseCost p tau a + smoothedPowerPhaseCost p tau b := by
  have h := phaseMinimum_le_signed_cost p tau ((a + b) / 2) ((a - b) / 2) hp htau
    ⟨by linarith, by linarith⟩
  simpa only [phaseCost, show (a + b) / 2 + (a - b) / 2 = a by ring,
    show (a + b) / 2 - (a - b) / 2 = b by ring] using h

/-- Convexity along the augmented Hilbert line bounds the penalty by the
chord joining its values at zero and two. No phase-transition formula is
used. This also includes zero smoothing. -/
theorem penalty_two_mul_le_mul (p tau s : ℝ)
    (hp : 1 ≤ p) (htau : 0 ≤ tau) (hs : s ∈ Icc 0 1) :
    penalty p tau (2 * s) ≤ s * penalty p tau 2 := by
  let x : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 (tau, 0)
  let y : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 (tau, 2)
  have hxy : (1 - s) • x + s • y = WithLp.toLp 2 (tau, 2 * s) := by
    apply WithLp.ofLp_injective 2
    change ((1 - s) * tau + s * tau, (1 - s) * 0 + s * 2) = (tau, 2 * s)
    apply Prod.ext <;> dsimp <;> ring
  have hnorm (u : ℝ) :
      ‖WithLp.toLp 2 (tau, u)‖ ^ p = (tau ^ 2 + u ^ 2) ^ (p / 2) := by
    have hsq := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (tau, u))
    change ‖WithLp.toLp 2 (tau, u)‖ ^ 2 = ‖tau‖ ^ 2 + ‖u‖ ^ 2 at hsq
    simp only [Real.norm_eq_abs, sq_abs] at hsq
    calc
      _ = (‖WithLp.toLp 2 (tau, u)‖ ^ (2 : ℕ)) ^ (p / 2) := by
        rw [← Real.rpow_natCast_mul (norm_nonneg _)]
        congr 1
        ring
      _ = _ := congrArg (fun a : ℝ => a ^ (p / 2)) hsq
  have h := (convexOn_norm_rpow (E := WithLp 2 (ℝ × ℝ)) hp).2
    (mem_univ x) (mem_univ y) (sub_nonneg.mpr hs.2) hs.1 (by ring : 1 - s + s = 1)
  rw [hxy] at h
  change ‖WithLp.toLp 2 (tau, 2 * s)‖ ^ p ≤
    (1 - s) * ‖WithLp.toLp 2 (tau, 0)‖ ^ p + s * ‖WithLp.toLp 2 (tau, 2)‖ ^ p at h
  rw [hnorm, hnorm, hnorm] at h
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at h
  rw [rpow_sq_half p tau htau] at h
  unfold penalty
  nlinarith

/-- The boundary phase supplies a scalar competitor of endpoint sine cost. -/
theorem phaseMinimum_le_endpoint (p tau theta : ℝ)
    (hp : 0 ≤ p) (htau : 0 ≤ tau) (hθ : 0 ≤ theta) :
    phaseMinimum p tau theta ≤ penalty p tau (2 * Real.sin theta) := by
  have h := phaseMinimum_le_cost p tau theta theta hp htau ⟨hθ, le_rfl⟩
  have hrad : tau ^ 2 + 2 - 2 * Real.cos (theta + theta) =
      tau ^ 2 + (2 * Real.sin theta) ^ 2 := by
    rw [← two_mul theta, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hcost : phaseCost p tau theta theta = penalty p tau (2 * Real.sin theta) := by
    simp only [phaseCost, sub_self, phase_zero p tau htau, add_zero]
    unfold smoothedPowerPhaseCost penalty
    rw [hrad]
  exact h.trans_eq hcost

/-- The endpoint and convexity bound needed for the full gradient-kernel
sector, including zero and right principal angles. -/
theorem phaseMinimum_le_penalty_two_mul_sin (p tau theta : ℝ)
    (hp : 1 ≤ p) (htau : 0 ≤ tau) (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    phaseMinimum p tau theta ≤ penalty p tau 2 * Real.sin theta := by
  have hs : Real.sin theta ∈ Icc 0 1 :=
    ⟨Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]),
      Real.sin_le_one theta⟩
  exact (phaseMinimum_le_endpoint p tau theta (by linarith) htau hθ.1).trans
    ((penalty_two_mul_le_mul p tau (Real.sin theta) hp htau hs).trans_eq (mul_comm _ _))

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
