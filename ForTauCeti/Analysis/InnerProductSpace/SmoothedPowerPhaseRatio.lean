/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SmoothedPowerPhase
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The common logarithmic-curvature control for smoothed powers

The derivative of a logarithmic phase-slope ratio is controlled by a cubic
normalized by `(d-c)^2`. The raw cubic need not be monotone. Its normalized
form is strictly decreasing for the whole positively smoothed convex-power
family. This is the scalar mechanism for C2, independent of ambient transport.

The differentiation and monotonicity principles are classical ingredients.
The scalar generalized Charbonnier penalty is prior art (Sun--Roth--Black
2010, section 4; Barron 2019, equation (4)); historical priority of the
resulting constrained transport transition remains unresolved. See the
source-to-Lean map in `dev/spectral-transport-unification.md`.
-/

public section
noncomputable section

namespace TauCeti

/-- The auxiliary cubic in the normalized phase-ratio derivative. -/
@[expose] def smoothedPowerPhaseRatioCubic (p c d : ℝ) : ℝ :=
  4 * c - (p + 2) * c ^ 2 * d - (2 - p) * d ^ 3

/-- The normalized sign-controlling factor, in cosine coordinates. -/
@[expose] def smoothedPowerPhaseRatioControl (p tau c d : ℝ) : ℝ :=
  2 * p * c - 2 * (2 - p) * d +
    tau ^ 2 * smoothedPowerPhaseRatioCubic p c d / (d - c) ^ 2 +
      tau ^ 4 * c / (d - c) ^ 2

private theorem cubic_hasDerivAt (p c d : ℝ) :
    HasDerivAt (smoothedPowerPhaseRatioCubic p c)
      (-(p + 2) * c ^ 2 - 3 * (2 - p) * d ^ 2) d := by
  have h := ((hasDerivAt_const d (4 * c)).sub
    ((hasDerivAt_id d).const_mul ((p + 2) * c ^ 2))).sub
      (((hasDerivAt_id d).pow 3).const_mul (2 - p))
  convert h using 1
  · funext x
    rfl
  · simp only [id_eq]
    norm_num
    ring

private theorem cubic_quotient_hasDerivAt (p c d : ℝ) (hd : d ≠ c) :
    HasDerivAt (fun x => smoothedPowerPhaseRatioCubic p c x / (x - c) ^ 2)
      (((d - c) * (-(p + 2) * c ^ 2 - 3 * (2 - p) * d ^ 2) -
        2 * smoothedPowerPhaseRatioCubic p c d) / (d - c) ^ 3) d := by
  apply ((cubic_hasDerivAt p c d).div
    (((hasDerivAt_id d).sub_const c).pow 2) (pow_ne_zero 2 (sub_ne_zero.mpr hd))).congr_deriv
  simp only [id_eq, Pi.pow_apply]
  field_simp
  ring

private theorem cubic_quotient_numerator_neg (p c d : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hc : c ∈ Set.Ioo 0 1) (hd : d ∈ Set.Ioc c 1) :
    (d - c) * (-(p + 2) * c ^ 2 - 3 * (2 - p) * d ^ 2) -
      2 * smoothedPowerPhaseRatioCubic p c d < 0 := by
  have he : 0 < d - c := sub_pos.mpr hd.1
  have he1 : d - c ≤ 1 - c := sub_le_sub_right hd.2 c
  have h1 := mul_le_mul_of_nonneg_right (by linarith : 8 - 2 * p ≤ 6)
    (mul_nonneg (sq_nonneg c) he.le)
  have h2 := mul_le_mul_of_nonneg_left he1 (by positivity : 0 ≤ 6 * c ^ 2)
  have h3 : 0 ≤ (2 - p) * (d - c) ^ 3 := mul_nonneg (by linarith) (pow_nonneg he.le 3)
  have hneg : 0 < c * (1 - c) * (8 + 2 * c) :=
    mul_pos (mul_pos hc.1 (sub_pos.mpr hc.2)) (by linarith [hc.1])
  unfold smoothedPowerPhaseRatioCubic
  nlinarith

/-- The control factor decreases strictly in the phase cosine. Positive
smoothing includes the quadratic exponent; the acute cosine is essential. -/
theorem smoothedPowerPhaseRatioControl_strictAntiOn (p tau c : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hc : c ∈ Set.Ioo 0 1) :
    StrictAntiOn (smoothedPowerPhaseRatioControl p tau c) (Set.Ioc c 1) := by
  have hderiv (d : ℝ) (hd : d ∈ Set.Ioc c 1) :
      ∃ v < 0, HasDerivAt (smoothedPowerPhaseRatioControl p tau c) v d := by
    have hdc : d ≠ c := ne_of_gt hd.1
    let v := ((d - c) * (-(p + 2) * c ^ 2 - 3 * (2 - p) * d ^ 2) -
      2 * smoothedPowerPhaseRatioCubic p c d) / (d - c) ^ 3
    have hv : v < 0 := div_neg_of_neg_of_pos
      (cubic_quotient_numerator_neg p c d hp hp2 hc hd) (pow_pos (sub_pos.mpr hd.1) 3)
    have htail : HasDerivAt (fun x : ℝ => tau ^ 4 * c / (x - c) ^ 2)
        (-(2 * tau ^ 4 * c) / (d - c) ^ 3) d := by
      apply ((hasDerivAt_const d (tau ^ 4 * c)).div
        (((hasDerivAt_id d).sub_const c).pow 2)
          (pow_ne_zero 2 (sub_ne_zero.mpr hdc))).congr_deriv
      simp only [id_eq, Pi.pow_apply]
      field_simp
      ring
    refine ⟨-2 * (2 - p) + tau ^ 2 * v - 2 * tau ^ 4 * c / (d - c) ^ 3, ?_, ?_⟩
    · have hstrict : tau ^ 2 * v < 0 := mul_neg_of_pos_of_neg (sq_pos_of_pos htau) hv
      have hlast : 0 ≤ 2 * tau ^ 4 * c / (d - c) ^ 3 :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg htau.le 4)) hc.1.le)
          (pow_nonneg (sub_pos.mpr hd.1).le 3)
      nlinarith
    · have h := (((hasDerivAt_const d (2 * p * c)).sub
        ((hasDerivAt_id d).const_mul (2 * (2 - p)))).add
          ((cubic_quotient_hasDerivAt p c d hdc).const_mul (tau ^ 2))).add htail
      convert h using 1
      · funext x
        simp only [smoothedPowerPhaseRatioControl, Pi.add_apply, Pi.sub_apply, id_eq]
        ring
      · simp only [v]
        ring
  apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
  · intro d hd
    obtain ⟨v, _, hv⟩ := hderiv d hd
    exact hv.continuousAt.continuousWithinAt
  · intro d hd
    rw [interior_Ioc] at hd
    obtain ⟨v, hv, hD⟩ := hderiv d ⟨hd.1, hd.2.le⟩
    rw [hD.deriv]
    exact hv

/-- Multiplying out the normalization gives the actual ratio numerator. -/
theorem smoothedPowerPhaseRatioControl_mul_sq (p tau c d : ℝ) (hd : d ≠ c) :
    smoothedPowerPhaseRatioControl p tau c d * (d - c) ^ 2 =
      c * ((tau ^ 2 + 2) ^ 2 - 4 * (tau ^ 2 + 2) * c * d + 4 * (c ^ 2 + d ^ 2 - 1)) -
        (2 - p) * ((tau ^ 2 + 2) * d - 2 * c) * (d ^ 2 - c ^ 2) := by
  unfold smoothedPowerPhaseRatioControl smoothedPowerPhaseRatioCubic
  field_simp
  ring

/-- At zero phase the ratio numerator factors by the curvature polynomial. -/
theorem smoothedPowerPhaseRatioControl_one_mul_sq (p tau c : ℝ) (hc : c ≠ 1) :
    smoothedPowerPhaseRatioControl p tau c 1 * (1 - c) ^ 2 =
      (tau ^ 2 + 2 - 2 * c) * (p - 2 + (tau ^ 2 + 2) * c - p * c ^ 2) := by
  rw [smoothedPowerPhaseRatioControl_mul_sq p tau c 1 (Ne.symm hc)]
  ring

end TauCeti
