/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SmoothedPowerPhaseRatio

/-!
# Logarithmic phase-slope imbalance for the common penalty family

On an acute principal plane the log ratio has derivative equal to a positive
weight times the normalized control from `SmoothedPowerPhaseRatio`. This
identity supplies the single-crossing mechanism, rather than assuming scalar
optimality. Differentiation, trigonometric identities and logarithmic order
are classical. Transport-specific historical priority remains unresolved;
see T15--T16 and the common-phase discussion in the unification note.
-/

public section
noncomputable section

namespace TauCeti

/-- Logarithmic imbalance of opposite positive phase slopes, with the
constant positive exponent factor canceled. -/
@[expose] def smoothedPowerPhaseLogRatio (p tau theta delta : ℝ) : ℝ :=
  Real.log (Real.sin (theta + delta)) - Real.log (Real.sin (theta - delta)) +
    ((p - 2) / 2) * (Real.log (tau ^ 2 + 2 - 2 * Real.cos (theta + delta)) -
      Real.log (tau ^ 2 + 2 - 2 * Real.cos (theta - delta)))

/-- Positive phase slopes in the open upper semicircle. -/
theorem smoothedPowerPhaseSlope_pos (p tau t : ℝ) (hp : 0 < p) (htau : 0 < tau)
    (ht : t ∈ Set.Ioo 0 Real.pi) : 0 < smoothedPowerPhaseSlope p tau t :=
  mul_pos (mul_pos hp (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))
    (Real.rpow_pos_of_pos (smoothedPowerPhase_radicand_pos tau t htau) _)

/-- The explicit log expression is the actual log ratio of phase slopes. -/
theorem smoothedPowerPhaseLogRatio_eq_log_slope (p tau theta delta : ℝ)
    (hp : 0 < p) (htau : 0 < tau) (hθ : theta ∈ Set.Ioo 0 (Real.pi / 2))
    (hδ : delta ∈ Set.Ico 0 theta) :
    smoothedPowerPhaseLogRatio p tau theta delta =
      Real.log (smoothedPowerPhaseSlope p tau (theta + delta)) -
        Real.log (smoothedPowerPhaseSlope p tau (theta - delta)) := by
  have hlog (t : ℝ) (ht : t ∈ Set.Ioo 0 Real.pi) :
      Real.log (smoothedPowerPhaseSlope p tau t) =
        Real.log p + Real.log (Real.sin t) +
          ((p - 2) / 2) * Real.log (tau ^ 2 + 2 - 2 * Real.cos t) := by
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have hr := smoothedPowerPhase_radicand_pos tau t htau
    rw [smoothedPowerPhaseSlope, Real.log_mul (mul_pos hp hs).ne'
      (Real.rpow_pos_of_pos hr _).ne', Real.log_mul hp.ne' hs.ne', Real.log_rpow hr]
  rw [hlog _ ⟨by linarith [hθ.1, hδ.1], by linarith [hθ.2, hδ.2]⟩,
    hlog _ ⟨by linarith [hδ.2], by linarith [hθ.2, hδ.1, Real.pi_pos]⟩]
  unfold smoothedPowerPhaseLogRatio
  ring

/-- At zero phase the logarithmic imbalance is zero. -/
theorem smoothedPowerPhaseLogRatio_zero (p tau theta : ℝ) :
    smoothedPowerPhaseLogRatio p tau theta 0 = 0 := by
  simp only [smoothedPowerPhaseLogRatio, add_zero, sub_zero, sub_self, mul_zero]

/-- **The common logarithmic-curvature identity.** The actual log ratio
has derivative equal to a positive weight times the normalized control.
It includes zero phase but excludes the vanishing-slope endpoint. -/
theorem hasDerivAt_smoothedPowerPhaseLogRatio (p tau theta delta : ℝ)
    (htau : 0 < tau) (hθ : theta ∈ Set.Ioo 0 (Real.pi / 2))
    (hδ : delta ∈ Set.Ico 0 theta) :
    ∃ w > 0, HasDerivAt (smoothedPowerPhaseLogRatio p tau theta)
      (w * smoothedPowerPhaseRatioControl p tau (Real.cos theta) (Real.cos delta)) delta := by
  let sp := Real.sin (theta + delta)
  let sm := Real.sin (theta - delta)
  let cp := Real.cos (theta + delta)
  let cm := Real.cos (theta - delta)
  let A := tau ^ 2 + 2 - 2 * cp
  let B := tau ^ 2 + 2 - 2 * cm
  let c := Real.cos theta
  let d := Real.cos delta
  let s := Real.sin theta
  have hsp : 0 < sp := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hθ.1, hδ.1]) (by linarith [hθ.2, hδ.2])
  have hsm : 0 < sm := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hδ.2]) (by linarith [hθ.2, hδ.1, Real.pi_pos])
  have hA : 0 < A := smoothedPowerPhase_radicand_pos tau _ htau
  have hB : 0 < B := smoothedPowerPhase_radicand_pos tau _ htau
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hdc : c < d := Real.strictAntiOn_cos
    ⟨hδ.1, by linarith [hδ.2, hθ.2, Real.pi_pos]⟩
    ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩ hδ.2
  have hplus : HasDerivAt (fun x : ℝ => theta + x) 1 delta := by
    simpa only [id_eq] using (hasDerivAt_id delta).const_add theta
  have hminus : HasDerivAt (fun x : ℝ => theta - x) (-1) delta := by
    simpa only [id_eq] using HasDerivAt.const_sub theta (hasDerivAt_id delta)
  have hlogs := (((Real.hasDerivAt_sin _).comp delta hplus).log hsp.ne').sub
    (((Real.hasDerivAt_sin _).comp delta hminus).log hsm.ne')
  have hrp := (hasDerivAt_const delta (tau ^ 2 + 2)).sub
    (((Real.hasDerivAt_cos _).comp delta hplus).const_mul 2)
  have hrm := (hasDerivAt_const delta (tau ^ 2 + 2)).sub
    (((Real.hasDerivAt_cos _).comp delta hminus).const_mul 2)
  have hd := hlogs.add (((hrp.log hA.ne').sub (hrm.log hB.ne')).const_mul ((p - 2) / 2))
  change HasDerivAt (smoothedPowerPhaseLogRatio p tau theta) _ delta at hd
  have hd' : HasDerivAt (smoothedPowerPhaseLogRatio p tau theta)
      (cp / sp + cm / sm - (2 - p) * (sp / A + sm / B)) delta := by
    apply hd.congr_deriv
    simp only [sp, sm, cp, cm, A, B, Function.comp_apply, Pi.sub_apply]
    ring
  have hcross : cp * sm + cm * sp = 2 * s * c := by
    dsimp only [cp, cm, sp, sm, s, c]
    rw [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
    nlinarith [congrArg (fun x : ℝ => 2 * Real.sin theta * Real.cos theta * x)
      (Real.sin_sq_add_cos_sq delta)]
  have hsum : sp + sm = 2 * s * d := by
    dsimp only [sp, sm, s, d]
    rw [Real.sin_add, Real.sin_sub]
    ring
  have hrad : sp * B + sm * A = 2 * s * ((tau ^ 2 + 2) * d - 2 * c) := by
    dsimp only [A, B]
    linear_combination (tau ^ 2 + 2) * hsum - 2 * hcross
  have hprod : sp * sm = d ^ 2 - c ^ 2 := by
    dsimp only [sp, sm, d, c]
    rw [Real.sin_add, Real.sin_sub]
    nlinarith [congrArg (fun x : ℝ => Real.cos delta ^ 2 * x)
      (Real.sin_sq_add_cos_sq theta),
      congrArg (fun x : ℝ => Real.cos theta ^ 2 * x) (Real.sin_sq_add_cos_sq delta)]
  have hAB : A * B = (tau ^ 2 + 2) ^ 2 - 4 * (tau ^ 2 + 2) * c * d +
      4 * (c ^ 2 + d ^ 2 - 1) := by
    have hsumcos : cp + cm = 2 * c * d := by
      dsimp only [cp, cm, c, d]
      rw [Real.cos_add, Real.cos_sub]
      ring
    have hprodcos : cp * cm = c ^ 2 + d ^ 2 - 1 := by
      dsimp only [cp, cm, c, d]
      rw [Real.cos_add, Real.cos_sub]
      nlinarith [Real.sin_sq_add_cos_sq theta, Real.sin_sq_add_cos_sq delta,
        congrArg (fun x : ℝ => Real.sin delta ^ 2 * x) (Real.sin_sq_add_cos_sq theta),
        congrArg (fun x : ℝ => Real.cos theta ^ 2 * x) (Real.sin_sq_add_cos_sq delta)]
    dsimp only [A, B]
    nlinarith [congrArg (fun x : ℝ => 2 * (tau ^ 2 + 2) * x) hsumcos]
  let w := 2 * s * (d - c) ^ 2 / ((sp * sm) * (A * B))
  refine ⟨w, div_pos (mul_pos (mul_pos (by norm_num) hs) (sq_pos_of_pos (sub_pos.mpr hdc)))
    (mul_pos (mul_pos hsp hsm) (mul_pos hA hB)), ?_⟩
  apply hd'.congr_deriv
  have hcontrol := smoothedPowerPhaseRatioControl_mul_sq p tau c d (ne_of_gt hdc)
  rw [← hAB, ← hprod] at hcontrol
  calc
    _ = ((cp * sm + cm * sp) * (A * B) - (2 - p) * (sp * B + sm * A) * (sp * sm)) /
        ((sp * sm) * (A * B)) := by
      field_simp
    _ = (2 * s * (c * (A * B) - (2 - p) * ((tau ^ 2 + 2) * d - 2 * c) * (sp * sm))) /
        ((sp * sm) * (A * B)) := by rw [hcross, hrad]; ring
    _ = _ := by
      rw [← hcontrol]
      dsimp only [w]
      ring

end TauCeti
