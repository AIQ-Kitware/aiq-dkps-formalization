/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseCriticalAngle
public import Mathlib.Analysis.Convex.Strict
public import Mathlib.Analysis.Convex.Deriv

/-!
# Supporting lines associated with balanced amplitude roots

If a small phase `a` and a large phase `b` have equal amplitude, the tangent
to the chord power at `b` lies strictly above the power on `[a, pi]` away
from `b`. The corresponding strict upper support for the angle minimum
compares a mixed spectral block with independently optimized planes.
-/

public section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set

noncomputable section

/-- Between two balanced roots, the amplitude is strictly above their
common level. -/
theorem phaseAmplitude_gt_between_balanced_roots (p a b t : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2)
    (ha : a ∈ Ioo 0 (criticalAngle p)) (hb : b ∈ Ioo (criticalAngle p) Real.pi)
    (hab : phaseAmplitude p a = phaseAmplitude p b) (ht : t ∈ Ioo a b) :
    phaseAmplitude p a < phaseAmplitude p t := by
  rcases le_total t (criticalAngle p) with htc | hct
  · exact phaseAmplitude_strictMonoOn p hp1 hp2 ⟨ha.1.le, ha.2.le⟩
      ⟨(ha.1.trans ht.1).le, htc⟩ ht.1
  · rw [hab]
    exact phaseAmplitude_strictAntiOn p hp1 hp2 ⟨hct, (ht.2.trans hb.2).le⟩
      ⟨hb.1.le, hb.2.le⟩ ht.2

private theorem shifted_chord_hasDerivAt (p slope t : ℝ) (ht : 0 < phaseChord t) :
    HasDerivAt (fun u => phaseChord u ^ p - slope * u)
      (p * phaseAmplitude p t - slope) t := by
  have h := (chord_rpow_hasDerivAt p t ht).sub ((hasDerivAt_id t).const_mul slope)
  convert h using 1
  · rfl
  · unfold phaseAmplitude
    ring

/-- The chord-power tangent at the large balanced root is a strict upper
bound throughout the interval from the small root to `pi`. -/
theorem phaseChord_power_lt_balanced_tangent (p a b t : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2)
    (ha : a ∈ Ioo 0 (criticalAngle p)) (hb : b ∈ Ioo (criticalAngle p) Real.pi)
    (hab : phaseAmplitude p a = phaseAmplitude p b)
    (ht : t ∈ Icc a Real.pi) (hne : t ≠ b) :
    phaseChord t ^ p < phaseChord b ^ p +
      p * phaseAmplitude p b * (t - b) := by
  let g := fun u => phaseChord u ^ p - p * phaseAmplitude p b * u
  have hchord : Continuous phaseChord := by unfold phaseChord; fun_prop
  have hg : Continuous g :=
    ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp hchord).sub
      (continuous_const.mul continuous_id)
  have hmono : StrictMonoOn g (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hg.continuousOn
    intro u hu
    rw [interior_Icc] at hu
    have hpos := phaseChord_pos (ha.1.trans hu.1) (hu.2.trans hb.2)
    rw [(shifted_chord_hasDerivAt p (p * phaseAmplitude p b) u hpos).deriv]
    have hlevel := phaseAmplitude_gt_between_balanced_roots p a b u hp1 hp2 ha hb hab hu
    rw [hab] at hlevel
    nlinarith [mul_pos (by linarith : 0 < p) (sub_pos.2 hlevel)]
  have hanti : StrictAntiOn g (Icc b Real.pi) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hg.continuousOn
    intro u hu
    rw [interior_Icc] at hu
    have hcrit := criticalAngle_mem p hp1 hp2
    have hpos := phaseChord_pos (hcrit.1.trans (hb.1.trans hu.1)) hu.2
    rw [(shifted_chord_hasDerivAt p (p * phaseAmplitude p b) u hpos).deriv]
    have hlevel := phaseAmplitude_strictAntiOn p hp1 hp2 ⟨hb.1.le, hb.2.le⟩
      ⟨(hb.1.trans hu.1).le, hu.2.le⟩ hu.1
    nlinarith [mul_pos (by linarith : 0 < p) (sub_pos.2 hlevel)]
  have hgb : g t < g b := by
    rcases lt_or_gt_of_ne hne with htb | hbt
    · exact hmono ⟨ht.1, htb.le⟩ ⟨(ha.2.trans hb.1).le, le_rfl⟩ htb
    · exact hanti ⟨le_rfl, hb.2.le⟩ ⟨hbt.le, ht.2⟩ hbt
  dsimp only [g] at hgb
  nlinarith

/-- The same tangent is a non-strict upper bound at its contact point. -/
theorem phaseChord_power_le_balanced_tangent (p a b t : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2)
    (ha : a ∈ Ioo 0 (criticalAngle p)) (hb : b ∈ Ioo (criticalAngle p) Real.pi)
    (hab : phaseAmplitude p a = phaseAmplitude p b) (ht : t ∈ Icc a Real.pi) :
    phaseChord t ^ p ≤ phaseChord b ^ p +
      p * phaseAmplitude p b * (t - b) := by
  rcases eq_or_ne t b with rfl | hne
  · simp
  · exact (phaseChord_power_lt_balanced_tangent p a b t hp1 hp2 ha hb hab ht hne).le

private theorem small_root_angle_region (p a theta : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2)
    (ha : a ∈ Ioo 0 (criticalAngle p))
    (hθ : theta ∈ Icc a (Real.pi / 2)) :
    a ∈ Icc 0 Real.pi ∧ 2 * theta - a ∈ Icc a Real.pi ∧ 0 ≤ theta := by
  have hcrit := criticalAngle_mem p hp1 hp2
  exact ⟨⟨ha.1.le, by linarith [ha.2, hcrit.2, Real.pi_pos]⟩,
    ⟨by linarith [hθ.1], by linarith [hθ.2, ha.1]⟩,
    ha.1.le.trans hθ.1⟩

/-- A balanced root pair gives an upper supporting line for the exact
angle minimum on every angle at least its small root. -/
theorem phaseMinimum_le_balanced_support (p a b theta : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2)
    (ha : a ∈ Ioo 0 (criticalAngle p)) (hb : b ∈ Ioo (criticalAngle p) Real.pi)
    (hab : phaseAmplitude p a = phaseAmplitude p b)
    (hθ : theta ∈ Icc a (Real.pi / 2)) :
    phaseMinimum p theta ≤ phaseMinimum p ((a + b) / 2) +
      2 * p * phaseAmplitude p b * (theta - (a + b) / 2) := by
  obtain ⟨haπ, ht, hθ0⟩ := small_root_angle_region p a theta hp1 hp2 ha hθ
  have hcost := phaseMinimum_le_chord_sum p theta (2 * theta - a) a hp1.le hθ0
    ⟨ha.1.le.trans ht.1, ht.2⟩ haπ (by linarith)
  have htangent := phaseChord_power_le_balanced_tangent p a b (2 * theta - a)
    hp1 hp2 ha hb hab ht
  have hmin := (balanced_roots_phase_minimum p a b hp1 hp2 ha hb hab).2.2
  rw [hmin]
  nlinarith

/-- Away from its contact angle, the balanced-root support is strict. -/
theorem phaseMinimum_lt_balanced_support (p a b theta : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2)
    (ha : a ∈ Ioo 0 (criticalAngle p)) (hb : b ∈ Ioo (criticalAngle p) Real.pi)
    (hab : phaseAmplitude p a = phaseAmplitude p b)
    (hθ : theta ∈ Icc a (Real.pi / 2)) (hne : theta ≠ (a + b) / 2) :
    phaseMinimum p theta < phaseMinimum p ((a + b) / 2) +
      2 * p * phaseAmplitude p b * (theta - (a + b) / 2) := by
  obtain ⟨haπ, ht, hθ0⟩ := small_root_angle_region p a theta hp1 hp2 ha hθ
  have hcost := phaseMinimum_le_chord_sum p theta (2 * theta - a) a hp1.le hθ0
    ⟨ha.1.le.trans ht.1, ht.2⟩ haπ (by linarith)
  have hne' : 2 * theta - a ≠ b := by intro h; apply hne; linarith
  have htangent := phaseChord_power_lt_balanced_tangent p a b (2 * theta - a)
    hp1 hp2 ha hb hab ht hne'
  have hmin := (balanced_roots_phase_minimum p a b hp1 hp2 ha hb hab).2.2
  rw [hmin]
  nlinarith

/-- Spreading a balanced spectral block into distinct physical angles
with no greater total angle strictly lowers its independent scalar cost. -/
theorem two_angle_cost_lt_balanced_block (p a b theta₁ theta₂ : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2)
    (ha : a ∈ Ioo 0 (criticalAngle p)) (hb : b ∈ Ioo (criticalAngle p) Real.pi)
    (hab : phaseAmplitude p a = phaseAmplitude p b)
    (hθ₁ : theta₁ ∈ Icc a (Real.pi / 2)) (hθ₂ : theta₂ ∈ Icc a (Real.pi / 2))
    (hsum : theta₁ + theta₂ ≤ a + b)
    (hne : theta₁ ≠ (a + b) / 2 ∨ theta₂ ≠ (a + b) / 2) :
    phaseMinimum p theta₁ + phaseMinimum p theta₂ <
      2 * (phaseChord a ^ p + phaseChord b ^ p) := by
  have hlevel : 0 < phaseAmplitude p b := by
    have hcrit := criticalAngle_mem p hp1 hp2
    exact mul_pos (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hcrit.1, hb.1, Real.pi_pos], by linarith [hb.2]⟩)
      (Real.rpow_pos_of_pos (phaseChord_pos (hcrit.1.trans hb.1) hb.2) _)
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 2 * p * phaseAmplitude p b by positivity)
    (show theta₁ + theta₂ - (a + b) ≤ 0 by linarith)
  have hmin := (balanced_roots_phase_minimum p a b hp1 hp2 ha hb hab).2.2
  rcases hne with hne | hne
  · have h₁ := phaseMinimum_lt_balanced_support p a b theta₁ hp1 hp2 ha hb hab hθ₁ hne
    have h₂ := phaseMinimum_le_balanced_support p a b theta₂ hp1 hp2 ha hb hab hθ₂
    rw [hmin] at h₁ h₂
    nlinarith
  · have h₁ := phaseMinimum_le_balanced_support p a b theta₁ hp1 hp2 ha hb hab hθ₁
    have h₂ := phaseMinimum_lt_balanced_support p a b theta₂ hp1 hp2 ha hb hab hθ₂ hne
    rw [hmin] at h₁ h₂
    nlinarith

/-- The exact angle-cost power sum is strictly concave from its critical
angle through the right-angle endpoint. The proof uses strict supporting
lines and does not assume differentiability of the minimizing phase. -/
theorem phaseMinimum_strictConcaveOn_supercritical (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    StrictConcaveOn ℝ (Icc (criticalAngle p) (Real.pi / 2)) (phaseMinimum p) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy u v hu hv huv
  let z := u * x + v * y
  have hz : z ∈ Ioo (criticalAngle p) (Real.pi / 2) := by
    have h := (strictConvex_Icc (𝕜 := ℝ) (criticalAngle p) (Real.pi / 2))
      hx hy hxy hu hv huv
    simpa only [interior_Icc, smul_eq_mul] using h
  obtain ⟨a, ha, b, hb, hzab, hab⟩ :=
    exists_balanced_roots_of_supercritical_angle p z hp1 hp2 hz.1 hz.2
  have hxne : x ≠ (a + b) / 2 := by
    rw [← hzab]
    intro heq
    have hcomb : u * x + v * x = x := by rw [← add_mul, huv, one_mul]
    have hcancel : v * x = v * y := by dsimp [z] at heq; linarith
    exact hxy (mul_left_cancel₀ hv.ne' hcancel)
  have h₁ := phaseMinimum_lt_balanced_support p a b x hp1 hp2 ha hb hab
    ⟨ha.2.le.trans hx.1, hx.2⟩ hxne
  have h₂ := phaseMinimum_le_balanced_support p a b y hp1 hp2 ha hb hab
    ⟨ha.2.le.trans hy.1, hy.2⟩
  rw [← hzab] at h₁ h₂
  have hmix : u * (x - z) + v * (y - z) = 0 := by
    calc
      _ = u * x + v * y - (u + v) * z := by ring
      _ = 0 := by rw [huv]; dsimp [z]; ring
  change u * phaseMinimum p x + v * phaseMinimum p y < phaseMinimum p z
  calc
    _ < u * (phaseMinimum p z + 2 * p * phaseAmplitude p b * (x - z)) +
        v * (phaseMinimum p z + 2 * p * phaseAmplitude p b * (y - z)) :=
      add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h₁ hu)
        (mul_le_mul_of_nonneg_left h₂ hv.le)
    _ = (u + v) * phaseMinimum p z + 2 * p * phaseAmplitude p b *
        (u * (x - z) + v * (y - z)) := by ring
    _ = _ := by rw [huv, hmix]; ring

/-- Below the same transition, the exact angle-cost power sum is strictly
convex. Thus the scalar minimum has distinct convex and concave regimes. -/
theorem phaseMinimum_strictConvexOn_subcritical (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    StrictConvexOn ℝ (Icc 0 (criticalAngle p)) (phaseMinimum p) := by
  have hp0 : 0 < p := by linarith
  have hc := criticalAngle_mem p hp1 hp2
  have hchord : Continuous phaseChord := by unfold phaseChord; fun_prop
  have hcont : Continuous (fun t => 2 * phaseChord t ^ p) :=
    ((Real.continuous_rpow_const hp0.le).comp hchord).const_mul 2
  have hderiv (t : ℝ) (ht : t ∈ Ioo 0 (criticalAngle p)) :
      deriv (fun s => 2 * phaseChord s ^ p) t = 2 * (p * phaseAmplitude p t) := by
    have hpos := phaseChord_pos ht.1 (by linarith [ht.2, hc.2, Real.pi_pos])
    have hbase : HasDerivAt (fun s => phaseChord s ^ p) (p * phaseAmplitude p t) t := by
      simpa only [zero_mul, sub_zero] using shifted_chord_hasDerivAt p 0 t hpos
    exact (hbase.const_mul 2).deriv
  have hconv : StrictConvexOn ℝ (Icc 0 (criticalAngle p)) (fun t => 2 * phaseChord t ^ p) := by
    apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc _ _) hcont.continuousOn
    intro x hx y hy hxy
    rw [interior_Icc] at hx hy
    rw [hderiv x hx, hderiv y hy]
    exact mul_lt_mul_of_pos_left
      (mul_lt_mul_of_pos_left (phaseAmplitude_strictMonoOn p hp1 hp2
        ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy) hp0) (by norm_num)
  apply hconv.congr
  intro theta hθ
  symm
  rcases eq_or_ne theta 0 with rfl | hne
  · rw [phaseMinimum_zero_angle p hp1.le]
    simp [phaseChord, Real.zero_rpow hp0.ne']
  · have h0 : 0 < theta := lt_of_le_of_ne hθ.1 hne.symm
    exact phaseMinimum_eq_canonical_of_subcritical p theta hp1 hp2 h0 (hθ.2.trans_lt hc.2)
      ((critical_inequality_iff p theta hp1 hp2
        ⟨hθ.1, by linarith [hθ.2, hc.2, Real.pi_pos]⟩).2 hθ.2)

end
end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
