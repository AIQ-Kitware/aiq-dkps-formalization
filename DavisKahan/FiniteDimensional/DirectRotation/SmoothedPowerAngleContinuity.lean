/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerScalarMinimum

/-!
# Angle continuity of the common planar minimum

Rescaling the phase interval to `[0,1]` proves continuity of the exact minimum
in the physical angle, including zero and all transition/right boundaries.
This is classical compact-minimum continuity, used by the Hilbert-space lift;
it does not assert continuity of entire optimizer sets.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set

/-- Compact attainment makes the scalar minimum nonnegative. -/
theorem phaseMinimum_nonneg (p tau theta : ℝ) (hp : 0 ≤ p) (htau : 0 ≤ tau) (hθ : 0 ≤ theta) :
    0 ≤ phaseMinimum p tau theta := by
  obtain ⟨d, _, hv, _⟩ := exists_attains_phaseMinimum_of_nonneg p tau theta hp hθ
  rw [hv]
  exact phaseCost_nonneg p tau theta d hp htau

private theorem phaseMinimum_eq_scaled (p tau theta : ℝ) (hθ : 0 ≤ theta) :
    phaseMinimum p tau theta = sInf ((fun r => phaseCost p tau theta (theta * r)) '' Icc 0 1) := by
  unfold phaseMinimum
  congr 1
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    by_cases hz : theta = 0
    · subst theta
      have hd0 : d = 0 := le_antisymm hd.2 hd.1
      subst d
      exact ⟨0, ⟨le_rfl, by norm_num⟩, by simp only [mul_zero]⟩
    · have hpos : 0 < theta := lt_of_le_of_ne hθ (Ne.symm hz)
      refine ⟨d / theta, ⟨div_nonneg hd.1 hθ, (div_le_one hpos).mpr hd.2⟩, ?_⟩
      change phaseCost p tau theta (theta * (d / theta)) = phaseCost p tau theta d
      congr 1
      field_simp
  · rintro ⟨r, hr, rfl⟩
    refine ⟨theta * r, ⟨mul_nonneg hθ hr.1, ?_⟩, rfl⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr.2 hθ

/-- The literal scalar minimum varies continuously with the physical
angle. No phase-selection formula is needed, so every boundary is included. -/
theorem continuousOn_phaseMinimum_angle (p tau : ℝ) (hp : 0 ≤ p) :
    ContinuousOn (phaseMinimum p tau) (Ici 0) := by
  have hphi : Continuous (smoothedPowerPhaseCost p tau) := by
    unfold smoothedPowerPhaseCost
    exact ((continuous_const.sub (continuous_const.mul Real.continuous_cos)).rpow_const
      (fun _ => Or.inr (by linarith : 0 ≤ p / 2))).sub continuous_const
  have hf : Continuous (fun x : ℝ × ℝ => phaseCost p tau x.1 (x.1 * x.2)) :=
    (hphi.comp (continuous_fst.add (continuous_fst.mul continuous_snd))).add
      (hphi.comp (continuous_fst.sub (continuous_fst.mul continuous_snd)))
  have hmin : Continuous (fun theta : ℝ =>
      sInf ((fun r : ℝ => phaseCost p tau theta (theta * r)) '' Icc 0 1)) :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).continuous_sInf hf
  exact hmin.continuousOn.congr (fun theta hθ => phaseMinimum_eq_scaled p tau theta hθ)

/-- The attained scalar minimum is increasing in the physical angle.
Clipping the larger angle's phase gives a competitor with both eigenphases
smaller; no derivative or optimizer-selection formula is needed. -/
theorem monotoneOn_phaseMinimum_angle (p tau : ℝ) (hp : 0 ≤ p) (htau : 0 ≤ tau) :
    MonotoneOn (phaseMinimum p tau) (Icc 0 (Real.pi / 2)) := by
  have hphi : MonotoneOn (smoothedPowerPhaseCost p tau) (Icc 0 Real.pi) := by
    intro a ha b hb hab
    have hc := Real.antitoneOn_cos ha hb hab
    unfold smoothedPowerPhaseCost
    apply sub_le_sub_right
    exact Real.rpow_le_rpow (by nlinarith [sq_nonneg tau, Real.cos_le_one a])
      (by linarith) (by linarith)
  intro x hx y hy hxy
  obtain ⟨d, hd, hv, _⟩ := exists_attains_phaseMinimum_of_nonneg p tau y hp hy.1
  let e := min d x
  have he : e ∈ Icc 0 x := ⟨le_min hd.1 hx.1, min_le_right _ _⟩
  have heδ : e ≤ d := min_le_left _ _
  have hminus : x - e ≤ y - d := by
    by_cases hdx : d ≤ x
    · dsimp only [e]
      rw [min_eq_left hdx]
      linarith
    · dsimp only [e]
      rw [min_eq_right (le_of_not_ge hdx), sub_self]
      linarith [hd.2]
  calc
    _ ≤ phaseCost p tau x e := phaseMinimum_le_cost p tau x e hp htau he
    _ ≤ phaseCost p tau y d := by
      apply add_le_add
      · exact hphi ⟨by linarith [hx.1, he.1], by linarith [hx.2, he.2]⟩
          ⟨by linarith [hy.1, hd.1], by linarith [hy.2, hd.2]⟩ (by linarith)
      · exact hphi ⟨by linarith [he.2], by linarith [hx.2, he.1, Real.pi_pos]⟩
          ⟨by linarith [hd.2], by linarith [hy.2, hd.1, Real.pi_pos]⟩ hminus
    _ = _ := hv.symm

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
