/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseCriticalAngle

/-!
# An explicit optimal phase for the Schatten three-halves cost

At exponent `3/2`, the amplitude balance reduces to a polynomial identity.
Above the transition, the unique optimal scalar phase is
`arccos (cos theta / (1 - 2 * cos theta))`.
-/

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set

noncomputable section

private theorem amplitude_three_halves_sq (t : ℝ) (ht : 0 ≤ phaseChord t) :
    phaseAmplitude (3 / 2) t ^ 2 =
      2 * Real.sin (t / 2) * Real.cos (t / 2) ^ 2 := by
  unfold phaseAmplitude
  rw [mul_pow, show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt ht]
  unfold phaseChord
  ring

/-- At exponent `3/2`, every positive interior stationary phase satisfies
an algebraic cosine equation. -/
theorem stationary_phase_cos_three_halves (theta delta : ℝ)
    (hδ : delta ∈ Ioo 0 theta) (hπ : theta < Real.pi / 2)
    (hstat : deriv (phasePower (3 / 2) theta) delta = 0) :
    (1 - 2 * Real.cos theta) * Real.cos delta = Real.cos theta := by
  let u := (theta + delta) / 2
  let v := (theta - delta) / 2
  have hu0 : 0 < u := by dsimp [u]; linarith [hδ.1, hδ.2]
  have hv0 : 0 < v := by dsimp [v]; linarith [hδ.2]
  have hup : u < Real.pi / 2 := by dsimp [u]; linarith [hδ.2]
  have hvp : v < Real.pi / 2 := by dsimp [v]; linarith [hδ.1]
  have hsu : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos])
  have hsv : 0 < Real.sin v := Real.sin_pos_of_pos_of_lt_pi hv0 (by linarith [Real.pi_pos])
  have hp : 0 < phaseChord (theta + delta) := by
    change 0 < 2 * Real.sin u
    positivity
  have hm : 0 < phaseChord (theta - delta) := by
    change 0 < 2 * Real.sin v
    positivity
  have hbal := (phasePower_stationary_iff (3 / 2) theta delta (by norm_num) hp hm).1 hstat
  have hsq := congrArg (fun x : ℝ => x ^ 2) hbal
  rw [amplitude_three_halves_sq _ hp.le, amplitude_three_halves_sq _ hm.le] at hsq
  change 2 * Real.sin u * Real.cos u ^ 2 =
    2 * Real.sin v * Real.cos v ^ 2 at hsq
  have hsin : Real.sin v < Real.sin u :=
    Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos], hvp.le⟩
      ⟨by linarith [Real.pi_pos], hup.le⟩ (by dsimp [u, v]; linarith [hδ.1])
  have hcu : Real.cos u ^ 2 = 1 - Real.sin u ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hcv : Real.cos v ^ 2 = 1 - Real.sin v ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq v]
  rw [hcu, hcv] at hsq
  have hpoly : Real.sin u ^ 2 + Real.sin u * Real.sin v + Real.sin v ^ 2 = 1 := by
    have hfac : (Real.sin u - Real.sin v) *
        (1 - Real.sin u ^ 2 - Real.sin u * Real.sin v - Real.sin v ^ 2) = 0 := by
      nlinarith
    have hzero := (mul_eq_zero.mp hfac).resolve_left (sub_pos.2 hsin).ne'
    linarith
  have hadd : u + v = theta := by dsimp [u, v]; ring
  have hsub : u - v = delta := by dsimp [u, v]; ring
  have hcθ : Real.cos theta = Real.cos u * Real.cos v - Real.sin u * Real.sin v := by
    rw [← hadd, Real.cos_add]
  have hcδ : Real.cos delta = Real.cos u * Real.cos v + Real.sin u * Real.sin v := by
    rw [← hsub, Real.cos_sub]
  have hprod : (Real.cos u * Real.cos v) ^ 2 =
      (1 - Real.sin u ^ 2) * (1 - Real.sin v ^ 2) := by rw [mul_pow, hcu, hcv]
  rw [hcθ, hcδ]
  nlinarith

/-- Above the critical angle, the Schatten `3/2` scalar-phase minimizer is
given by a single explicit inverse cosine. -/
theorem explicit_phase_minimizer_three_halves (theta : ℝ)
    (h0 : 0 < theta) (hπ : theta < Real.pi / 2)
    (hc : Real.cos theta < 1 / 3) :
    Real.arccos (Real.cos theta / (1 - 2 * Real.cos theta)) ∈ Ioo 0 theta ∧
      ∀ eta ∈ Icc 0 theta,
        phasePower (3 / 2) theta
            (Real.arccos (Real.cos theta / (1 - 2 * Real.cos theta))) ≤
          phasePower (3 / 2) theta eta ∧
        (phasePower (3 / 2) theta eta =
          phasePower (3 / 2) theta
            (Real.arccos (Real.cos theta / (1 - 2 * Real.cos theta))) ↔
          eta = Real.arccos (Real.cos theta / (1 - 2 * Real.cos theta))) := by
  obtain ⟨delta, hδ, hstat, hmin⟩ := exists_unique_phase_minimizer_of_supercritical
    (3 / 2) theta (by norm_num) (by norm_num) h0 hπ (by nlinarith)
  have hroot := stationary_phase_cos_three_halves theta delta hδ hπ hstat
  have hden : 1 - 2 * Real.cos theta ≠ 0 := by linarith
  have hcos : Real.cos delta = Real.cos theta / (1 - 2 * Real.cos theta) := by
    apply (eq_div_iff hden).2
    nlinarith
  have heq := congrArg Real.arccos hcos
  rw [Real.arccos_cos hδ.1.le (by linarith [hδ.2, Real.pi_pos])] at heq
  rw [heq] at hδ hmin
  exact ⟨hδ, hmin⟩

/-- The attained `3/2` minimum is the cost at the explicit optimal phase. -/
theorem phaseMinimum_three_halves_eq_explicit (theta : ℝ)
    (h0 : 0 < theta) (hπ : theta < Real.pi / 2)
    (hc : Real.cos theta < 1 / 3) :
    phaseMinimum (3 / 2) theta = phasePower (3 / 2) theta
      (Real.arccos (Real.cos theta / (1 - 2 * Real.cos theta))) := by
  obtain ⟨hδ, hmin⟩ := explicit_phase_minimizer_three_halves theta h0 hπ hc
  apply phaseMinimum_eq_of_isMinOn
  · exact ⟨hδ.1.le, hδ.2.le⟩
  · exact fun eta heta => (hmin eta heta).1

private theorem three_halves_power_sq (x y c : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hc0 : 0 ≤ c) (hc : c < 1 / 3)
    (hxy : x * y * (1 - 2 * c) = 4 * c ^ 2)
    (hquad : x ^ 2 + x * y + y ^ 2 = 4) :
    (x ^ ((3 : ℝ) / 2) + y ^ ((3 : ℝ) / 2)) ^ 2 =
      8 * (1 + c) * Real.sqrt (1 - 2 * c) := by
  have hd : 0 < 1 - 2 * c := by linarith
  have ht : 0 < Real.sqrt (1 - 2 * c) := Real.sqrt_pos.2 hd
  have hsum : (x + y) ^ 2 = 4 + x * y := by nlinarith
  have hSt : (x + y) * Real.sqrt (1 - 2 * c) = 2 * (1 - c) := by
    apply (sq_eq_sq₀ (by positivity) (by linarith : 0 ≤ 2 * (1 - c))).1
    rw [mul_pow, Real.sq_sqrt hd.le, hsum]
    nlinarith
  have hTt : Real.sqrt (x * y) * Real.sqrt (1 - 2 * c) = 2 * c := by
    apply (sq_eq_sq₀ (by positivity) (by positivity : 0 ≤ 2 * c)).1
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hx.le hy.le), Real.sq_sqrt hd.le]
    nlinarith
  have hpow (z : ℝ) (hz : 0 < z) : z ^ ((3 : ℝ) / 2) = z * Real.sqrt z := by
    calc
      z ^ ((3 : ℝ) / 2) = z ^ ((1 : ℝ) + 1 / 2) := by congr 1; norm_num
      _ = z ^ (1 : ℝ) * z ^ ((1 : ℝ) / 2) := Real.rpow_add hz _ _
      _ = z * Real.sqrt z := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have hcost : (x ^ ((3 : ℝ) / 2) + y ^ ((3 : ℝ) / 2)) ^ 2 =
      (x + y) * (4 - 2 * x * y) + 2 * x * y * Real.sqrt (x * y) := by
    rw [hpow x hx, hpow y hy]
    calc
      (x * Real.sqrt x + y * Real.sqrt y) ^ 2 =
          x ^ 2 * Real.sqrt x ^ 2 + y ^ 2 * Real.sqrt y ^ 2 +
            2 * x * y * (Real.sqrt x * Real.sqrt y) := by ring
      _ = (x + y) * (x ^ 2 - x * y + y ^ 2) +
          2 * x * y * Real.sqrt (x * y) := by
        rw [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le, ← Real.sqrt_mul hx.le]
        ring
      _ = _ := by rw [show x ^ 2 - x * y + y ^ 2 = 4 - 2 * x * y by linarith]
  apply mul_right_cancel₀ ht.ne'
  calc
    (x ^ ((3 : ℝ) / 2) + y ^ ((3 : ℝ) / 2)) ^ 2 * Real.sqrt (1 - 2 * c) =
        4 * ((x + y) * Real.sqrt (1 - 2 * c)) -
          2 * x * y * ((x + y) * Real.sqrt (1 - 2 * c)) +
          2 * x * y * (Real.sqrt (x * y) * Real.sqrt (1 - 2 * c)) := by rw [hcost]; ring
    _ = 8 * (1 + c) * Real.sqrt (1 - 2 * c) ^ 2 := by
      rw [hSt, hTt, Real.sq_sqrt hd.le]
      nlinarith
    _ = (8 * (1 + c) * Real.sqrt (1 - 2 * c)) * Real.sqrt (1 - 2 * c) := by ring

/-- Above the critical angle, the square of the optimal Schatten `3/2`
power sum has a closed expression involving one square root. -/
theorem phaseMinimum_three_halves_sq (theta : ℝ)
    (h0 : 0 < theta) (hπ : theta < Real.pi / 2)
    (hc : Real.cos theta < 1 / 3) :
    phaseMinimum (3 / 2) theta ^ 2 =
      8 * (1 + Real.cos theta) * Real.sqrt (1 - 2 * Real.cos theta) := by
  obtain ⟨delta, hδ, hstat, hmin⟩ := exists_unique_phase_minimizer_of_supercritical
    (3 / 2) theta (by norm_num) (by norm_num) h0 hπ (by nlinarith)
  have heq := phaseMinimum_eq_of_isMinOn (3 / 2) theta delta
    ⟨hδ.1.le, hδ.2.le⟩ (fun eta heta => (hmin eta heta).1)
  have hroot := stationary_phase_cos_three_halves theta delta hδ hπ hstat
  have hp : 0 < phaseChord (theta + delta) := by
    apply mul_pos (by norm_num)
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hδ.1])
      (by linarith [hδ.2, Real.pi_pos])
  have hm : 0 < phaseChord (theta - delta) := by
    apply mul_pos (by norm_num)
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hδ.2])
      (by linarith [hδ.1, Real.pi_pos])
  have hprod := phaseChord_mul theta delta
  have hsum := phaseChord_add_sq theta delta
  have hxy : phaseChord (theta + delta) * phaseChord (theta - delta) *
      (1 - 2 * Real.cos theta) = 4 * Real.cos theta ^ 2 := by
    rw [hprod]
    nlinarith
  have hquad : phaseChord (theta + delta) ^ 2 +
      phaseChord (theta + delta) * phaseChord (theta - delta) +
        phaseChord (theta - delta) ^ 2 = 4 := by
    nlinarith
  rw [heq]
  exact three_halves_power_sq _ _ _ hp hm
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hπ⟩).le hc hxy hquad

end
end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
