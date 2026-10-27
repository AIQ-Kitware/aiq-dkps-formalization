/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseTransition
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The exact scalar-phase minimum as an angle cost

`phaseMinimum p theta` is the attained minimum of the Schatten power sum on
`[0, theta]`. The angle-budget inequality compares it with any two nonnegative
rotation angles whose sum is at least `2 * theta`. This is the scalar reduction
needed for spectral lower bounds on general unitary transports.
-/

public section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

noncomputable section

/-- The minimum Schatten power sum on a scalar-phase interval. The lemmas
below supply attainment and the intended angle and exponent hypotheses. -/
@[expose] def phaseMinimum (p theta : ℝ) : ℝ :=
  sInf (phasePower p theta '' Set.Icc 0 theta)

/-- The scalar phase minimum depends continuously on every positive
exponent, including at one and at vanishing displacement chords. -/
theorem continuousOn_phaseMinimum_exponent (theta : ℝ) :
    ContinuousOn (fun p => phaseMinimum p theta) (Set.Ioi 0) := by
  unfold phaseMinimum
  rw [continuousOn_iff_continuous_domRestrict]
  apply isCompact_Icc.continuous_sInf
  unfold phasePower phaseChord
  apply Continuous.add
  · apply Continuous.rpow (by fun_prop) (continuous_subtype_val.comp continuous_fst)
    intro x
    exact Or.inr x.1.property
  · apply Continuous.rpow (by fun_prop) (continuous_subtype_val.comp continuous_fst)
    intro x
    exact Or.inr x.1.property

/-- An attaining phase identifies the infimum with its actual power sum. -/
theorem phaseMinimum_eq_of_isMinOn (p theta delta : ℝ)
    (hδ : delta ∈ Set.Icc 0 theta)
    (hmin : IsMinOn (phasePower p theta) (Set.Icc 0 theta) delta) :
    phaseMinimum p theta = phasePower p theta delta := by
  apply IsLeast.csInf_eq
  refine ⟨⟨delta, hδ, rfl⟩, ?_⟩
  rintro _ ⟨eta, heta, rfl⟩
  exact hmin heta

/-- The angle cost is always attained for Schatten exponents. -/
theorem exists_attains_phaseMinimum (p theta : ℝ) (hp : 1 ≤ p) (hθ : 0 ≤ theta) :
    ∃ delta ∈ Set.Icc 0 theta,
      phaseMinimum p theta = phasePower p theta delta ∧
        IsMinOn (phasePower p theta) (Set.Icc 0 theta) delta := by
  obtain ⟨delta, hδ0, hδθ, hmin⟩ := exists_phase_minimizer p theta hp hθ
  have hm : IsMinOn (phasePower p theta) (Set.Icc 0 theta) delta :=
    fun eta heta => hmin eta heta.1 heta.2
  exact ⟨delta, ⟨hδ0, hδθ⟩,
    phaseMinimum_eq_of_isMinOn p theta delta ⟨hδ0, hδθ⟩ hm, hm⟩

/-- Every phase in the optimization interval bounds the exact minimum above. -/
theorem phaseMinimum_le_phasePower (p theta : ℝ) (hp : 1 ≤ p) (hθ : 0 ≤ theta)
    {delta : ℝ} (hδ : delta ∈ Set.Icc 0 theta) :
    phaseMinimum p theta ≤ phasePower p theta delta := by
  obtain ⟨eta, _, heq, hmin⟩ := exists_attains_phaseMinimum p theta hp hθ
  rw [heq]
  exact hmin hδ

private theorem phaseChord_nonneg {t : ℝ} (h0 : 0 ≤ t) (hπ : t ≤ Real.pi) :
    0 ≤ phaseChord t := by
  exact mul_nonneg (by norm_num)
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]))

private theorem phaseChord_strictMonoOn : StrictMonoOn phaseChord (Set.Icc 0 Real.pi) := by
  intro a ha b hb hab
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
  exact Real.strictMonoOn_sin ⟨by linarith [ha.1, Real.pi_pos], by linarith [ha.2]⟩
    ⟨by linarith [hb.1, Real.pi_pos], by linarith [hb.2]⟩ (by linarith)

/-- A principal-angle minimum is nonnegative. -/
theorem phaseMinimum_nonneg (p theta : ℝ) (hp : 1 ≤ p)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) : 0 ≤ phaseMinimum p theta := by
  obtain ⟨delta, hδ, heq, _⟩ := exists_attains_phaseMinimum p theta hp hθ.1
  rw [heq]
  apply add_nonneg
  · exact Real.rpow_nonneg
      (phaseChord_nonneg (by linarith [hθ.1, hδ.1]) (by linarith [hθ.2, hδ.2])) _
  · exact Real.rpow_nonneg
      (phaseChord_nonneg (by linarith [hδ.2]) (by linarith [hθ.2, hδ.1, Real.pi_pos])) _

/-- The zero-angle cost vanishes. -/
@[simp] theorem phaseMinimum_zero_angle (p : ℝ) (hp : 1 ≤ p) :
    phaseMinimum p 0 = 0 := by
  obtain ⟨delta, hδ, heq, _⟩ := exists_attains_phaseMinimum p 0 hp le_rfl
  have hzero : delta = 0 := le_antisymm hδ.2 hδ.1
  rw [heq, hzero]
  simp [phasePower, phaseChord, Real.zero_rpow (show p ≠ 0 by linarith)]

/-- The exact angle cost is the canonical displacement cost throughout the
subcritical regime, including the critical angle. -/
theorem phaseMinimum_eq_canonical_of_subcritical (p theta : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hcrit : 2 - p ≤ p * Real.cos theta) :
    phaseMinimum p theta = 2 * phaseChord theta ^ p := by
  rw [phaseMinimum_eq_of_isMinOn p theta 0 ⟨le_rfl, hθ.le⟩
    ((canonical_phase_isMinOn_iff p theta hp1 hp2 hθ hπ).mpr hcrit)]
  simp only [phasePower, add_zero, sub_zero, two_mul]

/-- At an acute positive angle an attaining phase never reaches the
rank-one-displacement endpoint. -/
theorem exists_attains_phaseMinimum_mem_Ico (p theta : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (hθ : 0 < theta) (hπ : theta < Real.pi / 2) :
    ∃ delta ∈ Set.Ico 0 theta, phaseMinimum p theta = phasePower p theta delta := by
  by_cases hcrit : 2 - p ≤ p * Real.cos theta
  · refine ⟨0, ⟨le_rfl, hθ⟩, ?_⟩
    exact phaseMinimum_eq_of_isMinOn p theta 0 ⟨le_rfl, hθ.le⟩
      ((canonical_phase_isMinOn_iff p theta hp1 hp2 hθ hπ).mpr hcrit)
  · obtain ⟨delta, hδ, _, hopt⟩ := exists_unique_phase_minimizer_of_supercritical
      p theta hp1 hp2 hθ hπ (lt_of_not_ge hcrit)
    exact ⟨delta, ⟨hδ.1.le, hδ.2⟩,
      phaseMinimum_eq_of_isMinOn p theta delta ⟨hδ.1.le, hδ.2.le⟩
        (fun eta heta => (hopt eta heta).1)⟩

private theorem phaseMinimum_le_chord_sum_ordered
    (p theta a b : ℝ) (hp : 1 ≤ p)
    (hθ : 0 ≤ theta) (ha0 : 0 ≤ a) (haπ : a ≤ Real.pi)
    (hb0 : 0 ≤ b) (hbπ : b ≤ Real.pi) (hba : b ≤ a)
    (hbudget : 2 * theta ≤ a + b) :
    phaseMinimum p theta ≤ phaseChord a ^ p + phaseChord b ^ p := by
  by_cases hs : a + b = 0
  · have ha : a = 0 := by linarith
    have hb : b = 0 := by linarith
    have htheta : theta = 0 := by linarith
    rw [htheta, phaseMinimum_zero_angle p hp, ha, hb]
    simp [phaseChord, Real.zero_rpow (show p ≠ 0 by linarith)]
  have hspos : 0 < a + b := lt_of_le_of_ne (by linarith) (Ne.symm hs)
  let x := 2 * theta * a / (a + b)
  let y := 2 * theta * b / (a + b)
  have hx0 : 0 ≤ x := div_nonneg (by positivity) hspos.le
  have hy0 : 0 ≤ y := div_nonneg (by positivity) hspos.le
  have hxa : x ≤ a := by
    apply (div_le_iff₀ hspos).mpr
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hbudget)]
  have hyb : y ≤ b := by
    apply (div_le_iff₀ hspos).mpr
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hbudget)]
  have hyx : y ≤ x := by
    apply (div_le_div_iff_of_pos_right hspos).mpr
    exact mul_le_mul_of_nonneg_left hba (by positivity)
  have hxy : x + y = 2 * theta := by
    dsimp [x, y]
    field_simp
  let delta := (x - y) / 2
  have hδ : delta ∈ Set.Icc 0 theta := by
    constructor <;> dsimp [delta] <;> linarith
  have hplus : theta + delta = x := by dsimp [delta]; linarith
  have hminus : theta - delta = y := by dsimp [delta]; linarith
  calc
    phaseMinimum p theta ≤ phasePower p theta delta :=
      phaseMinimum_le_phasePower p theta hp hθ hδ
    _ = phaseChord x ^ p + phaseChord y ^ p := by rw [phasePower, hplus, hminus]
    _ ≤ phaseChord a ^ p + phaseChord b ^ p := by
      apply add_le_add
      · exact Real.rpow_le_rpow (phaseChord_nonneg hx0 (hxa.trans haπ))
          (phaseChord_strictMonoOn.monotoneOn ⟨hx0, hxa.trans haπ⟩ ⟨ha0, haπ⟩ hxa)
          (by linarith)
      · exact Real.rpow_le_rpow (phaseChord_nonneg hy0 (hyb.trans hbπ))
          (phaseChord_strictMonoOn.monotoneOn ⟨hy0, hyb.trans hbπ⟩ ⟨hb0, hbπ⟩ hyb)
          (by linarith)

/-- Any two nonnegative spectral rotation angles with a total angle at least
`2 * theta` have cost at least the optimal scalar phase at `theta`. The order
of the two spectral angles is immaterial. -/
theorem phaseMinimum_le_chord_sum (p theta a b : ℝ) (hp : 1 ≤ p)
    (hθ : 0 ≤ theta) (ha : a ∈ Set.Icc 0 Real.pi) (hb : b ∈ Set.Icc 0 Real.pi)
    (hbudget : 2 * theta ≤ a + b) :
    phaseMinimum p theta ≤ phaseChord a ^ p + phaseChord b ^ p := by
  rcases le_total b a with hba | hab
  · exact phaseMinimum_le_chord_sum_ordered p theta a b hp hθ ha.1 ha.2 hb.1 hb.2 hba
      hbudget
  · simpa only [add_comm] using phaseMinimum_le_chord_sum_ordered p theta b a hp hθ
      hb.1 hb.2 ha.1 ha.2 hab (by linarith)

/-- Squared chord length in terms of the full angle. -/
theorem phaseChord_sq (t : ℝ) : phaseChord t ^ 2 = 2 - 2 * Real.cos t := by
  have hcos := Real.cos_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hcos
  unfold phaseChord
  nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

/-- The two squared planar displacement chords have this exact sum. -/
theorem phaseChord_add_sq (theta delta : ℝ) :
    phaseChord (theta + delta) ^ 2 + phaseChord (theta - delta) ^ 2 =
      4 - 4 * Real.cos theta * Real.cos delta := by
  rw [phaseChord_sq, phaseChord_sq, Real.cos_add, Real.cos_sub]
  ring

/-- The product of the two planar displacement chords. -/
theorem phaseChord_mul (theta delta : ℝ) :
    phaseChord (theta + delta) * phaseChord (theta - delta) =
      2 * (Real.cos delta - Real.cos theta) := by
  have h := Real.two_mul_sin_mul_sin ((theta + delta) / 2) ((theta - delta) / 2)
  rw [show (theta + delta) / 2 - (theta - delta) / 2 = delta by ring,
    show (theta + delta) / 2 + (theta - delta) / 2 = theta by ring] at h
  unfold phaseChord
  nlinarith

private theorem sq_rpow_half {x : ℝ} (hx : 0 ≤ x) (p : ℝ) :
    (x ^ 2) ^ (p / 2) = x ^ p := by
  rw [← Real.rpow_natCast_mul hx 2 (p / 2)]
  congr 1
  ring

private theorem phase_energy_lower_bound (theta delta : ℝ)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    2 * phaseChord theta ^ 2 ≤
      phaseChord (theta + delta) ^ 2 + phaseChord (theta - delta) ^ 2 := by
  have hc : 0 ≤ Real.cos theta :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hcos := Real.cos_le_one delta
  rw [phaseChord_sq, phaseChord_sq, phaseChord_sq, Real.cos_add, Real.cos_sub]
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hcos)]

/-- The scalar-phase power sum dominates its Frobenius lower bound. This
gives the sharp dimension-free comparison after taking direct sums. -/
theorem phasePower_frobenius_lower_bound (p theta delta : ℝ)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) (hδ : delta ∈ Set.Icc 0 theta) :
    (2 : ℝ) ^ (p / 2) * phaseChord theta ^ p ≤ phasePower p theta delta := by
  have hpchord := phaseChord_nonneg (show 0 ≤ theta + delta by linarith [hθ.1, hδ.1])
    (show theta + delta ≤ Real.pi by linarith [hθ.2, hδ.2])
  have hmchord := phaseChord_nonneg (show 0 ≤ theta - delta by linarith [hδ.2])
    (show theta - delta ≤ Real.pi by linarith [hθ.2, hδ.1, Real.pi_pos])
  have hchord := phaseChord_nonneg hθ.1 (by linarith [hθ.2, Real.pi_pos])
  calc
    (2 : ℝ) ^ (p / 2) * phaseChord theta ^ p =
        (2 * phaseChord theta ^ 2) ^ (p / 2) := by
      rw [Real.mul_rpow (by norm_num) (sq_nonneg _), sq_rpow_half hchord]
    _ ≤ (phaseChord (theta + delta) ^ 2 + phaseChord (theta - delta) ^ 2) ^
        (p / 2) :=
      Real.rpow_le_rpow (by positivity) (phase_energy_lower_bound theta delta hθ)
        (by linarith)
    _ ≤ (phaseChord (theta + delta) ^ 2) ^ (p / 2) +
        (phaseChord (theta - delta) ^ 2) ^ (p / 2) :=
      Real.rpow_add_le_add_rpow (sq_nonneg _) (sq_nonneg _) (by linarith) (by linarith)
    _ = phasePower p theta delta := by
      rw [sq_rpow_half hpchord, sq_rpow_half hmchord]
      rfl

/-- The exact scalar minimum satisfies the same Frobenius lower bound. -/
theorem phaseMinimum_frobenius_lower_bound (p theta : ℝ)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    (2 : ℝ) ^ (p / 2) * phaseChord theta ^ p ≤ phaseMinimum p theta := by
  obtain ⟨delta, hδ, heq, _⟩ := exists_attains_phaseMinimum p theta hp1 hθ.1
  rw [heq]
  exact phasePower_frobenius_lower_bound p theta delta (by linarith) hp2 hθ hδ

/-- A phase that fixes one eigendirection gives an explicit upper bound on
the exact scalar minimum. -/
theorem phaseMinimum_le_endpoint (p theta : ℝ) (hp : 1 ≤ p) (hθ : 0 ≤ theta) :
    phaseMinimum p theta ≤ (2 * Real.sin theta) ^ p := by
  have h := phaseMinimum_le_phasePower p theta hp hθ ⟨hθ, le_rfl⟩
  have hhalf : (theta + theta) / 2 = theta := by ring
  simpa only [phasePower, phaseChord, hhalf, sub_self, zero_div, Real.sin_zero,
    mul_zero, Real.zero_rpow (show p ≠ 0 by linarith), add_zero] using h

/-- Every principal-plane cost is at most the cost of one eigenvalue `-1`. -/
theorem phaseMinimum_le_two_rpow (p theta : ℝ) (hp : 1 ≤ p)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    phaseMinimum p theta ≤ (2 : ℝ) ^ p := by
  apply (phaseMinimum_le_endpoint p theta hp hθ.1).trans
  exact Real.rpow_le_rpow
    (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])))
    (by linarith [Real.sin_le_one theta]) (by linarith)

/-- At a right angle the exact Schatten power minimum is `2^p`. -/
theorem phaseMinimum_right_angle (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    phaseMinimum p (Real.pi / 2) = (2 : ℝ) ^ p := by
  apply le_antisymm (phaseMinimum_le_two_rpow p (Real.pi / 2) hp1 ⟨by positivity, le_rfl⟩)
  have hc : phaseChord (Real.pi / 2) ^ 2 = 2 := by
    rw [phaseChord_sq, Real.cos_pi_div_two]
    norm_num
  have hnon : 0 ≤ phaseChord (Real.pi / 2) :=
    phaseChord_nonneg (by positivity) (by linarith [Real.pi_pos])
  have heq : (2 : ℝ) ^ (p / 2) * phaseChord (Real.pi / 2) ^ p = (2 : ℝ) ^ p := by
    calc
      _ = (2 * phaseChord (Real.pi / 2) ^ 2) ^ (p / 2) := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg _), sq_rpow_half hnon]
      _ = ((2 : ℝ) ^ 2) ^ (p / 2) := by rw [hc]; norm_num
      _ = (2 : ℝ) ^ p := sq_rpow_half (by norm_num) p
  rw [← heq]
  exact phaseMinimum_frobenius_lower_bound p (Real.pi / 2) hp1 hp2 ⟨by positivity, le_rfl⟩

/-- The canonical phase is within the sharp power-sum factor
`2^(1-p/2)` of the exact scalar-phase minimum, uniformly in the angle. -/
theorem canonical_phase_power_le_factor_mul_minimum (p theta : ℝ)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    phasePower p theta 0 ≤ (2 : ℝ) ^ (1 - p / 2) * phaseMinimum p theta := by
  have hcoeff : (2 : ℝ) ^ (1 - p / 2) * (2 : ℝ) ^ (p / 2) = 2 := by
    rw [← Real.rpow_add (by norm_num), show 1 - p / 2 + p / 2 = 1 by ring,
      Real.rpow_one]
  calc
    phasePower p theta 0 = 2 * phaseChord theta ^ p := by
      simp only [phasePower, add_zero, sub_zero, two_mul]
    _ = (2 : ℝ) ^ (1 - p / 2) * ((2 : ℝ) ^ (p / 2) * phaseChord theta ^ p) := by
      rw [← mul_assoc, hcoeff]
    _ ≤ (2 : ℝ) ^ (1 - p / 2) * phaseMinimum p theta :=
      mul_le_mul_of_nonneg_left (phaseMinimum_frobenius_lower_bound p theta hp1 hp2 hθ)
        (Real.rpow_nonneg (by norm_num) _)

/-- A right-angle plane attains the uniform comparison factor. -/
theorem canonical_phase_power_eq_factor_right_angle (p : ℝ)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    phasePower p (Real.pi / 2) 0 =
      (2 : ℝ) ^ (1 - p / 2) * phaseMinimum p (Real.pi / 2) := by
  rw [phaseMinimum_right_angle p hp1 hp2]
  have hc : phaseChord (Real.pi / 2) ^ 2 = 2 := by
    rw [phaseChord_sq, Real.cos_pi_div_two]
    norm_num
  have hnon : 0 ≤ phaseChord (Real.pi / 2) :=
    phaseChord_nonneg (by positivity) (by linarith [Real.pi_pos])
  have hpow : phaseChord (Real.pi / 2) ^ p = (2 : ℝ) ^ (p / 2) := by
    rw [← sq_rpow_half hnon p, hc]
  simp only [phasePower, add_zero, sub_zero, ← two_mul, hpow]
  calc
    (2 : ℝ) * 2 ^ (p / 2) = (2 : ℝ) ^ (1 + p / 2) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
    _ = (2 : ℝ) ^ (1 - p / 2 + p) := by congr 1; ring
    _ = (2 : ℝ) ^ (1 - p / 2) * 2 ^ p := Real.rpow_add (by norm_num) _ _

/-- Before the endpoint, a right-angle phase has strictly larger cost than
`2^p` for every exponent below two. -/
theorem phasePower_right_angle_gt_endpoint (p delta : ℝ) (hp2 : p < 2)
    (hδ : delta ∈ Set.Ico 0 (Real.pi / 2)) :
    (2 : ℝ) ^ p < phasePower p (Real.pi / 2) delta := by
  let u := (Real.pi / 2 + delta) / 2
  let v := (Real.pi / 2 - delta) / 2
  have hu0 : 0 < u := by dsimp [u]; linarith [hδ.1, Real.pi_pos]
  have hv0 : 0 < v := by dsimp [v]; linarith [hδ.2]
  have hup : u < Real.pi / 2 := by dsimp [u]; linarith [hδ.2]
  have hvp : v < Real.pi / 2 := by dsimp [v]; linarith [hδ.1, Real.pi_pos]
  have hs0 : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos])
  have ht0 : 0 < Real.sin v := Real.sin_pos_of_pos_of_lt_pi hv0 (by linarith [Real.pi_pos])
  have hs1 : Real.sin u < 1 := by
    simpa only [Real.sin_pi_div_two] using Real.strictMonoOn_sin
      ⟨by linarith [Real.pi_pos], hup.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hup
  have ht1 : Real.sin v < 1 := by
    simpa only [Real.sin_pi_div_two] using Real.strictMonoOn_sin
      ⟨by linarith [Real.pi_pos], hvp.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hvp
  have hs := Real.rpow_lt_rpow_of_exponent_gt hs0 hs1 hp2
  have ht := Real.rpow_lt_rpow_of_exponent_gt ht0 ht1 hp2
  rw [Real.rpow_two] at hs ht
  have hsum := phaseChord_add_sq (Real.pi / 2) delta
  rw [Real.cos_pi_div_two] at hsum
  change (2 * Real.sin u) ^ 2 + (2 * Real.sin v) ^ 2 = _ at hsum
  have hsum' : 1 < Real.sin u ^ p + Real.sin v ^ p := by nlinarith
  change (2 : ℝ) ^ p < (2 * Real.sin u) ^ p + (2 * Real.sin v) ^ p
  rw [Real.mul_rpow (by norm_num) hs0.le, Real.mul_rpow (by norm_num) ht0.le]
  nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p]

/-- At a right angle the endpoint is the unique scalar-phase minimizer. -/
theorem phasePower_right_angle_eq_minimum_iff (p delta : ℝ)
    (hp1 : 1 ≤ p) (hp2 : p < 2) (hδ : delta ∈ Set.Icc 0 (Real.pi / 2)) :
    phasePower p (Real.pi / 2) delta = phaseMinimum p (Real.pi / 2) ↔
      delta = Real.pi / 2 := by
  rw [phaseMinimum_right_angle p hp1 hp2.le]
  constructor
  · intro heq
    by_contra hne
    have hlt : delta < Real.pi / 2 := lt_of_le_of_ne hδ.2 hne
    exact (phasePower_right_angle_gt_endpoint p delta hp2 ⟨hδ.1, hlt⟩).ne' heq
  · rintro rfl
    have hhalf : (Real.pi / 2 + Real.pi / 2) / 2 = Real.pi / 2 := by ring
    simp only [phasePower, phaseChord, hhalf, Real.sin_pi_div_two, mul_one,
      sub_self, zero_div, Real.sin_zero, mul_zero,
      Real.zero_rpow (show p ≠ 0 by linarith), add_zero]

end
/-- The quadratic right-angle cost is flat in the scalar phase. This
endpoint degeneracy contrasts with the unique subquadratic phase. -/
theorem phasePower_two_right_angle (delta : ℝ) :
    phasePower 2 (Real.pi / 2) delta = 4 := by
  simp only [phasePower, Real.rpow_two]
  rw [phaseChord_add_sq, Real.cos_pi_div_two, mul_zero, zero_mul, sub_zero]

/-- **Endpoint optimizer-set obstruction.** Exact right-angle scalar
minimizers at exponents below two cannot converge to phase zero,
although phase zero is quadratic-optimal. No assertion about limits
of unrestricted ambient optimizer sets is inferred from this statement. -/
theorem not_tendsto_zero_of_right_angle_subquadratic_minimizers
    {ι : Type*} {l : Filter ι} [l.NeBot] (p delta : ι → ℝ)
    (h : ∀ᶠ i in l, 1 ≤ p i ∧ p i < 2 ∧ delta i ∈ Set.Icc 0 (Real.pi / 2) ∧
      phasePower (p i) (Real.pi / 2) (delta i) = phaseMinimum (p i) (Real.pi / 2)) :
    ¬Filter.Tendsto delta l (nhds 0) := by
  intro ht
  have hevent : delta =ᶠ[l] fun _ => Real.pi / 2 := by
    filter_upwards [h] with i hi
    exact (phasePower_right_angle_eq_minimum_iff (p i) (delta i) hi.1 hi.2.1 hi.2.2.1).mp
      hi.2.2.2
  have hc : Filter.Tendsto delta l (nhds (Real.pi / 2)) :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => Real.pi / 2) l
      (nhds (Real.pi / 2))).congr' hevent.symm
  have heq := tendsto_nhds_unique ht hc
  linarith [Real.pi_pos]

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
