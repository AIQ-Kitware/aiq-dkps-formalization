/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The two-focus circle problem for smoothed nuclear transport

The sum of distances to two conjugate foci is minimized on a circle either
at its rightmost point or at its intersection with the segment joining the
foci. This gives the explicit scalar phase transition for weighted nuclear
distance, equivalently the Charbonnier displacement penalty on unitaries.

The geometric inequalities are elementary; mathematical novelty is reserved
for the unrestricted constrained transport theorem, not these ingredients.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped ComplexConjugate

/-- The sum of distances to the conjugate foci `u + i v` and `u - i v`. -/
@[expose]
def twoFocusCost (u v : ℝ) (z : ℂ) : ℝ :=
  ‖(u : ℂ) + v * Complex.I - z‖ + ‖(u : ℂ) - v * Complex.I - z‖

private theorem norm_cartesian (x y : ℝ) :
    ‖(x : ℂ) + y * Complex.I‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply, pow_two]

/-- The segment between the foci gives a lower bound valid at every point. -/
theorem two_mul_im_le_twoFocusCost (u v : ℝ) (hv : 0 ≤ v) (z : ℂ) :
    2 * v ≤ twoFocusCost u v z := by
  have hdiff : ((u : ℂ) + v * Complex.I - z) -
      ((u : ℂ) - v * Complex.I - z) = (2 * v : ℂ) * Complex.I := by ring
  calc
    2 * v = ‖(2 * v : ℂ) * Complex.I‖ := by
      simp [abs_of_nonneg hv]
    _ = ‖((u : ℂ) + v * Complex.I - z) -
        ((u : ℂ) - v * Complex.I - z)‖ := congrArg norm hdiff.symm
    _ ≤ _ := norm_sub_le _ _

private theorem radial_average_bound (u v : ℝ) (z : ℂ) :
    2 * ‖((u - z.re : ℝ) : ℂ) + v * Complex.I‖ ≤ twoFocusCost u v z := by
  have havg : ((u : ℂ) + v * Complex.I - z) +
      conj ((u : ℂ) - v * Complex.I - z) =
      (2 : ℂ) * (((u - z.re : ℝ) : ℂ) + v * Complex.I) := by
    apply Complex.ext <;> simp <;> ring
  have h := norm_add_le ((u : ℂ) + v * Complex.I - z)
    (conj ((u : ℂ) - v * Complex.I - z))
  rw [havg, norm_mul, Complex.norm_ofNat, Complex.norm_conj] at h
  exact h

/-- If the circle is to the left of the focal segment, its rightmost
point minimizes the sum of distances. The bound holds on the entire disk. -/
theorem canonical_le_twoFocusCost (u v b : ℝ) (hub : b ≤ u)
    (z : ℂ) (hz : ‖z‖ ≤ b) :
    2 * Real.sqrt ((u - b) ^ 2 + v ^ 2) ≤ twoFocusCost u v z := by
  have hx : z.re ≤ b := (Complex.re_le_norm z).trans hz
  have hsq : (u - b) ^ 2 + v ^ 2 ≤ (u - z.re) ^ 2 + v ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ 2 * u - b - z.re by linarith)]
  calc
    _ ≤ 2 * Real.sqrt ((u - z.re) ^ 2 + v ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (by norm_num)
    _ = 2 * ‖((u - z.re : ℝ) : ℂ) + v * Complex.I‖ := by
      rw [norm_cartesian]
    _ ≤ _ := radial_average_bound u v z

/-- Away from the rightmost disk coordinate, the canonical comparison is
strict, including at the tangency threshold. -/
theorem canonical_lt_twoFocusCost (u v b : ℝ) (hub : b ≤ u)
    (z : ℂ) (hz : z.re < b) :
    2 * Real.sqrt ((u - b) ^ 2 + v ^ 2) < twoFocusCost u v z := by
  have hsq : (u - b) ^ 2 + v ^ 2 < (u - z.re) ^ 2 + v ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hz) (show 0 < 2 * u - b - z.re by linarith)]
  calc
    _ < 2 * Real.sqrt ((u - z.re) ^ 2 + v ^ 2) :=
      mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) hsq) (by norm_num)
    _ = 2 * ‖((u - z.re : ℝ) : ℂ) + v * Complex.I‖ := by
      rw [norm_cartesian]
    _ ≤ _ := radial_average_bound u v z

/-- Equality in the focal-segment bound forces the point onto the focal
line. This avoids differentiating the scalar objective. -/
theorem re_eq_of_twoFocusCost_eq_two_mul (u v : ℝ) (z : ℂ)
    (hz : twoFocusCost u v z = 2 * v) : z.re = u := by
  have hrad := radial_average_bound u v z
  rw [hz, norm_cartesian] at hrad
  have hs : Real.sqrt ((u - z.re) ^ 2 + v ^ 2) ≤ v := by linarith
  have hsq : (u - z.re) ^ 2 + v ^ 2 ≤ v ^ 2 := (Real.sqrt_le_iff).mp hs |>.2
  nlinarith [sq_nonneg (u - z.re)]

/-- The rightmost circle point attains the canonical bound. -/
theorem twoFocusCost_ofReal (u v b : ℝ) :
    twoFocusCost u v (b : ℂ) = 2 * Real.sqrt ((u - b) ^ 2 + v ^ 2) := by
  have hp : (u : ℂ) + v * Complex.I - b = ((u - b : ℝ) : ℂ) + v * Complex.I := by
    push_cast
    ring
  have hm : (u : ℂ) - v * Complex.I - b = ((u - b : ℝ) : ℂ) + (-v) * Complex.I := by
    push_cast
    ring
  rw [twoFocusCost, hp, hm, norm_cartesian]
  have hn : ‖((u - b : ℝ) : ℂ) + (-v) * Complex.I‖ =
      Real.sqrt ((u - b) ^ 2 + (-v) ^ 2) := by
    simpa only [Complex.ofReal_neg] using norm_cartesian (u - b) (-v)
  rw [hn, neg_sq]
  ring

/-- The upper intersection of a circle with the focal line. -/
@[expose]
def focalIntersection (u b : ℝ) : ℂ :=
  (u : ℂ) + Real.sqrt (b ^ 2 - u ^ 2) * Complex.I

/-- The focal intersection lies on the specified circle. -/
theorem norm_focalIntersection (u b : ℝ) (hu : 0 ≤ u) (hb : u ≤ b) :
    ‖focalIntersection u b‖ = b := by
  have hsq : 0 ≤ b ^ 2 - u ^ 2 := by nlinarith
  rw [focalIntersection, norm_cartesian, Real.sq_sqrt hsq]
  rw [show u ^ 2 + (b ^ 2 - u ^ 2) = b ^ 2 by ring,
    Real.sqrt_sq (show 0 ≤ b by linarith)]

/-- If the circle meets the focal segment, its upper intersection attains
the triangle-inequality lower bound. -/
theorem twoFocusCost_focalIntersection (u v b : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hub : u ≤ b) (hb : b ^ 2 ≤ u ^ 2 + v ^ 2) :
    twoFocusCost u v (focalIntersection u b) = 2 * v := by
  let y := Real.sqrt (b ^ 2 - u ^ 2)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hsq : 0 ≤ b ^ 2 - u ^ 2 := by nlinarith
  have hysq : y ^ 2 = b ^ 2 - u ^ 2 := Real.sq_sqrt hsq
  have hyv : y ≤ v := by nlinarith
  have hp : (u : ℂ) + v * Complex.I - focalIntersection u b =
      ((v - y : ℝ) : ℂ) * Complex.I := by
    dsimp [focalIntersection, y]
    push_cast
    ring
  have hm : (u : ℂ) - v * Complex.I - focalIntersection u b =
      ((-v - y : ℝ) : ℂ) * Complex.I := by
    dsimp [focalIntersection, y]
    push_cast
    ring
  rw [twoFocusCost, hp, hm]
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith : 0 ≤ v - y), abs_of_nonpos (by linarith : -v - y ≤ 0)]
  ring

/-- A point on the circle of radius `b`, parametrized by its phase. -/
@[expose]
def circlePhase (b delta : ℝ) : ℂ := b * Complex.exp (delta * Complex.I)

theorem norm_circlePhase (b delta : ℝ) (hb : 0 ≤ b) :
    ‖circlePhase b delta‖ = b := by
  simp [circlePhase, abs_of_nonneg hb]

private theorem circlePhase_re (b delta : ℝ) :
    (circlePhase b delta).re = b * Real.cos delta := by
  simp [circlePhase, Complex.exp_ofReal_mul_I_re]

private theorem circlePhase_im (b delta : ℝ) :
    (circlePhase b delta).im = b * Real.sin delta := by
  simp [circlePhase, Complex.exp_ofReal_mul_I_im]

/-- The inverse-cosine phase gives exactly the upper focal intersection. -/
theorem circlePhase_arccos (u b : ℝ) (hu : 0 ≤ u) (hub : u ≤ b) (hb : 0 < b) :
    circlePhase b (Real.arccos (u / b)) = focalIntersection u b := by
  have hr0 : 0 ≤ u / b := div_nonneg hu hb.le
  have hr1 : u / b ≤ 1 := (div_le_one hb).mpr hub
  have hre : (circlePhase b (Real.arccos (u / b))).re = u := by
    rw [circlePhase_re, Real.cos_arccos (by linarith) hr1]
    field_simp
  have him0 : 0 ≤ (circlePhase b (Real.arccos (u / b))).im := by
    rw [circlePhase_im, Real.sin_arccos]
    positivity
  have hnorm := norm_circlePhase b (Real.arccos (u / b)) hb.le
  have himsq := Complex.sq_norm_sub_sq_re (circlePhase b (Real.arccos (u / b)))
  rw [hnorm, hre] at himsq
  have hsq : 0 ≤ b ^ 2 - u ^ 2 := by nlinarith
  apply Complex.ext
  · simpa [focalIntersection] using hre
  · simp only [focalIntersection, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, zero_add, add_zero]
    nlinarith [Real.sq_sqrt hsq, Real.sqrt_nonneg (b ^ 2 - u ^ 2)]

/-- Weighted nuclear cost on one complex scalar-phase rotation plane. -/
@[expose]
def weightedPhaseCost (a b theta delta : ℝ) : ℝ :=
  twoFocusCost (a * Real.cos theta) (a * Real.sin theta) (circlePhase b delta)

/-- The explicit weighted nuclear minimum on one principal plane. -/
@[expose]
def weightedPhaseMinimum (a b theta : ℝ) : ℝ :=
  if b ≤ a * Real.cos theta then
    2 * Real.sqrt (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta)
  else 2 * a * Real.sin theta

/-- A fixed direction pair contributes twice the radial distance. -/
theorem weightedPhaseMinimum_zero (a b : ℝ) (hab : b ≤ a) :
    weightedPhaseMinimum a b 0 = 2 * (a - b) := by
  rw [weightedPhaseMinimum, Real.cos_zero, mul_one, ite_eq_left hab]
  rw [show a ^ 2 + b ^ 2 - 2 * a * b * 1 = (a - b) ^ 2 by ring,
    Real.sqrt_sq (sub_nonneg.mpr hab)]

/-- The nonnegative attaining scalar phase. -/
@[expose]
def optimalWeightedPhase (a b theta : ℝ) : ℝ :=
  if b ≤ a * Real.cos theta then 0 else Real.arccos (a * Real.cos theta / b)

private theorem focal_radius_identity (a b theta : ℝ) :
    (a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2 =
      a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta := by
  have h := congrArg (fun t : ℝ => a ^ 2 * t) (Real.sin_sq_add_cos_sq theta)
  nlinarith

/-- The explicit value bounds every phase, including phases outside the
usual interval between zero and the physical angle. -/
theorem weightedPhaseMinimum_le_cost (a b theta : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) (delta : ℝ) :
    weightedPhaseMinimum a b theta ≤ weightedPhaseCost a b theta delta := by
  unfold weightedPhaseMinimum weightedPhaseCost
  split_ifs with hc
  · rw [← focal_radius_identity]
    exact canonical_le_twoFocusCost _ _ _ hc _ (norm_circlePhase b delta hb).le
  · simpa only [mul_assoc] using two_mul_im_le_twoFocusCost _ _
      (mul_nonneg ha (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos]))) _

/-- Independent circle geometry gives the exact attaining phase and value,
without any stationary-point argument. -/
theorem weightedPhaseCost_optimal (a b theta : ℝ) (hb : 0 < b) (hab : b ≤ a)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    weightedPhaseCost a b theta (optimalWeightedPhase a b theta) =
      weightedPhaseMinimum a b theta := by
  have ha : 0 ≤ a := hb.le.trans hab
  have hc0 : 0 ≤ a * Real.cos theta :=
    mul_nonneg ha (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  unfold optimalWeightedPhase weightedPhaseMinimum
  split_ifs with hc
  · change twoFocusCost (a * Real.cos theta) (a * Real.sin theta)
      (circlePhase b 0) = _
    have hz : circlePhase b 0 = (b : ℂ) := by simp [circlePhase]
    rw [hz, twoFocusCost_ofReal, focal_radius_identity]
  · change twoFocusCost (a * Real.cos theta) (a * Real.sin theta)
      (circlePhase b (Real.arccos (a * Real.cos theta / b))) = _
    rw [circlePhase_arccos _ _ hc0 (le_of_not_ge hc) hb]
    have hradius : b ^ 2 ≤ (a * Real.cos theta) ^ 2 + (a * Real.sin theta) ^ 2 := by
      have hcircle := congrArg (fun t : ℝ => a ^ 2 * t) (Real.sin_sq_add_cos_sq theta)
      have habsq : b ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hb.le ha).mpr hab
      nlinarith
    simpa only [mul_assoc] using twoFocusCost_focalIntersection
      (a * Real.cos theta) (a * Real.sin theta) b hc0
      (mul_nonneg ha (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos]))) (le_of_not_ge hc) hradius

/-- The explicit attaining phase lies in the physical scalar-phase interval. -/
theorem optimalWeightedPhase_mem (a b theta : ℝ) (hb : 0 < b) (hab : b ≤ a)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    optimalWeightedPhase a b theta ∈ Set.Icc 0 theta := by
  unfold optimalWeightedPhase
  split_ifs
  · exact ⟨le_rfl, hθ.1⟩
  · refine ⟨Real.arccos_nonneg _, ?_⟩
    have hc : 0 ≤ Real.cos theta := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have hratio : Real.cos theta ≤ a * Real.cos theta / b := by
      apply (le_div_iff₀ hb).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) hc]
    calc
      _ ≤ Real.arccos (Real.cos theta) := Real.arccos_le_arccos hratio
      _ = theta := Real.arccos_cos hθ.1 (by linarith [hθ.2, Real.pi_pos])

/-- The weighted scalar phase problem has an explicit global minimizer. -/
theorem optimalWeightedPhase_isMinOn (a b theta : ℝ) (hb : 0 < b) (hab : b ≤ a)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    IsMinOn (weightedPhaseCost a b theta) Set.univ (optimalWeightedPhase a b theta) := by
  intro delta _
  rw [weightedPhaseCost_optimal a b theta hb hab hθ]
  exact weightedPhaseMinimum_le_cost a b theta (hb.le.trans hab) hb.le hθ delta

/-- Negating the angle conjugates the scalar circle phase. -/
theorem circlePhase_neg_eq_star (b delta : ℝ) :
    circlePhase b (-delta) = star (circlePhase b delta) := by
  change circlePhase b (-delta) = conj (circlePhase b delta)
  have hexp : ((-delta : ℝ) : ℂ) * Complex.I = conj ((delta : ℂ) * Complex.I) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring
  unfold circlePhase
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hexp]

/-- Reversing a scalar phase preserves the weighted two-focus cost. -/
theorem weightedPhaseCost_neg (a b theta delta : ℝ) :
    weightedPhaseCost a b theta (-delta) = weightedPhaseCost a b theta delta := by
  have hphase : circlePhase b (-delta) = conj (circlePhase b delta) :=
    circlePhase_neg_eq_star b delta
  have hp : (a * Real.cos theta : ℂ) + (a * Real.sin theta) * Complex.I -
      circlePhase b (-delta) =
      conj ((a * Real.cos theta : ℂ) - (a * Real.sin theta) * Complex.I - circlePhase b delta) := by
    rw [hphase]
    simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hm : (a * Real.cos theta : ℂ) - (a * Real.sin theta) * Complex.I -
      circlePhase b (-delta) =
      conj ((a * Real.cos theta : ℂ) + (a * Real.sin theta) * Complex.I - circlePhase b delta) := by
    rw [hphase]
    simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  unfold weightedPhaseCost twoFocusCost
  simp only [Complex.ofReal_mul]
  rw [hp, hm, Complex.norm_conj, Complex.norm_conj, add_comm]

/-- The attaining nonnegative scalar phase is unique, including at the
critical angle and at a right angle. -/
theorem weightedPhaseCost_eq_minimum_iff (a b theta delta : ℝ)
    (hb : 0 < b) (hab : b ≤ a) (hθ : theta ∈ Set.Icc 0 (Real.pi / 2))
    (hδ : delta ∈ Set.Icc 0 theta) :
    weightedPhaseCost a b theta delta = weightedPhaseMinimum a b theta ↔
      delta = optimalWeightedPhase a b theta := by
  constructor
  · intro heq
    have hδπ : delta ≤ Real.pi := by linarith [hδ.2, hθ.2, Real.pi_pos]
    by_cases hc : b ≤ a * Real.cos theta
    · have hre : (circlePhase b delta).re = b := by
        apply le_antisymm ((Complex.re_le_norm _).trans (norm_circlePhase b delta hb.le).le)
        by_contra h
        have hstrict := canonical_lt_twoFocusCost (a * Real.cos theta)
          (a * Real.sin theta) b hc (circlePhase b delta) (lt_of_not_ge h)
        change 2 * Real.sqrt ((a * Real.cos theta - b) ^ 2 + (a * Real.sin theta) ^ 2) <
          weightedPhaseCost a b theta delta at hstrict
        rw [focal_radius_identity, heq, weightedPhaseMinimum, ite_eq_left hc] at hstrict
        exact lt_irrefl _ hstrict
      rw [circlePhase_re] at hre
      have hcos : Real.cos delta = Real.cos 0 := by
        rw [Real.cos_zero]
        nlinarith
      have hzero : delta = 0 := Real.strictAntiOn_cos.injOn
        ⟨hδ.1, hδπ⟩ ⟨le_rfl, Real.pi_pos.le⟩ hcos
      simpa only [optimalWeightedPhase, ite_eq_left hc] using hzero
    · have hcost : twoFocusCost (a * Real.cos theta) (a * Real.sin theta)
          (circlePhase b delta) = 2 * (a * Real.sin theta) := by
        simpa only [weightedPhaseCost, weightedPhaseMinimum, ite_eq_right hc, mul_assoc] using heq
      have hre := re_eq_of_twoFocusCost_eq_two_mul _ _ _ hcost
      rw [circlePhase_re] at hre
      have hcos : Real.cos delta = a * Real.cos theta / b :=
        (eq_div_iff hb.ne').mpr (by simpa only [mul_comm] using hre)
      rw [optimalWeightedPhase, ite_eq_right hc, ← hcos, Real.arccos_cos hδ.1 hδπ]
  · rintro rfl
    exact weightedPhaseCost_optimal a b theta hb hab hθ

/-- The outer radius associated with a positive Charbonnier smoothing scale. -/
@[expose]
def smoothingRadius (tau : ℝ) : ℝ := (tau + Real.sqrt (tau ^ 2 + 4)) / 2

theorem one_lt_smoothingRadius (tau : ℝ) (hτ : 0 < tau) :
    1 < smoothingRadius tau := by
  have hs : 2 ≤ Real.sqrt (tau ^ 2 + 4) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg tau]
  dsimp [smoothingRadius]
  linarith

theorem smoothingRadius_sub_inv (tau : ℝ) (hτ : 0 < tau) :
    smoothingRadius tau - (smoothingRadius tau)⁻¹ = tau := by
  have ha : 0 < smoothingRadius tau := lt_trans zero_lt_one (one_lt_smoothingRadius tau hτ)
  have heq : smoothingRadius tau ^ 2 - tau * smoothingRadius tau = 1 := by
    dsimp [smoothingRadius]
    nlinarith [Real.sq_sqrt (show 0 ≤ tau ^ 2 + 4 by positivity)]
  apply (mul_right_inj' ha.ne').mp
  rw [mul_sub, mul_inv_cancel₀ ha.ne']
  nlinarith

theorem smoothingRadius_sq_add_inv_sq (tau : ℝ) (hτ : 0 < tau) :
    smoothingRadius tau ^ 2 + ((smoothingRadius tau)⁻¹) ^ 2 = tau ^ 2 + 2 := by
  have ha : 0 < smoothingRadius tau := lt_trans zero_lt_one (one_lt_smoothingRadius tau hτ)
  have hdiff := congrArg (fun x : ℝ => x ^ 2) (smoothingRadius_sub_inv tau hτ)
  have hprod : smoothingRadius tau * (smoothingRadius tau)⁻¹ = 1 :=
    mul_inv_cancel₀ ha.ne'
  nlinarith

/-- The smoothed spectral cost on one scalar-phase plane. -/
@[expose]
def smoothedPhaseCost (tau theta delta : ℝ) : ℝ :=
  weightedPhaseCost (smoothingRadius tau) (smoothingRadius tau)⁻¹ theta delta - 2 * tau

/-- The explicit minimum, in the original smoothing parameter. -/
@[expose]
def smoothedPhaseMinimum (tau theta : ℝ) : ℝ :=
  if (smoothingRadius tau)⁻¹ ≤ smoothingRadius tau * Real.cos theta then
    2 * (Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos theta) - tau)
  else 2 * smoothingRadius tau * Real.sin theta - 2 * tau

/-- The explicit phase that attains the smoothed scalar minimum. -/
@[expose]
def optimalSmoothedPhase (tau theta : ℝ) : ℝ :=
  optimalWeightedPhase (smoothingRadius tau) (smoothingRadius tau)⁻¹ theta

private theorem inverse_radius_le_radius (tau : ℝ) (hτ : 0 < tau) :
    (smoothingRadius tau)⁻¹ ≤ smoothingRadius tau := by
  have ha := one_lt_smoothingRadius tau hτ
  exact (inv_le_one_of_one_le₀ ha.le).trans ha.le

/-- The displayed smoothing formula is exactly the weighted circle minimum
after removing the two scalar baseline contributions. -/
theorem smoothedPhaseMinimum_eq_weighted (tau theta : ℝ) (hτ : 0 < tau) :
    smoothedPhaseMinimum tau theta =
      weightedPhaseMinimum (smoothingRadius tau) (smoothingRadius tau)⁻¹ theta - 2 * tau := by
  have ha : 0 < smoothingRadius tau := lt_trans zero_lt_one (one_lt_smoothingRadius tau hτ)
  have hrad := smoothingRadius_sq_add_inv_sq tau hτ
  have hprod : smoothingRadius tau * (smoothingRadius tau)⁻¹ = 1 :=
    mul_inv_cancel₀ ha.ne'
  unfold smoothedPhaseMinimum weightedPhaseMinimum
  split_ifs
  · have hr : smoothingRadius tau ^ 2 + ((smoothingRadius tau)⁻¹) ^ 2 -
        2 * smoothingRadius tau * (smoothingRadius tau)⁻¹ * Real.cos theta =
        tau ^ 2 + 2 - 2 * Real.cos theta := by
      rw [hrad]
      nlinarith [congrArg (fun t : ℝ => 2 * t * Real.cos theta) hprod]
    rw [hr]
    ring
  · rfl

/-- Zero principal angles contribute zero to the smoothed optimum. -/
theorem smoothedPhaseMinimum_zero_angle (tau : ℝ) (htau : 0 < tau) :
    smoothedPhaseMinimum tau 0 = 0 := by
  rw [smoothedPhaseMinimum_eq_weighted tau 0 htau,
    weightedPhaseMinimum_zero _ _ (inverse_radius_le_radius tau htau),
    smoothingRadius_sub_inv tau htau]
  ring

/-- Each right-angle plane contributes one displacement of size two. -/
theorem smoothedPhaseMinimum_right_angle (tau : ℝ) (htau : 0 < tau) :
    smoothedPhaseMinimum tau (Real.pi / 2) = Real.sqrt (tau ^ 2 + 4) - tau := by
  have heta : 0 < smoothingRadius tau := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  rw [smoothedPhaseMinimum, Real.cos_pi_div_two, mul_zero,
    ite_eq_right (not_le_of_gt (inv_pos.mpr heta)), Real.sin_pi_div_two, mul_one]
  dsimp only [smoothingRadius]
  ring

/-- The smoothed minimum is attained by its explicit inverse-cosine phase. -/
theorem smoothedPhaseCost_optimal (tau theta : ℝ) (hτ : 0 < tau)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    smoothedPhaseCost tau theta (optimalSmoothedPhase tau theta) =
      smoothedPhaseMinimum tau theta := by
  have ha : 0 < smoothingRadius tau := lt_trans zero_lt_one (one_lt_smoothingRadius tau hτ)
  rw [smoothedPhaseCost, optimalSmoothedPhase,
    weightedPhaseCost_optimal _ _ _ (inv_pos.mpr ha) (inverse_radius_le_radius tau hτ) hθ,
    smoothedPhaseMinimum_eq_weighted tau theta hτ]

/-- The displayed smoothed minimum bounds the scalar-phase cost globally. -/
theorem smoothedPhaseMinimum_le_cost (tau theta : ℝ) (hτ : 0 < tau)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) (delta : ℝ) :
    smoothedPhaseMinimum tau theta ≤ smoothedPhaseCost tau theta delta := by
  have ha : 0 < smoothingRadius tau := lt_trans zero_lt_one (one_lt_smoothingRadius tau hτ)
  rw [smoothedPhaseMinimum_eq_weighted tau theta hτ, smoothedPhaseCost]
  exact sub_le_sub_right (weightedPhaseMinimum_le_cost _ _ _ ha.le (inv_nonneg.mpr ha.le)
    hθ delta) _

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
