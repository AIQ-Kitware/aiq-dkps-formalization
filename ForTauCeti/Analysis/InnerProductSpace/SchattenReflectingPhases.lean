/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The two phases of a reflecting-unitary variation

For a nontrivial reflection block, a source-preserving diagonal phase
variation has a phase near zero and an offset from the phase at pi.
The vanishing phase has zero first derivative. Its chord power is
therefore negligible compared with the negative quadratic contribution
from the opposite phase when the exponent is greater than one.
-/

public section

noncomputable section

namespace TauCeti

open Asymptotics Filter Set
open scoped Topology

/-- The phase issuing from the eigenvalue one of a reflecting variation. -/
@[expose] def reflectingSmallPhase (d t : ℝ) : ℝ :=
  d * t / 2 - Real.arcsin (d * Real.sin (t / 2))

/-- The offset from pi of the other eigenphase of a reflecting variation. -/
@[expose] def reflectingLargeOffset (d t : ℝ) : ℝ :=
  d * t / 2 + Real.arcsin (d * Real.sin (t / 2))

/-- The sum of the two displacement chord powers along this variation. -/
@[expose] def reflectingPhasePower (p d t : ℝ) : ℝ :=
  |2 * Real.sin (reflectingSmallPhase d t / 2)| ^ p +
    |2 * Real.cos (reflectingLargeOffset d t / 2)| ^ p

private theorem second_order_remainder {f : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    (fun t => f t - f 0 - t * deriv f 0 - t ^ 2 / 2 * deriv (deriv f) 0)
      =o[𝓝 0] fun t => t ^ 2 := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hf.eventually (by norm_num))
  let V := Metric.ball (0 : ℝ) r
  have hV : IsOpen V := Metric.isOpen_ball
  have h0 : (0 : ℝ) ∈ V := Metric.mem_ball_self hr
  have hcont : ContDiffOn ℝ 2 f V := fun x hx =>
    (hball (Metric.mem_ball.mp hx)).contDiffWithinAt
  have h := taylor_isLittleO (convex_ball (0 : ℝ) r) h0 hcont
  rw [hV.nhdsWithin_eq h0] at h
  have hpoly (t : ℝ) : taylorWithinEval f 2 V 0 t =
      f 0 + t * deriv f 0 + t ^ 2 / 2 * deriv (deriv f) 0 := by
    rw [taylorWithinEval_succ f 1 V 0 t, taylorWithinEval_succ f 0 V 0 t,
      taylor_within_zero_eval,
      iteratedDerivWithin_of_isOpen (n := 1) hV h0,
      iteratedDerivWithin_of_isOpen (n := 2) hV h0]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_zero, Nat.cast_one,
      zero_add, one_mul, mul_one, inv_one, sub_zero, pow_one, smul_eq_mul]
    ring
  simp only [sub_zero] at h
  convert h using 1
  funext t
  rw [hpoly]
  ring

private theorem isBigO_sq_of_two_zeros {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hdf0 : deriv f 0 = 0) :
    f =O[𝓝 0] fun t => t ^ 2 := by
  have h := second_order_remainder hf
  simp only [hf0, hdf0, sub_zero, mul_zero] at h
  have hp : (fun t : ℝ => t ^ 2 / 2 * deriv (deriv f) 0) =O[𝓝 0] fun t => t ^ 2 := by
    convert (isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0)).const_mul_left
      (deriv (deriv f) 0 / 2) using 1
    funext t
    ring
  simpa only [sub_add_cancel] using h.isBigO.add hp

private theorem rpow_sq_isLittleO_sq (p : ℝ) (hp : 1 < p) :
    (fun t : ℝ => (t ^ 2) ^ p) =o[𝓝 0] fun t => t ^ 2 := by
  have ht : Tendsto (fun t : ℝ => (t ^ 2) ^ (p - 1)) (𝓝 0) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const (by linarith : 0 ≤ p - 1)).comp
      (continuous_id.pow 2)).tendsto (0 : ℝ)
    simpa [Function.comp_def, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
      using h
  have ho := ((isLittleO_one_iff ℝ).mpr ht).mul_isBigO
    (isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0))
  convert ho using 1
  · funext t
    by_cases ht0 : t = 0
    · simp [ht0, Real.zero_rpow (by linarith : p ≠ 0)]
    · calc
        (t ^ 2) ^ p = (t ^ 2) ^ (1 + (p - 1)) := by congr 1; ring
        _ = (t ^ 2) ^ 1 * (t ^ 2) ^ (p - 1) :=
          Real.rpow_add (sq_pos_of_ne_zero ht0) _ _
        _ = (t ^ 2) ^ (p - 1) * t ^ 2 := by rw [Real.rpow_one, mul_comm]
  · funext t
    simp

private theorem chord_power_isLittleO_sq_of_two_zeros (p : ℝ) (hp : 1 < p)
    {f : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hdf0 : deriv f 0 = 0) :
    (fun t => |f t| ^ p) =o[𝓝 0] fun t => t ^ 2 := by
  have hb := (isBigO_sq_of_two_zeros hf hf0 hdf0).norm_left
  have hpw := hb.rpow (by linarith : 0 ≤ p) (Eventually.of_forall (fun t => sq_nonneg t))
  simpa only [Real.norm_eq_abs] using hpw.trans_isLittleO (rpow_sq_isLittleO_sq p hp)

/-- The small eigenphase is smooth and has zero first derivative at the
reflecting transporter. No restriction on `d` is needed locally. -/
theorem reflectingSmallPhase_regular (d : ℝ) :
    ContDiffAt ℝ 2 (reflectingSmallPhase d) 0 ∧ reflectingSmallPhase d 0 = 0 ∧
      HasDerivAt (reflectingSmallPhase d) 0 0 := by
  have hhalf := (hasDerivAt_id (0 : ℝ)).div_const (2 : ℝ)
  have hinner := hhalf.sin.const_mul d
  have ha : HasDerivAt Real.arcsin 1 (d * Real.sin ((0 : ℝ) / 2)) := by
    convert Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1) using 1 <;> norm_num
  have harc := ha.comp (0 : ℝ) hinner
  have hcont : ContDiffAt ℝ 2 (reflectingSmallPhase d) 0 := by
    change ContDiffAt ℝ 2 (fun t : ℝ => d * t / 2 - Real.arcsin (d * Real.sin (t / 2))) 0
    have harg : ContDiffAt ℝ 2 (fun t : ℝ => d * Real.sin (t / 2)) 0 := by fun_prop
    have ha2 : ContDiffAt ℝ 2 Real.arcsin (d * Real.sin ((0 : ℝ) / 2)) :=
      Real.contDiffAt_arcsin (by norm_num) (by norm_num)
    have hlin : ContDiffAt ℝ 2 (fun t : ℝ => d * t / 2) 0 := by fun_prop
    exact hlin.sub (ha2.comp (f := fun t : ℝ => d * Real.sin (t / 2))
      (g := Real.arcsin) (0 : ℝ) harg)
  refine ⟨hcont, by simp [reflectingSmallPhase], ?_⟩
  convert ((hasDerivAt_id (0 : ℝ)).const_mul d |>.div_const 2).sub harc using 1
  · rfl
  · norm_num
    ring

/-- The displacement issuing from eigenvalue one costs `o(t²)` for
every exponent greater than one. No second derivative of its chord
power at zero is assumed. -/
theorem reflectingSmallPhase_chord_power_isLittleO_sq
    (p d : ℝ) (hp : 1 < p) :
    (fun t => |2 * Real.sin (reflectingSmallPhase d t / 2)| ^ p)
      =o[𝓝 0] fun t => t ^ 2 := by
  obtain ⟨hcont, hzero, hder⟩ := reflectingSmallPhase_regular d
  apply chord_power_isLittleO_sq_of_two_zeros p hp
    (by fun_prop) (by simp [hzero])
  have h := (hder.div_const 2).sin.const_mul 2
  simpa only [div_zero, zero_div, mul_zero] using h.deriv

private theorem quadratic_remainder_comp {f q : ℝ → ℝ} {v k d : ℝ}
    (h : (fun t => f t - v - k * t ^ 2) =o[𝓝 0] fun t => t ^ 2)
    (hq : HasDerivAt q d 0) (hq0 : q 0 = 0) :
    (fun t => f (q t) - v - (k * d ^ 2) * t ^ 2) =o[𝓝 0] fun t => t ^ 2 := by
  have hqb : q =O[𝓝 0] fun t : ℝ => t := by
    simpa only [hq0, sub_zero] using hq.isBigO_sub
  have hqo : (fun t => q t - d * t) =o[𝓝 0] fun t : ℝ => t := by
    simpa only [hq0, sub_zero, smul_eq_mul, mul_comm] using hq.isLittleO
  have hqt : Tendsto q (𝓝 0) (𝓝 0) := by
    simpa only [hq0] using hq.continuousAt.tendsto
  have hcomp := (h.comp_tendsto hqt).trans_isBigO (hqb.pow 2)
  have hsum : (fun t => q t + d * t) =O[𝓝 0] fun t : ℝ => t :=
    hqb.add ((isBigO_refl (fun t : ℝ => t) (𝓝 0)).const_mul_left d)
  have hsq := (hqo.mul_isBigO hsum).const_mul_left k
  simp only [← sq] at hsq
  convert hcomp.add hsq using 1
  funext t
  dsimp only [Function.comp_def]
  ring

private theorem cos_chord_power_remainder (p : ℝ) :
    (fun t : ℝ => (2 * Real.cos (t / 2)) ^ p - (2 : ℝ) ^ p +
      p * (2 : ℝ) ^ p / 8 * t ^ 2) =o[𝓝 0] fun t => t ^ 2 := by
  let b := fun t : ℝ => 2 * Real.cos (t / 2)
  let f := fun t : ℝ => b t ^ p
  let slope := fun t : ℝ => -Real.sin (t / 2) * p * b t ^ (p - 1)
  have hb : ContDiff ℝ 2 b := by dsimp only [b]; fun_prop
  have hbder (t : ℝ) : HasDerivAt b (-Real.sin (t / 2)) t := by
    convert ((hasDerivAt_id t).div_const 2).cos.const_mul 2 using 1
    · rfl
    · simp only [id_eq]
      ring
  have hb0 : b 0 = 2 := by simp [b]
  have hf : ContDiffAt ℝ 2 f 0 :=
    hb.contDiffAt.rpow_const_of_ne (by rw [hb0]; norm_num)
  have hd0 : HasDerivAt f 0 0 := by
    simpa only [Real.sin_zero, zero_div, neg_zero, zero_mul] using
      ((hbder 0).rpow_const (p := p) (Or.inl (by rw [hb0]; norm_num)))
  have hdeq : deriv f =ᶠ[𝓝 0] slope := by
    filter_upwards [hb.continuous.continuousAt.eventually_ne
      (by rw [hb0]; norm_num : b 0 ≠ 0)] with t ht
    exact ((hbder t).rpow_const (Or.inl ht)).deriv
  have hsder : HasDerivAt slope (-(p * (2 : ℝ) ^ (p - 1) / 2)) 0 := by
    have hsin := ((hasDerivAt_id (0 : ℝ)).div_const 2).sin.neg.mul_const p
    have hpow := (hbder 0).rpow_const (p := p - 1) (Or.inl (by rw [hb0]; norm_num))
    convert hsin.mul hpow using 1
    · rfl
    · simp only [id_eq, zero_div, Real.cos_zero, Real.sin_zero, neg_zero, zero_mul,
        hb0, mul_zero, add_zero]
      ring
  have hdd : deriv (deriv f) 0 = -(p * (2 : ℝ) ^ (p - 1) / 2) :=
    hdeq.deriv_eq.trans hsder.deriv
  have h := second_order_remainder hf
  rw [show f 0 = (2 : ℝ) ^ p by rw [show f 0 = b 0 ^ p from rfl, hb0],
    hd0.deriv, hdd, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one] at h
  convert h using 1
  funext t
  dsimp only [f, b]
  ring

/-- The large eigenphase has the expected first-order offset from pi. -/
theorem reflectingLargeOffset_hasDerivAt (d : ℝ) :
    HasDerivAt (reflectingLargeOffset d) d 0 := by
  have hinner := ((hasDerivAt_id (0 : ℝ)).div_const 2).sin.const_mul d
  have ha : HasDerivAt Real.arcsin 1 (d * Real.sin ((0 : ℝ) / 2)) := by
    convert Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1) using 1 <;> norm_num
  convert ((hasDerivAt_id (0 : ℝ)).const_mul d |>.div_const 2).add
    (ha.comp (0 : ℝ) hinner) using 1
  · rfl
  · norm_num
    ring

/-- Exact quadratic cost expansion for a reflecting two-phase variation.
The contribution from its zero-displacement singular value is included.
The exponent is allowed to exceed two; only `p>1` is used. -/
theorem reflectingPhasePower_second_order (p d : ℝ) (hp : 1 < p) :
    (fun t => reflectingPhasePower p d t - (2 : ℝ) ^ p +
      p * (2 : ℝ) ^ p * d ^ 2 / 8 * t ^ 2) =o[𝓝 0] fun t => t ^ 2 := by
  have hs := reflectingSmallPhase_chord_power_isLittleO_sq p d hp
  have hq0 : reflectingLargeOffset d 0 = 0 := by simp [reflectingLargeOffset]
  have hcos := cos_chord_power_remainder p
  have hc : (fun t : ℝ => (2 * Real.cos (t / 2)) ^ p - (2 : ℝ) ^ p -
      (-p * (2 : ℝ) ^ p / 8) * t ^ 2) =o[𝓝 0] fun t => t ^ 2 := by
    convert hcos using 1
    funext t
    ring
  have hlarge := quadratic_remainder_comp hc (reflectingLargeOffset_hasDerivAt d) hq0
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ),
      0 < 2 * Real.cos (reflectingLargeOffset d t / 2) := by
    have hcont : ContinuousAt (fun t => 2 * Real.cos (reflectingLargeOffset d t / 2)) 0 :=
      continuousAt_const.mul (Real.continuous_cos.continuousAt.comp
        ((reflectingLargeOffset_hasDerivAt d).continuousAt.div_const 2))
    exact hcont (Ioi_mem_nhds (by norm_num [hq0]))
  apply (hs.add hlarge).congr' ?_ EventuallyEq.rfl
  filter_upwards [hpos] with t ht
  dsimp only [reflectingPhasePower]
  rw [abs_of_pos ht]
  ring

/-- A non-right reflecting phase pair has strictly smaller cost at every
sufficiently small nonzero variation. The identity endpoint of its
displacement spectrum is included in the cost expansion. -/
theorem reflectingPhasePower_strict_descent
    (p d : ℝ) (hp : 1 < p) (hd0 : d ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 < |t| → |t| < r →
      reflectingPhasePower p d t < (2 : ℝ) ^ p := by
  let a := p * (2 : ℝ) ^ p * d ^ 2 / 8
  have ha : 0 < a := by
    dsimp only [a]
    exact div_pos (mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _))
      (sq_pos_of_ne_zero hd0)) (by norm_num)
  have hbound := (reflectingPhasePower_second_order p d hp).bound (half_pos ha)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨r, hr, ?_⟩
  intro t ht0 htr
  have h := hball (by simpa only [Real.dist_eq, sub_zero] using htr)
  have hsq : 0 < t ^ 2 := sq_pos_of_ne_zero (abs_pos.mp ht0)
  have he : reflectingPhasePower p d t - (2 : ℝ) ^ p + a * t ^ 2 ≤ a / 2 * t ^ 2 := by
    have habs := (le_abs_self (reflectingPhasePower p d t - (2 : ℝ) ^ p + a * t ^ 2))
    exact habs.trans (by simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using h)
  nlinarith

end TauCeti
