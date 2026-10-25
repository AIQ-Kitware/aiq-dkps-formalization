/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.Sources.DavisKahan1970.Section4Examples
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Topology.Order.Compact

/-!
# The Schatten-p phase bifurcation on a complex principal plane

For a complex planar direct rotation with principal angle `theta`, changing its
scalar phase by `delta` gives displacement singular values
`2 sin ((theta + delta) / 2)` and `2 sin ((theta - delta) / 2)` whenever
`0 <= delta < theta <= pi/2`.

This file defines the exact p-th power sum, calculates its first and second
derivatives, and solves the scalar-phase minimization problem on `[0, theta]`.
For positive `p`, the second derivative changes sign exactly at

    p * cos theta = 2 - p.

For `1 < p < 2`, the same threshold is necessary and sufficient for the
canonical phase to be the unique global minimizer on that interval, including
equality. Above the threshold there is a unique interior minimizer, the only
positive stationary phase. The proof uses the logarithmic amplitude ratio;
its derivative has a strictly increasing sign-controlling factor.

The conclusions concern scalar-phase competitors; this is not yet an
optimization theorem over every unitary transporter. Nonminimality of
particular p < 2 examples was already
observed by Bolotnikov--Li--Rodman (Electronic J. Linear Algebra 8 (2001),
Lemma 3.3).  The parameter-dependent threshold is the new target investigated
here, not a claim of historical priority.
-/

public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace SchattenPhaseTransition

open TauCeti.DavisKahan1970.Section4Examples

noncomputable section

/-- Nonnegative chord length on the angle ranges used below. -/
@[expose]
def phaseChord (t : Real) : Real := 2 * Real.sin (t / 2)

/-- The exact p-th power sum of the displacement singular values of a
scalar-phase-modified complex planar direct rotation. -/
@[expose]
def phasePower (p theta delta : Real) : Real :=
  (phaseChord (theta + delta)) ^ p + (phaseChord (theta - delta)) ^ p

/-- The auxiliary amplitude whose difference gives the first derivative after
multiplication by `p`. -/
@[expose]
def phaseAmplitude (p t : Real) : Real :=
  Real.cos (t / 2) * (phaseChord t) ^ (p - 1)

/-- First derivative of the phase power sum in the positive-chord region. -/
def phaseSlope (p theta delta : Real) : Real :=
  p * (phaseAmplitude p (theta + delta) - phaseAmplitude p (theta - delta))

/-- Derivative of the auxiliary phase amplitude. -/
def amplitudeDerivative (p t : Real) : Real :=
  -(Real.sin (t / 2) / 2) * (phaseChord t) ^ (p - 1) +
    Real.cos (t / 2) * (Real.cos (t / 2) * (p - 1) *
      (phaseChord t) ^ (p - 2))

/-- Curvature of the p-th power sum at the direct rotation (`delta = 0`). -/
def phaseCurvature (p theta : Real) : Real :=
  2 * p * amplitudeDerivative p theta

/-- Continuity of the phase power sum for nonnegative exponents, including
the endpoints where a displacement singular value vanishes. -/
theorem continuous_phasePower (p theta : ℝ) (hp : 0 ≤ p) :
    Continuous (phasePower p theta) := by
  have hchord : Continuous phaseChord := by unfold phaseChord; fun_prop
  exact ((Real.continuous_rpow_const hp).comp
    (hchord.comp (continuous_const.add continuous_id))).add
    ((Real.continuous_rpow_const hp).comp
      (hchord.comp (continuous_const.sub continuous_id)))

/-- The planar singular-value theorem from the source-example formalization
identifies `phasePower` with the *actual* displacement singular values. -/
theorem phasePower_eq_singularValues_rpow
    (p theta delta : Real) (hd : 0 <= delta) (hlt : delta < theta)
    (hpi : theta <= Real.pi / 2) :
    phasePower p theta delta =
      ((LinearMap.id - example42Competitor theta delta).singularValues 0) ^ p +
      ((LinearMap.id - example42Competitor theta delta).singularValues 1) ^ p := by
  rw [example4_2_competitor_singularValues hd hlt hpi]
  simp only [TauCeti.pairSingularValues_zero, TauCeti.pairSingularValues_one]
  rfl

/-- The displacement chord is positive at an interior angle. -/
theorem phaseChord_pos {t : Real} (h0 : 0 < t)
    (hpi : t < Real.pi) : 0 < phaseChord t := by
  unfold phaseChord
  apply mul_pos (by norm_num)
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

private theorem half_hasDerivAt (t : Real) :
    HasDerivAt (fun s : Real => s / 2) (1 / 2) t := by
  simpa only [id_eq] using (hasDerivAt_id t).div_const (2 : Real)

private theorem plus_hasDerivAt (theta delta : Real) :
    HasDerivAt (fun s : Real => theta + s) 1 delta := by
  convert (hasDerivAt_const delta theta).add (hasDerivAt_id delta) using 1
  · rfl
  · ring

private theorem minus_hasDerivAt (theta delta : Real) :
    HasDerivAt (fun s : Real => theta - s) (-1) delta := by
  convert (hasDerivAt_const delta theta).sub (hasDerivAt_id delta) using 1
  · rfl
  · ring

/-- The chord parametrization has the half-angle cosine as its derivative. -/
theorem phaseChord_hasDerivAt (t : Real) :
    HasDerivAt phaseChord (Real.cos (t / 2)) t := by
  have h := (half_hasDerivAt t).sin.const_mul (2 : Real)
  change HasDerivAt phaseChord (2 * (Real.cos (t / 2) * (1 / 2))) t at h
  convert h using 1
  ring

/-- Derivative of the chord power away from its zero endpoints. -/
theorem chord_rpow_hasDerivAt (p t : Real)
    (ht : 0 < phaseChord t) :
    HasDerivAt (fun s => (phaseChord s) ^ p)
      (Real.cos (t / 2) * p * (phaseChord t) ^ (p - 1)) t :=
  (phaseChord_hasDerivAt t).rpow_const (Or.inl ht.ne')

/-- Derivative of the amplitude at a positive chord. -/
theorem phaseAmplitude_hasDerivAt (p t : Real)
    (ht : 0 < phaseChord t) :
    HasDerivAt (phaseAmplitude p) (amplitudeDerivative p t) t := by
  have hc : HasDerivAt (fun s : Real => Real.cos (s / 2))
      (-Real.sin (t / 2) * (1 / 2)) t :=
    (half_hasDerivAt t).cos
  have hp : HasDerivAt (fun s => (phaseChord s) ^ (p - 1))
      (Real.cos (t / 2) * (p - 1) * (phaseChord t) ^ (p - 2)) t := by
    simpa only [show p - 1 - 1 = p - 2 by ring] using
      chord_rpow_hasDerivAt (p - 1) t ht
  have h := hc.mul hp
  change HasDerivAt (phaseAmplitude p) _ t at h
  convert h using 1
  dsimp only [amplitudeDerivative]
  ring

/-- Exact first derivative for an arbitrary real Schatten exponent.
The positivity assumptions are only needed for the differentiation of real powers. -/
theorem phasePower_hasDerivAt (p theta delta : Real)
    (hp : 0 < phaseChord (theta + delta))
    (hm : 0 < phaseChord (theta - delta)) :
    HasDerivAt (phasePower p theta) (phaseSlope p theta delta) delta := by
  have hplus := (chord_rpow_hasDerivAt p (theta + delta) hp).comp delta
    (plus_hasDerivAt theta delta)
  have hminus := (chord_rpow_hasDerivAt p (theta - delta) hm).comp delta
    (minus_hasDerivAt theta delta)
  have h := hplus.add hminus
  change HasDerivAt (phasePower p theta) _ delta at h
  convert h using 1
  dsimp only [phaseSlope, phaseAmplitude]
  ring

/-- For exponents at least one, differentiation is valid even at a vanishing
chord. This includes the endpoint of the optimization interval. -/
theorem phasePower_hasDerivAt_of_one_le (p theta delta : ℝ) (hp : 1 ≤ p) :
    HasDerivAt (phasePower p theta) (phaseSlope p theta delta) delta := by
  have hplus := ((phaseChord_hasDerivAt (theta + delta)).rpow_const
    (Or.inr hp)).comp delta (plus_hasDerivAt theta delta)
  have hminus := ((phaseChord_hasDerivAt (theta - delta)).rpow_const
    (Or.inr hp)).comp delta (minus_hasDerivAt theta delta)
  have h := hplus.add hminus
  change HasDerivAt (phasePower p theta) _ delta at h
  convert h using 1
  dsimp only [phaseSlope, phaseAmplitude]
  ring

/-- The canonical direct rotation is stationary under global complex phases. -/
theorem phasePower_hasDerivAt_zero (p theta : Real)
    (h0 : 0 < theta) (hpi : theta < Real.pi / 2) :
    HasDerivAt (phasePower p theta) 0 0 := by
  have hs : 0 < phaseChord theta :=
    phaseChord_pos h0 (lt_trans hpi (by linarith [Real.pi_pos]))
  have h := phasePower_hasDerivAt p theta 0 (by simpa using hs)
    (by simpa using hs)
  simpa [phaseSlope] using h

/-- Derivative of the phase slope at the canonical direct rotation. -/
theorem phaseSlope_hasDerivAt_zero (p theta : Real)
    (h0 : 0 < theta) (hpi : theta < Real.pi / 2) :
    HasDerivAt (phaseSlope p theta) (phaseCurvature p theta) 0 := by
  have hs : 0 < phaseChord theta :=
    phaseChord_pos h0 (lt_trans hpi (by linarith [Real.pi_pos]))
  have hplus := (phaseAmplitude_hasDerivAt p theta hs).comp_of_eq 0
    (plus_hasDerivAt theta 0) (by simp)
  have hminus := (phaseAmplitude_hasDerivAt p theta hs).comp_of_eq 0
    (minus_hasDerivAt theta 0) (by simp)
  have h := (hplus.sub hminus).const_mul p
  change HasDerivAt (phaseSlope p theta) _ 0 at h
  convert h using 1
  dsimp only [phaseCurvature]
  ring

/-- Express the curvature as a positive scalar times a signed trigonometric bracket. -/
theorem phaseCurvature_eq_factored (p theta : Real)
    (ht : 0 < phaseChord theta) :
    phaseCurvature p theta =
      (2 * p * (phaseChord theta) ^ (p - 2)) *
        ((p - 1) * Real.cos (theta / 2) ^ 2 -
          Real.sin (theta / 2) ^ 2) := by
  have hpow : (phaseChord theta) ^ (p - 1) =
      (phaseChord theta) ^ (p - 2) * phaseChord theta := by
    calc
      (phaseChord theta) ^ (p - 1) =
          (phaseChord theta) ^ ((p - 2) + 1) := by congr 1; ring
      _ = (phaseChord theta) ^ (p - 2) * (phaseChord theta) ^ (1 : Real) :=
        Real.rpow_add ht _ _
      _ = (phaseChord theta) ^ (p - 2) * phaseChord theta := by
        rw [Real.rpow_one]
  simp only [phaseCurvature, amplitudeDerivative]
  rw [hpow]
  unfold phaseChord
  ring

/-- The bracket is *exactly* the signed critical-angle expression. -/
private theorem curvature_bracket_identity (p theta : Real) :
    (p - 1) * Real.cos (theta / 2) ^ 2 - Real.sin (theta / 2) ^ 2 =
      (p * Real.cos theta - (2 - p)) / 2 := by
  have hcos : Real.cos theta =
      Real.cos (theta / 2) ^ 2 - Real.sin (theta / 2) ^ 2 := by
    calc
      Real.cos theta = Real.cos (theta / 2 + theta / 2) := by
        congr 1
        ring
      _ = Real.cos (theta / 2) * Real.cos (theta / 2) -
          Real.sin (theta / 2) * Real.sin (theta / 2) := by
        rw [Real.cos_add]
      _ = Real.cos (theta / 2) ^ 2 - Real.sin (theta / 2) ^ 2 := by
        ring
  rw [hcos]
  linear_combination ((p - 2) / 2) * (Real.sin_sq_add_cos_sq (theta / 2))

/-- The amplitude derivative has a single sign-controlling cosine factor. -/
theorem amplitudeDerivative_eq_critical (p t : ℝ) (hp : p ≠ 0)
    (ht : 0 < phaseChord t) :
    amplitudeDerivative p t =
      (phaseChord t) ^ (p - 2) * (p * Real.cos t - (2 - p)) / 2 := by
  have h := phaseCurvature_eq_factored p t ht
  rw [curvature_bracket_identity] at h
  dsimp only [phaseCurvature] at h
  apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hp))
  calc
    2 * p * amplitudeDerivative p t = _ := h
    _ = 2 * p * ((phaseChord t) ^ (p - 2) *
        (p * Real.cos t - (2 - p)) / 2) := by ring

/-- The exact bifurcation criterion.  For `1 < p < 2`, the direct rotation
changes from positive to negative curvature at `cos theta = (2-p)/p`.
This is a sharp local statement about the scalar-phase family, not yet a
classification of global Schatten-p minimizers. -/
theorem phaseCurvature_neg_iff (p theta : Real) (hp : 0 < p)
    (h0 : 0 < theta) (hpi : theta < Real.pi / 2) :
    phaseCurvature p theta < 0 <-> p * Real.cos theta < 2 - p := by
  have ht : 0 < phaseChord theta :=
    phaseChord_pos h0 (lt_trans hpi (by linarith [Real.pi_pos]))
  have hcoeff : 0 < 2 * p * (phaseChord theta) ^ (p - 2) := by
    exact mul_pos (mul_pos (by norm_num) hp) (Real.rpow_pos_of_pos ht _)
  rw [phaseCurvature_eq_factored p theta ht, curvature_bracket_identity]
  constructor
  · intro h
    have hb : (p * Real.cos theta - (2 - p)) / 2 < 0 := by
      by_contra hn
      have hnon : 0 <= (p * Real.cos theta - (2 - p)) / 2 := le_of_not_gt hn
      exact (not_lt_of_ge (mul_nonneg hcoeff.le hnon)) h
    linarith
  · intro h
    apply mul_neg_of_pos_of_neg hcoeff
    linarith

/-- In the complementary regime the curvature of the canonical phase is
nonnegative.  This includes the whole acute range for `p >= 2`. -/
theorem phaseCurvature_nonneg_iff (p theta : Real) (hp : 0 < p)
    (h0 : 0 < theta) (hpi : theta < Real.pi / 2) :
    0 <= phaseCurvature p theta <-> 2 - p <= p * Real.cos theta := by
  constructor
  · intro h
    by_contra hn
    have hneg : p * Real.cos theta < 2 - p := lt_of_not_ge hn
    exact (not_lt_of_ge h) ((phaseCurvature_neg_iff p theta hp h0 hpi).mpr hneg)
  · intro h
    by_contra hn
    have hneg : phaseCurvature p theta < 0 := lt_of_not_ge hn
    exact (not_lt_of_ge h) ((phaseCurvature_neg_iff p theta hp h0 hpi).mp hneg)


/-- The exact first derivative vanishes at the canonical rotation. -/
theorem phasePower_deriv_zero (p theta : Real)
    (h0 : 0 < theta) (hpi : theta < Real.pi / 2) :
    deriv (phasePower p theta) 0 = 0 :=
  (phasePower_hasDerivAt_zero p theta h0 hpi).deriv

/-- Every interior stationary phase satisfies a concrete balance equation.
This is an implicit equation for the nonzero minimizing phase. -/
theorem phasePower_stationary_iff (p theta delta : Real) (hp : p ≠ 0)
    (hplus : 0 < phaseChord (theta + delta))
    (hminus : 0 < phaseChord (theta - delta)) :
    deriv (phasePower p theta) delta = 0 <->
      phaseAmplitude p (theta + delta) = phaseAmplitude p (theta - delta) := by
  rw [(phasePower_hasDerivAt p theta delta hplus hminus).deriv]
  simp only [phaseSlope, mul_eq_zero, sub_eq_zero, hp, false_or]

/-- The ordinary second derivative at phase zero agrees with the curvature
calculated by differentiating the explicit first derivative. -/
theorem phasePower_secondDeriv_zero (p theta : Real)
    (h0 : 0 < theta) (hpi : theta < Real.pi / 2) :
    deriv (deriv (phasePower p theta)) 0 = phaseCurvature p theta := by
  have hnear : (0 : Real) ∈ Set.Ioo (-(theta / 2)) (theta / 2) := by
    constructor <;> linarith
  have hevent : (deriv (phasePower p theta)) =ᶠ[nhds (0 : Real)]
      phaseSlope p theta := by
    filter_upwards [isOpen_Ioo.mem_nhds hnear] with delta hd
    have hp0 : 0 < theta + delta := by linarith [hd.1]
    have hm0 : 0 < theta - delta := by linarith [hd.2]
    have hpluspi : theta + delta < Real.pi := by
      linarith [Real.pi_pos, hd.2]
    have hminuspi : theta - delta < Real.pi := by
      linarith [Real.pi_pos, hd.1]
    exact (phasePower_hasDerivAt p theta delta
      (phaseChord_pos hp0 hpluspi)
      (phaseChord_pos hm0 hminuspi)).deriv
  exact ((phaseSlope_hasDerivAt_zero p theta h0 hpi).congr_of_eventuallyEq
    hevent).deriv

/-- Above the sharp critical angle, the canonical phase is a local maximum
of the Schatten-p power sum.  A full exact optimizer classification still
requires the global analysis of the phase parameter and the general 2x2
unitary completion space. -/
theorem canonical_phase_localMax_of_supercritical (p theta : Real)
    (hp : 0 < p) (h0 : 0 < theta) (hpi : theta < Real.pi / 2)
    (hcrit : p * Real.cos theta < 2 - p) :
    IsLocalMax (phasePower p theta) 0 := by
  have hsecond : deriv (deriv (phasePower p theta)) 0 < 0 := by
    rw [phasePower_secondDeriv_zero p theta h0 hpi]
    exact (phaseCurvature_neg_iff p theta hp h0 hpi).mpr hcrit
  exact isLocalMax_of_deriv_deriv_neg hsecond
    (phasePower_deriv_zero p theta h0 hpi)
    (phasePower_hasDerivAt_zero p theta h0 hpi).continuousAt

/-- Below the sharp critical angle, the canonical phase is a local minimum
of the Schatten-p power sum.  Equality is the transition point. -/
theorem canonical_phase_localMin_of_subcritical (p theta : Real)
    (hp : 0 < p) (h0 : 0 < theta) (hpi : theta < Real.pi / 2)
    (hcrit : 2 - p < p * Real.cos theta) :
    IsLocalMin (phasePower p theta) 0 := by
  have hsecond : 0 < deriv (deriv (phasePower p theta)) 0 := by
    rw [phasePower_secondDeriv_zero p theta h0 hpi]
    have ht : 0 < phaseChord theta :=
      phaseChord_pos h0 (lt_trans hpi (by linarith [Real.pi_pos]))
    rw [phaseCurvature_eq_factored p theta ht, curvature_bracket_identity]
    apply mul_pos
    · exact mul_pos (mul_pos (by norm_num) hp)
        (Real.rpow_pos_of_pos ht _)
    · linarith
  exact isLocalMin_of_deriv_deriv_pos hsecond
    (phasePower_deriv_zero p theta h0 hpi)
    (phasePower_hasDerivAt_zero p theta h0 hpi).continuousAt


/-- The scalar-phase Schatten-p problem has a minimizing phase on the closed
interval from the direct rotation to the trace-optimal phase.  Unlike a mere
infimum, this theorem supplies an attaining witness. -/
theorem exists_phase_minimizer (p theta : Real) (hp : 1 <= p)
    (htheta : 0 <= theta) :
    Exists (fun delta : Real => 0 <= delta ∧ delta <= theta ∧
      (forall eta : Real, 0 <= eta -> eta <= theta ->
        phasePower p theta delta <= phasePower p theta eta)) := by
  obtain ⟨delta, hdelta, hmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : Real) theta)).exists_isMinOn
      ⟨0, by simp [htheta]⟩ (continuous_phasePower p theta (by linarith)).continuousOn
  exact ⟨delta, hdelta.1, hdelta.2,
    fun eta heta0 heta1 => hmin ⟨heta0, heta1⟩⟩

/-- Logarithmic amplitude imbalance. Its sign agrees with the sign of the
phase derivative when both half-angle cosines and chords are positive. -/
def phaseLogRatio (p theta delta : ℝ) : ℝ :=
  Real.log (Real.cos ((theta + delta) / 2)) -
    Real.log (Real.cos ((theta - delta) / 2)) +
    (p - 1) * (Real.log (phaseChord (theta + delta)) -
      Real.log (phaseChord (theta - delta)))

private theorem half_cos_pos {t : ℝ} (h0 : 0 < t) (hpi : t < Real.pi) :
    0 < Real.cos (t / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

private theorem phaseLogRatio_eq_log_amplitude (p theta delta : ℝ)
    (hp0 : 0 < theta + delta) (hpπ : theta + delta < Real.pi)
    (hm0 : 0 < theta - delta) (hmπ : theta - delta < Real.pi) :
    phaseLogRatio p theta delta =
      Real.log (phaseAmplitude p (theta + delta)) -
        Real.log (phaseAmplitude p (theta - delta)) := by
  have hplus := phaseChord_pos hp0 hpπ
  have hminus := phaseChord_pos hm0 hmπ
  rw [phaseAmplitude, phaseAmplitude,
    Real.log_mul (half_cos_pos hp0 hpπ).ne' (Real.rpow_pos_of_pos hplus _).ne',
    Real.log_mul (half_cos_pos hm0 hmπ).ne' (Real.rpow_pos_of_pos hminus _).ne',
    Real.log_rpow hplus, Real.log_rpow hminus]
  unfold phaseLogRatio
  ring

/-- The logarithmic imbalance has a derivative with a single sign-changing
factor. This turns the local curvature threshold into a global phase test. -/
theorem phaseLogRatio_hasDerivAt (p theta delta : ℝ)
    (hp0 : 0 < theta + delta) (hpπ : theta + delta < Real.pi)
    (hm0 : 0 < theta - delta) (hmπ : theta - delta < Real.pi) :
    HasDerivAt (phaseLogRatio p theta)
      (Real.sin theta * (p * Real.cos theta - (2 - p) * Real.cos delta) /
        (Real.cos delta ^ 2 - Real.cos theta ^ 2)) delta := by
  have sp := phaseChord_pos hp0 hpπ
  have sm := phaseChord_pos hm0 hmπ
  have cp := half_cos_pos hp0 hpπ
  have cm := half_cos_pos hm0 hmπ
  have hcp := ((half_hasDerivAt (theta + delta)).cos.log cp.ne').comp delta
    (plus_hasDerivAt theta delta)
  have hcm := ((half_hasDerivAt (theta - delta)).cos.log cm.ne').comp delta
    (minus_hasDerivAt theta delta)
  have hsp := ((phaseChord_hasDerivAt (theta + delta)).log sp.ne').comp delta
    (plus_hasDerivAt theta delta)
  have hsm := ((phaseChord_hasDerivAt (theta - delta)).log sm.ne').comp delta
    (minus_hasDerivAt theta delta)
  have h := (hcp.sub hcm).add ((hsp.sub hsm).const_mul (p - 1))
  change HasDerivAt (phaseLogRatio p theta) _ delta at h
  convert h using 1
  have hθ : theta = (theta + delta) / 2 + (theta - delta) / 2 := by ring
  have hδ : delta = (theta + delta) / 2 - (theta - delta) / 2 := by ring
  have hsθ := Real.sin_add ((theta + delta) / 2) ((theta - delta) / 2)
  have hcθ := Real.cos_add ((theta + delta) / 2) ((theta - delta) / 2)
  have hcδ := Real.cos_sub ((theta + delta) / 2) ((theta - delta) / 2)
  rw [← hθ] at hsθ hcθ
  rw [← hδ] at hcδ
  have hden : Real.cos delta ^ 2 - Real.cos theta ^ 2 =
      4 * Real.sin ((theta + delta) / 2) * Real.sin ((theta - delta) / 2) *
        Real.cos ((theta + delta) / 2) * Real.cos ((theta - delta) / 2) := by
    rw [hcδ, hcθ]
    ring
  have hsp0 : Real.sin ((theta + delta) / 2) ≠ 0 := by
    unfold phaseChord at sp
    exact (show 0 < Real.sin ((theta + delta) / 2) by linarith).ne'
  have hsm0 : Real.sin ((theta - delta) / 2) ≠ 0 := by
    unfold phaseChord at sm
    exact (show 0 < Real.sin ((theta - delta) / 2) by linarith).ne'
  rw [hden, hsθ, hcθ, hcδ]
  dsimp only [phaseChord]
  field_simp [hsp0, hsm0, cp.ne', cm.ne']
  ring

private theorem phase_region {theta delta : ℝ}
    (hθ : 0 < theta) (hπ : theta ≤ Real.pi / 2)
    (hδ : 0 ≤ delta) (hδθ : delta < theta) :
    0 < theta + delta ∧ theta + delta < Real.pi ∧
      0 < theta - delta ∧ theta - delta < Real.pi := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith [Real.pi_pos]

private theorem phase_log_denom_pos {theta delta : ℝ}
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hδ : 0 ≤ delta) (hδθ : delta < theta) :
    0 < Real.cos delta ^ 2 - Real.cos theta ^ 2 := by
  have hc : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hπ⟩
  have hcos : Real.cos theta < Real.cos delta :=
    Real.strictAntiOn_cos ⟨hδ, by linarith [Real.pi_pos]⟩
      ⟨hθ.le, by linarith [Real.pi_pos]⟩ hδθ
  nlinarith

private theorem phaseLogRatio_deriv_pos_of_subcritical
    (p theta delta : ℝ) (hp : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hcrit : 2 - p ≤ p * Real.cos theta)
    (hδ : 0 < delta) (hδθ : delta < theta) :
    0 < deriv (phaseLogRatio p theta) delta := by
  obtain ⟨hp0, hpπ, hm0, hmπ⟩ := phase_region hθ hπ.le hδ.le hδθ
  rw [(phaseLogRatio_hasDerivAt p theta delta hp0 hpπ hm0 hmπ).deriv]
  have hcos1 : Real.cos delta < 1 := by
    simpa only [Real.cos_zero] using
      Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
        ⟨hδ.le, by linarith [Real.pi_pos]⟩ hδ
  have hfactor : 0 < p * Real.cos theta - (2 - p) * Real.cos delta := by
    have := mul_pos (sub_pos.mpr hp) (sub_pos.mpr hcos1)
    nlinarith
  apply div_pos
  · exact mul_pos (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos]))
      hfactor
  · exact phase_log_denom_pos hθ hπ hδ.le hδθ

private theorem phaseLogRatio_pos_of_subcritical
    (p theta delta : ℝ) (hp : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hcrit : 2 - p ≤ p * Real.cos theta)
    (hδ : 0 < delta) (hδθ : delta < theta) :
    0 < phaseLogRatio p theta delta := by
  have hmono : StrictMonoOn (phaseLogRatio p theta) (Set.Icc 0 delta) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro eta heta
      obtain ⟨hp0, hpπ, hm0, hmπ⟩ :=
        phase_region hθ hπ.le heta.1 (lt_of_le_of_lt heta.2 hδθ)
      exact (phaseLogRatio_hasDerivAt p theta eta hp0 hpπ hm0 hmπ).continuousAt
        |>.continuousWithinAt
    · intro eta heta
      rw [interior_Icc] at heta
      exact phaseLogRatio_deriv_pos_of_subcritical p theta eta hp hθ hπ hcrit
        heta.1 (lt_trans heta.2 hδθ)
  have h := hmono (by simp [hδ.le]) (by simp [hδ.le]) hδ
  simpa [phaseLogRatio] using h

/-- The phase derivative is strictly positive at every positive interior
phase below or at the canonical-optimality threshold. -/
theorem phasePower_deriv_pos_of_subcritical
    (p theta delta : ℝ) (hp0 : 0 < p) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hcrit : 2 - p ≤ p * Real.cos theta)
    (hδ : 0 < delta) (hδθ : delta < theta) :
    0 < deriv (phasePower p theta) delta := by
  obtain ⟨hp0', hpπ, hm0, hmπ⟩ := phase_region hθ hπ.le hδ.le hδθ
  have hlog := phaseLogRatio_pos_of_subcritical p theta delta hp2 hθ hπ hcrit hδ hδθ
  rw [phaseLogRatio_eq_log_amplitude p theta delta hp0' hpπ hm0 hmπ] at hlog
  have hplus : 0 < phaseAmplitude p (theta + delta) :=
    mul_pos (half_cos_pos hp0' hpπ) (Real.rpow_pos_of_pos (phaseChord_pos hp0' hpπ) _)
  have hminus : 0 < phaseAmplitude p (theta - delta) :=
    mul_pos (half_cos_pos hm0 hmπ) (Real.rpow_pos_of_pos (phaseChord_pos hm0 hmπ) _)
  have hcmp := (Real.log_lt_log_iff hminus hplus).mp (sub_pos.mp hlog)
  rw [(phasePower_hasDerivAt p theta delta
    (phaseChord_pos hp0' hpπ) (phaseChord_pos hm0 hmπ)).deriv]
  exact mul_pos hp0 (sub_pos.mpr hcmp)

/-- Below the critical angle, including the critical angle itself, the
Schatten power sum increases strictly throughout the entire phase interval.
The vanishing curvature at the critical angle therefore does not create an
additional minimizer. -/
theorem phasePower_strictMonoOn_of_subcritical
    (p theta : ℝ) (hp0 : 0 < p) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hcrit : 2 - p ≤ p * Real.cos theta) :
    StrictMonoOn (phasePower p theta) (Set.Icc 0 theta) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact (continuous_phasePower p theta hp0.le).continuousOn
  · intro delta hdelta
    rw [interior_Icc] at hdelta
    exact phasePower_deriv_pos_of_subcritical p theta delta hp0 hp2 hθ hπ hcrit
      hdelta.1 hdelta.2

/-- Exact canonical-phase optimality on the full phase interval, with a
unique minimizing phase even when the curvature is zero. -/
theorem canonical_phase_unique_min_of_subcritical
    (p theta : ℝ) (hp0 : 0 < p) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hcrit : 2 - p ≤ p * Real.cos theta)
    {delta : ℝ} (hδ : delta ∈ Set.Icc 0 theta) :
    phasePower p theta 0 ≤ phasePower p theta delta ∧
      (phasePower p theta delta = phasePower p theta 0 ↔ delta = 0) := by
  have hmono := phasePower_strictMonoOn_of_subcritical p theta hp0 hp2 hθ hπ hcrit
  have hzero : (0 : ℝ) ∈ Set.Icc 0 theta := ⟨le_rfl, hθ.le⟩
  exact ⟨hmono.monotoneOn hzero hδ hδ.1,
    ⟨fun h => hmono.injOn hδ hzero h, fun h => by rw [h]⟩⟩

private theorem phaseLogRatio_continuousOn_Icc (p theta a b : ℝ)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (ha : 0 ≤ a) (hb : b < theta) :
    ContinuousOn (phaseLogRatio p theta) (Set.Icc a b) := by
  intro delta hdelta
  obtain ⟨hp0, hpπ, hm0, hmπ⟩ :=
    phase_region hθ hπ.le (ha.trans hdelta.1) (lt_of_le_of_lt hdelta.2 hb)
  exact (phaseLogRatio_hasDerivAt p theta delta hp0 hpπ hm0 hmπ).continuousAt
    |>.continuousWithinAt

private theorem phaseLogRatio_deriv_eq_zero_iff (p theta delta : ℝ)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hδ : 0 ≤ delta) (hδθ : delta < theta) :
    deriv (phaseLogRatio p theta) delta = 0 ↔
      p * Real.cos theta = (2 - p) * Real.cos delta := by
  obtain ⟨hp0, hpπ, hm0, hmπ⟩ := phase_region hθ hπ.le hδ hδθ
  rw [(phaseLogRatio_hasDerivAt p theta delta hp0 hpπ hm0 hmπ).deriv]
  have hs : Real.sin theta ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])).ne'
  have hd := (phase_log_denom_pos hθ hπ hδ hδθ).ne'
  simp [div_eq_zero_iff, hs, hd, sub_eq_zero]

private theorem phaseLogRatio_not_two_roots (p theta a b : ℝ) (hp : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (ha : 0 < a) (hab : a < b) (hb : b < theta)
    (hfa : phaseLogRatio p theta a = 0) (hfb : phaseLogRatio p theta b = 0) :
    False := by
  have hf0 : phaseLogRatio p theta 0 = 0 := by simp [phaseLogRatio]
  obtain ⟨x, hx, hxderiv⟩ := exists_deriv_eq_zero ha
    (phaseLogRatio_continuousOn_Icc p theta 0 a hθ hπ le_rfl (lt_trans hab hb))
    (hf0.trans hfa.symm)
  obtain ⟨y, hy, hyderiv⟩ := exists_deriv_eq_zero hab
    (phaseLogRatio_continuousOn_Icc p theta a b hθ hπ ha.le hb)
    (hfa.trans hfb.symm)
  have hKx := (phaseLogRatio_deriv_eq_zero_iff p theta x hθ hπ hx.1.le
    (lt_trans hx.2 (lt_trans hab hb))).mp hxderiv
  have hKy := (phaseLogRatio_deriv_eq_zero_iff p theta y hθ hπ
    (lt_trans ha hy.1).le (lt_trans hy.2 hb)).mp hyderiv
  have hcos : Real.cos y < Real.cos x :=
    Real.strictAntiOn_cos ⟨hx.1.le, by linarith [hx.2, Real.pi_pos]⟩
      ⟨by linarith [hy.1], by linarith [hy.2, Real.pi_pos]⟩ (lt_trans hx.2 hy.1)
  nlinarith [mul_pos (sub_pos.mpr hp) (sub_pos.mpr hcos)]

/-- There is at most one positive stationary phase in the open phase
interval. The proof uses Rolle's theorem twice and the strict monotonicity
of the numerator of the logarithmic-ratio derivative. -/
theorem phasePower_stationary_unique (p theta : ℝ) (hp : p ≠ 0) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    {a b : ℝ} (ha : a ∈ Set.Ioo 0 theta) (hb : b ∈ Set.Ioo 0 theta)
    (hfa : deriv (phasePower p theta) a = 0)
    (hfb : deriv (phasePower p theta) b = 0) : a = b := by
  have hroot : ∀ delta ∈ Set.Ioo 0 theta, deriv (phasePower p theta) delta = 0 →
      phaseLogRatio p theta delta = 0 := by
    intro delta hdelta hderiv
    obtain ⟨hp0, hpπ, hm0, hmπ⟩ := phase_region hθ hπ.le hdelta.1.le hdelta.2
    have hamp := (phasePower_stationary_iff p theta delta hp
      (phaseChord_pos hp0 hpπ) (phaseChord_pos hm0 hmπ)).mp hderiv
    rw [phaseLogRatio_eq_log_amplitude p theta delta hp0 hpπ hm0 hmπ, hamp, sub_self]
  have haroot := hroot a ha hfa
  have hbroot := hroot b hb hfb
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (phaseLogRatio_not_two_roots p theta a b hp2 hθ hπ
      ha.1 hab hb.2 haroot hbroot)
  · exact hab
  · exact False.elim (phaseLogRatio_not_two_roots p theta b a hp2 hθ hπ
      hb.1 hab ha.2 hbroot haroot)

/-- In the supercritical regime an admissible positive phase strictly
improves on the canonical phase. This excludes a merely flat local maximum. -/
theorem exists_phase_strict_improvement_of_supercritical
    (p theta : ℝ) (hp : 0 < p)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hcrit : p * Real.cos theta < 2 - p) :
    ∃ delta ∈ Set.Ioo 0 theta, phasePower p theta delta < phasePower p theta 0 := by
  have hs : deriv (phaseSlope p theta) 0 < 0 := by
    rw [(phaseSlope_hasDerivAt_zero p theta hθ hπ).deriv]
    exact (phaseCurvature_neg_iff p theta hp hθ hπ).mpr hcrit
  have hz : phaseSlope p theta 0 = 0 := by simp [phaseSlope]
  obtain ⟨a, b, hab, hsign⟩ :=
    (eventually_nhdsWithin_sign_eq_of_deriv_neg hs hz).exists_Ioo_subset
  obtain ⟨delta, hdelta0, hdeltab⟩ := exists_between (lt_min hab.2 hθ)
  have hdeltatheta : delta < theta := lt_of_lt_of_le hdeltab (min_le_right _ _)
  have hanti : StrictAntiOn (phasePower p theta) (Set.Icc 0 delta) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (continuous_phasePower p theta hp.le).continuousOn
    intro eta heta
    rw [interior_Icc] at heta
    obtain ⟨hp0, hpπ, hm0, hmπ⟩ := phase_region hθ hπ.le heta.1.le
      (lt_trans heta.2 hdeltatheta)
    rw [(phasePower_hasDerivAt p theta eta
      (phaseChord_pos hp0 hpπ) (phaseChord_pos hm0 hmπ)).deriv]
    have heq : SignType.sign (phaseSlope p theta eta) = SignType.sign ((0 : ℝ) - eta) :=
      hsign ⟨by linarith [hab.1, heta.1],
        by linarith [min_le_left b theta, heta.2]⟩
    have hneg : (0 : ℝ) - eta < 0 := by linarith [heta.1]
    rw [sign_neg hneg] at heq
    exact sign_eq_neg_one_iff.mp heq
  exact ⟨delta, ⟨hdelta0, hdeltatheta⟩,
    hanti ⟨le_rfl, hdelta0.le⟩ ⟨hdelta0.le, le_rfl⟩ hdelta0⟩

/-- At a positive acute angle the endpoint phase has positive derivative;
it cannot minimize on any nontrivial interval immediately to its left. -/
theorem phasePower_deriv_endpoint_pos (p theta : ℝ) (hp : 1 < p)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2) :
    0 < deriv (phasePower p theta) theta := by
  rw [(phasePower_hasDerivAt_of_one_le p theta theta hp.le).deriv]
  have hhalf : (theta + theta) / 2 = theta := by ring
  have hz : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
  simp only [phaseSlope, phaseAmplitude, phaseChord, hhalf, sub_self, zero_div,
    Real.sin_zero, Real.cos_zero, mul_zero, hz, sub_zero]
  exact mul_pos (by linarith) (mul_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hπ⟩)
    (Real.rpow_pos_of_pos (mul_pos (by norm_num)
      (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos]))) _))

private theorem exists_phase_better_than_endpoint (p theta : ℝ) (hp : 1 < p)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2) :
    ∃ delta ∈ Set.Ioo 0 theta,
      phasePower p theta delta < phasePower p theta theta := by
  let f : ℝ → ℝ := fun delta => phasePower p theta delta - phasePower p theta theta
  have hderiv : deriv f theta > 0 := by
    rw [(phasePower_hasDerivAt_of_one_le p theta theta hp.le).sub_const
      (phasePower p theta theta) |>.deriv]
    have hpos := phasePower_deriv_endpoint_pos p theta hp hθ hπ
    rwa [(phasePower_hasDerivAt_of_one_le p theta theta hp.le).deriv] at hpos
  have hz : f theta = 0 := by simp [f]
  obtain ⟨a, b, hab, hsign⟩ :=
    (eventually_nhdsWithin_sign_eq_of_deriv_pos hderiv hz).exists_Ioo_subset
  obtain ⟨delta, hdeltaa, hdeltatheta⟩ := exists_between (max_lt hab.1 hθ)
  have hdelta0 : 0 < delta := lt_of_le_of_lt (le_max_right _ _) hdeltaa
  have heq : SignType.sign (f delta) = SignType.sign (delta - theta) :=
    hsign ⟨lt_of_le_of_lt (le_max_left _ _) hdeltaa, lt_trans hdeltatheta hab.2⟩
  rw [sign_neg (sub_neg.mpr hdeltatheta)] at heq
  have hf : f delta < 0 := sign_eq_neg_one_iff.mp heq
  exact ⟨delta, ⟨hdelta0, hdeltatheta⟩, sub_neg.mp hf⟩

private theorem phase_minimizer_mem_Ioo_of_supercritical
    (p theta : ℝ) (hp : 1 < p)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hcrit : p * Real.cos theta < 2 - p)
    {delta : ℝ} (hδ : delta ∈ Set.Icc 0 theta)
    (hmin : IsMinOn (phasePower p theta) (Set.Icc 0 theta) delta) :
    delta ∈ Set.Ioo 0 theta := by
  have hδ0 : delta ≠ 0 := by
    intro heq
    obtain ⟨eta, heta, hbetter⟩ := exists_phase_strict_improvement_of_supercritical
      p theta (by linarith) hθ hπ hcrit
    have hle := hmin (show eta ∈ Set.Icc 0 theta from ⟨heta.1.le, heta.2.le⟩)
    rw [heq] at hle
    exact (not_lt_of_ge hle) hbetter
  have hδθ : delta ≠ theta := by
    intro heq
    obtain ⟨eta, heta, hbetter⟩ := exists_phase_better_than_endpoint p theta hp hθ hπ
    have hle := hmin (show eta ∈ Set.Icc 0 theta from ⟨heta.1.le, heta.2.le⟩)
    rw [heq] at hle
    exact (not_lt_of_ge hle) hbetter
  exact ⟨lt_of_le_of_ne hδ.1 hδ0.symm, lt_of_le_of_ne hδ.2 hδθ⟩

/-- Above the transition there is a unique minimizing phase on the full
closed interval, it lies strictly inside the interval, and it is stationary.
Thus the scalar-phase minimum has an exact single-root characterization. -/
theorem exists_unique_phase_minimizer_of_supercritical
    (p theta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2)
    (hcrit : p * Real.cos theta < 2 - p) :
    ∃ delta ∈ Set.Ioo 0 theta, deriv (phasePower p theta) delta = 0 ∧
      ∀ eta ∈ Set.Icc 0 theta,
        phasePower p theta delta ≤ phasePower p theta eta ∧
          (phasePower p theta eta = phasePower p theta delta ↔ eta = delta) := by
  obtain ⟨delta, hδ0, hδθ, hmin⟩ := exists_phase_minimizer p theta hp1.le hθ.le
  have hm : IsMinOn (phasePower p theta) (Set.Icc 0 theta) delta :=
    fun eta heta => hmin eta heta.1 heta.2
  have hδ := phase_minimizer_mem_Ioo_of_supercritical p theta hp1 hθ hπ hcrit
    ⟨hδ0, hδθ⟩ hm
  have hd : deriv (phasePower p theta) delta = 0 :=
    (hm.isLocalMin (Icc_mem_nhds hδ.1 hδ.2)).deriv_eq_zero
  refine ⟨delta, hδ, hd, ?_⟩
  intro eta heta
  refine ⟨hm heta, ⟨?_, fun h => by rw [h]⟩⟩
  intro heq
  have hmη : IsMinOn (phasePower p theta) (Set.Icc 0 theta) eta := by
    intro x hx
    rw [heq]
    exact hm hx
  have hη := phase_minimizer_mem_Ioo_of_supercritical p theta hp1 hθ hπ hcrit heta hmη
  have hdη : deriv (phasePower p theta) eta = 0 :=
    (hmη.isLocalMin (Icc_mem_nhds hη.1 hη.2)).deriv_eq_zero
  exact phasePower_stationary_unique p theta (by linarith) hp2 hθ hπ hη hδ hdη hd

/-- The critical-angle inequality is necessary and sufficient for the
canonical phase to minimize the scalar-phase objective globally on `[0, θ]`. -/
theorem canonical_phase_isMinOn_iff (p theta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hθ : 0 < theta) (hπ : theta < Real.pi / 2) :
    IsMinOn (phasePower p theta) (Set.Icc 0 theta) 0 ↔
      2 - p ≤ p * Real.cos theta := by
  constructor
  · intro hmin
    by_contra hcrit
    obtain ⟨delta, hδ, hbetter⟩ := exists_phase_strict_improvement_of_supercritical
      p theta (by linarith) hθ hπ (lt_of_not_ge hcrit)
    exact (not_lt_of_ge (hmin ⟨hδ.1.le, hδ.2.le⟩)) hbetter
  · intro hcrit delta hδ
    exact (canonical_phase_unique_min_of_subcritical p theta (by linarith)
      hp2 hθ hπ hcrit hδ).1

end
end SchattenPhaseTransition
end DavisKahan.FiniteDimensional
end TauCeti
