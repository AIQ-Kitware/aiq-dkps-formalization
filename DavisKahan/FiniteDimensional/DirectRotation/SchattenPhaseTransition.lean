/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.Sources.DavisKahan1970.Section4Examples
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.Order.Compact

/-!
# The Schatten-p phase bifurcation on a complex principal plane

For a complex planar direct rotation with principal angle `theta`, changing its
scalar phase by `delta` gives displacement singular values
`2 sin ((theta + delta) / 2)` and `2 sin ((theta - delta) / 2)` whenever
`0 <= delta < theta <= pi/2`.

This file defines the exact p-th power sum and calculates its first and
second derivatives at the direct rotation.  For positive `p`, the second
derivative changes sign exactly at

    p * cos theta = 2 - p.

For `1 < p < 2` this defines the critical angle.  The conclusion concerns
scalar-phase competitors; it is not yet an optimization theorem over every
unitary transporter.  Nonminimality of particular p < 2 examples was already
observed by Bolotnikov--Li--Rodman (Electronic J. Linear Algebra 8 (2001),
Lemma 3.3).  The parameter-dependent threshold is the new target investigated
here, not a claim of historical priority.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace SchattenPhaseTransition

open TauCeti.DavisKahan1970.Section4Examples

noncomputable section

/-- Nonnegative chord length on the angle ranges used below. -/
def phaseChord (t : Real) : Real := 2 * Real.sin (t / 2)

/-- The exact p-th power sum of the displacement singular values of a
scalar-phase-modified complex planar direct rotation. -/
def phasePower (p theta delta : Real) : Real :=
  (phaseChord (theta + delta)) ^ p + (phaseChord (theta - delta)) ^ p

/-- The auxiliary amplitude whose difference gives the first derivative after
multiplication by `p`. -/
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

private theorem phaseChord_pos {t : Real} (h0 : 0 < t)
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

private theorem phaseChord_hasDerivAt (t : Real) :
    HasDerivAt phaseChord (Real.cos (t / 2)) t := by
  have h := (half_hasDerivAt t).sin.const_mul (2 : Real)
  change HasDerivAt phaseChord (2 * (Real.cos (t / 2) * (1 / 2))) t at h
  convert h using 1
  ring

private theorem chord_rpow_hasDerivAt (p t : Real)
    (ht : 0 < phaseChord t) :
    HasDerivAt (fun s => (phaseChord s) ^ p)
      (Real.cos (t / 2) * p * (phaseChord t) ^ (p - 1)) t :=
  (phaseChord_hasDerivAt t).rpow_const (Or.inl ht.ne')

private theorem phaseAmplitude_hasDerivAt (p t : Real)
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
  have hpcont : Continuous (fun x : Real => x ^ p) :=
    Real.continuous_rpow_const (by linarith)
  have hchord : Continuous phaseChord := by
    unfold phaseChord
    fun_prop
  have hplus : Continuous (fun delta : Real => theta + delta) :=
    continuous_const.add continuous_id
  have hminus : Continuous (fun delta : Real => theta - delta) :=
    continuous_const.sub continuous_id
  have hcont : Continuous (phasePower p theta) := by
    unfold phasePower
    exact (hpcont.comp (hchord.comp hplus)).add
      (hpcont.comp (hchord.comp hminus))
  obtain ⟨delta, hdelta, hmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : Real) theta)).exists_isMinOn
      ⟨0, by simp [htheta]⟩ hcont.continuousOn
  exact ⟨delta, hdelta.1, hdelta.2,
    fun eta heta0 heta1 => hmin ⟨heta0, heta1⟩⟩

end
end SchattenPhaseTransition
end DavisKahan.FiniteDimensional
end TauCeti
