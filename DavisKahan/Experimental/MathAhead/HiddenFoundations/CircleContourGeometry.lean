/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.MathAhead.HiddenFoundations.ContourReuseBridge
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Explicit circle geometry for spectral continuation

The production continuation layer already handles operator-valued contour
integration.  This file supplies the remaining geometric specialization: a
positively oriented circle, its normalized winding law, and conversion from a
uniform real-spectrum separation hypothesis to the proof-carrying contour
record.
-/

open scoped InnerProductSpace Interval unitInterval Topology
open Set

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open DavisKahanExt
open Frontier
open Frontier.Section8

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Standard positive circle parameterized on the unit interval. -/
noncomputable def positiveCircleParam (center : ℂ) (radius : ℝ) (t : ℝ) : ℂ :=
  center + radius * Complex.exp ((2 * Real.pi * t) * Complex.I)

@[simp] theorem positiveCircleParam_zero (center : ℂ) (radius : ℝ) :
    positiveCircleParam center radius 0 = center + radius := by
  simp [positiveCircleParam]

@[simp] theorem positiveCircleParam_one (center : ℂ) (radius : ℝ) :
    positiveCircleParam center radius 1 = center + radius := by
  rw [positiveCircleParam]
  have hexp : Complex.exp (((2 : ℝ) * Real.pi : ℂ) * Complex.I) = 1 := by
    simpa [mul_assoc] using Complex.exp_two_pi_mul_I
  rw [show ((2 * Real.pi * (1 : ℝ) : ℝ) : ℂ) * Complex.I =
      (((2 : ℝ) * Real.pi : ℂ) * Complex.I) by norm_num]
  simp [hexp]

/-- Derivative of the standard positive circle parameterization. -/
theorem hasDerivAt_positiveCircleParam
    (center : ℂ) (radius t : ℝ) :
    HasDerivAt (positiveCircleParam center radius)
      ((radius : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)) t := by
  have hlin : HasDerivAt (fun s : ℝ => ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) t := by
    convert (((hasDerivAt_id t).const_mul (2 * Real.pi)).ofReal.comp t
      (hasDerivAt_id t)).mul_const Complex.I using 1 <;> ring
  have hexp := Complex.hasDerivAt_exp.comp t hlin
  simpa [positiveCircleParam, mul_assoc] using
    (hexp.const_mul (radius : ℂ)).const_add center

/-- The standard circle as a closed Mathlib path. -/
noncomputable def positiveCirclePath (center : ℂ) (radius : ℝ) :
    Path (center + radius) (center + radius) where
  toContinuousMap :=
    { toFun := fun t : unitInterval => positiveCircleParam center radius t
      continuous_toFun :=
        (continuous_const.add
          (continuous_const.mul
            (Complex.continuous_exp.comp
              (((continuous_const.mul continuous_subtype_val).ofReal).mul
                continuous_const)))) }
  source' := positiveCircleParam_zero center radius
  target' := positiveCircleParam_one center radius

/-- A one-piece `C1` circle contour. -/
noncomputable def positiveCircleContour (center : ℂ) (radius : ℝ) :
    PiecewiseC1ClosedContour where
  basePoint := center + radius
  path := positiveCirclePath center radius
  pieceCount := 1
  pieceCount_pos := by norm_num
  breakPoint := fun i => if i = 0 then 0 else 1
  breakPoint_zero := by simp
  breakPoint_last := by simp
  breakPoint_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  contDiffOn_piece := by
    intro i
    fin_cases i
    apply ContDiff.contDiffOn
    fun_prop

/-- The normalized winding used by the production contour layer is the usual
circle integral divided by `2*pi*i`. -/
theorem normalizedWinding_positiveCircle_eq_circleIntegral
    (center z : ℂ) (radius : ℝ) :
    (positiveCircleContour center radius).normalizedWinding z =
      (((2 : ℂ) * Real.pi * Complex.I)⁻¹) *
        circleIntegral (fun w : ℂ => (w - z)⁻¹) center radius := by
  unfold PiecewiseC1ClosedContour.normalizedWinding
  unfold positiveCircleContour PiecewiseC1ClosedContour.param
  rw [circleIntegral_def]
  have hchange := intervalIntegral.integral_comp_mul_deriv_Icc
    (f := fun theta : ℝ =>
      (circleMap center radius theta - z)⁻¹ *
        deriv (circleMap center radius) theta)
    (g := fun t : ℝ => 2 * Real.pi * t)
    (a := 0) (b := 1)
  simpa [positiveCirclePath, positiveCircleParam, circleMap,
    derivWithin_of_isOpen, mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun q : ℂ => (((2 : ℂ) * Real.pi * Complex.I)⁻¹) * q) hchange

/-- Winding law for a point strictly inside a positively oriented circle. -/
theorem normalizedWinding_positiveCircle_eq_one
    (center z : ℂ) {radius : ℝ} (hr : 0 < radius)
    (hz : ‖z - center‖ < radius) :
    (positiveCircleContour center radius).normalizedWinding z = 1 := by
  rw [normalizedWinding_positiveCircle_eq_circleIntegral]
  have hcauchy :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
      (f := fun _ : ℂ => (1 : ℂ)) (c := center) (R := radius) (z := z)
      hr hz
      (by fun_prop)
      Set.countable_empty
  have hcircle : circleIntegral (fun w : ℂ => (w - z)⁻¹) center radius =
      (2 : ℂ) * Real.pi * Complex.I := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcauchy
  rw [hcircle]
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- Winding law for a point strictly outside a positively oriented circle. -/
theorem normalizedWinding_positiveCircle_eq_zero
    (center z : ℂ) {radius : ℝ} (hr : 0 < radius)
    (hz : radius < ‖z - center‖) :
    (positiveCircleContour center radius).normalizedWinding z = 0 := by
  rw [normalizedWinding_positiveCircle_eq_circleIntegral]
  have hhol : DifferentiableOn ℂ (fun w : ℂ => (w - z)⁻¹)
      (Metric.closedBall center radius) := by
    intro w hw
    have hwz : w ≠ z := by
      intro h
      subst w
      have := Metric.mem_closedBall.mp hw
      rw [dist_eq_norm] at this
      linarith
    fun_prop
  have hzero := Complex.circleIntegral_eq_zero_of_differentiable_on_ball
    hr.le hhol
  rw [hzero, mul_zero]

/-- Uniform circle data stated directly as a distance condition. -/
structure UniformCircleSeparation
    (A E : H →L[ℂ] H) (s : Set ℝ)
    (center radius margin : ℝ) where
  hA : IsSelfAdjointOperator A
  hE : IsSelfAdjointOperator E
  hs : MeasurableSet s
  radius_pos : 0 < radius
  margin_pos : 0 < margin
  distance : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ x : unitInterval, ∀ lam ∈ realSpectrum (operatorPath A E t),
      margin ≤ ‖positiveCircleParam center radius x - (lam : ℂ)‖
  inside_iff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ lam ∈ realSpectrum (operatorPath A E t),
      (|lam - center| < radius ↔ lam ∈ s)

/-- Uniform distance data produce the existing proof-carrying contour at each
point of the affine path. -/
noncomputable def UniformCircleSeparation.separatingContour
    {A E : H →L[ℂ] H} {s : Set ℝ}
    {center radius margin : ℝ}
    (D : UniformCircleSeparation A E s center radius margin)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    SpectralSeparatingContour (operatorPath A E t) s where
  geometric := positiveCircleContour center radius
  selfAdjoint := D.hA.add (D.hE.smul t)
  measurable_selected := D.hs
  spectralMargin := margin
  spectralMargin_pos := D.margin_pos
  spectrum_separated := by
    intro x lam hlam
    simpa [positiveCircleContour, positiveCirclePath,
      PiecewiseC1ClosedContour.path, positiveCircleParam] using
      D.distance t ht x lam hlam
  winding_selected := by
    intro lam hlam hmem
    apply normalizedWinding_positiveCircle_eq_one
    · exact D.radius_pos
    · simpa [Complex.norm_real, abs_sub_comm] using
        (D.inside_iff t ht lam hlam).2 hmem
  winding_complement := by
    intro lam hlam hnot
    apply normalizedWinding_positiveCircle_eq_zero
    · exact D.radius_pos
    · have hnotInside : ¬ |lam - center| < radius := by
        intro h
        exact hnot ((D.inside_iff t ht lam hlam).1 h)
      have hne : |lam - center| ≠ radius := by
        intro heq
        have hdist := D.distance t ht
          ⟨0, by simp⟩ lam hlam
        have hcircle : positiveCircleParam center radius 0 = center + radius :=
          positiveCircleParam_zero _ _
        rw [hcircle] at hdist
        have : ‖(center + radius : ℂ) - lam‖ = |lam - center| := by
          rw [← Complex.abs.map_sub]
          norm_num
        rw [this, heq] at hdist
        linarith
      exact lt_of_le_of_ne (le_of_not_gt hnotInside) hne.symm

/-- Uniform circle data realize the bridge consumed by all Section 8
continuation theorems. -/
noncomputable def UniformCircleSeparation.toRealizedCircleContinuationData
    {A E : H →L[ℂ] H} {s : Set ℝ}
    {center radius margin : ℝ}
    (D : UniformCircleSeparation A E s center radius margin)
    (C : CircleContinuationData A E s)
    (hcenter : C.center = center) (hradius : C.radius = radius)
    (hmargin : C.margin = margin) :
    RealizedCircleContinuationData C where
  contour := positiveCircleContour center radius
  separating := fun t ht => by
    simpa [hcenter, hradius, hmargin] using D.separatingContour t ht
  geometric_eq := by intro t ht; rfl
  margin_eq := by intro t ht; simpa [hmargin]

end

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti