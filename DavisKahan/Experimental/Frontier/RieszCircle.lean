/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Core
import DavisKahan.Experimental.InfiniteDimensional.Core.SpectralProjection
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Circle Riesz projections for the Section 8 continuation argument

Only circles separating subsets of the real spectrum are exposed here.  This
is the minimum analytic surface required by the Davis--Kahan continuation
stack and intentionally avoids an abstract contour, rectifiability, or winding
number framework.
-/

open scoped InnerProductSpace Topology
open Set Filter

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace RieszCircle

open DavisKahanExt

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The circle resolvent integrand: the resolvent at the parametrized circle
point, weighted by the derivative of the parametrization, exactly as in
Mathlib's `circleIntegral`. -/
noncomputable def circleResolventIntegrand
    (A : H →L[ℂ] H) (center radius θ : ℝ) : H →L[ℂ] H :=
  deriv (circleMap (center : ℂ) radius) θ •
    Ring.inverse (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A)

/-- The operator-valued circle integral defining the Riesz projection. -/
noncomputable def circleRieszProjectionIntegral
    (A : H →L[ℂ] H) (center radius : ℝ) : H →L[ℂ] H :=
  (2 * Real.pi * Complex.I)⁻¹ •
    ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, circleResolventIntegrand A center radius θ

/-- The core definition in `Core` agrees with the explicit operator-valued
circle integral. -/
theorem circleRieszProjection_eq_integral
    (A : H →L[ℂ] H) (center radius : ℝ) :
    Frontier.circleRieszProjection A center radius =
      circleRieszProjectionIntegral A center radius :=
  rfl

/-- The resolvent integrand is continuous around a separating circle. -/
theorem continuous_circleResolventIntegrand
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : Set ℝ) (center radius : ℝ)
    (hsep : CircleSeparatesRealSpectrum A hA B center radius) :
    Continuous (circleResolventIntegrand A center radius) := by
  have hr : (0 : ℝ) ≤ radius := hsep.radius_pos.le
  have hderiv : Continuous fun θ : ℝ => deriv (circleMap (center : ℂ) radius) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 radius).mul continuous_const
  have haff : Continuous fun θ : ℝ =>
      circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A :=
    ((continuous_circleMap _ _).smul continuous_const).sub continuous_const
  have hinv : Continuous fun θ : ℝ =>
      Ring.inverse (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hz : circleMap (center : ℂ) radius θ ∉ spectrum ℂ A :=
      hsep.contour_resolvent _ (by
        simpa [mem_sphere_iff_norm] using circleMap_mem_sphere (center : ℂ) hr θ)
    have hu : IsUnit (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A) := by
      have h := spectrum.notMem_iff.mp hz
      rwa [Algebra.algebraMap_eq_smul_one] at h
    have hcont : ContinuousAt Ring.inverse
        (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A) := by
      have h := NormedRing.inverse_continuousAt hu.unit
      rwa [IsUnit.unit_spec] at h
    exact hcont.comp (f := fun θ' : ℝ =>
      circleMap (center : ℂ) radius θ' • (1 : H →L[ℂ] H) - A) haff.continuousAt
  exact hderiv.smul hinv

/-- Cauchy's formula identifies the scalar circle integral with the indicator
of being inside the circle on the real spectrum. -/
theorem scalar_circleIntegral_resolvent_indicator
    (x center radius : ℝ) (hr : 0 < radius)
    (hboundary : |x - center| ≠ radius) :
    (circleIntegral (fun z : ℂ => (z - x)⁻¹) center radius) /
        (2 * Real.pi * Complex.I) =
      if |x - center| < radius then 1 else 0 := by
  split_ifs with hin
  · have hmem : (x : ℂ) ∈ Metric.ball (center : ℂ) radius := by
      rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      exact hin
    rw [circleIntegral.integral_sub_inv_of_mem_ball hmem]
    exact div_self Complex.two_pi_I_ne_zero
  · have hout : (x : ℂ) ∉ Metric.closedBall (center : ℂ) radius := by
      rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      exact not_le.mpr (lt_of_le_of_ne (not_lt.mp hin) (Ne.symm hboundary))
    have hdiff : DiffContOnCl ℂ (fun z : ℂ => (z - (x : ℂ))⁻¹)
        (Metric.ball (center : ℂ) radius) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hr.ne']
      intro z hz
      have hzx : z - (x : ℂ) ≠ 0 := by
        intro h0
        exact hout (sub_eq_zero.mp h0 ▸ hz)
      have hd : DifferentiableAt ℂ (fun w : ℂ => w - (x : ℂ)) z :=
        differentiableAt_id.sub_const _
      exact (hd.inv hzx).differentiableWithinAt
    rw [DiffContOnCl.circleIntegral_eq_zero hr.le hdiff, zero_div]

/-- The circle Riesz projection equals the genuine measurable spectral
projection selected by the inside of the circle. -/
theorem circleRieszProjection_eq_boundedSelfAdjointSpectralProjection
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : Set ℝ) (hB : MeasurableSet B) (center radius : ℝ)
    (hsep : CircleSeparatesRealSpectrum A hA B center radius) :
    Frontier.circleRieszProjection A center radius =
      boundedSelfAdjointSpectralProjection A hA B hB := by
  sorry

/-- The second resolvent identity for the total `Ring.inverse` at two units. -/
private theorem ringInverse_sub_ringInverse (T T' : H →L[ℂ] H)
    (hT : IsUnit T) (hT' : IsUnit T') :
    Ring.inverse T' - Ring.inverse T =
      Ring.inverse T' * (T - T') * Ring.inverse T := by
  have h1 : T * Ring.inverse T = 1 := Ring.mul_inverse_cancel T hT
  have h2 : Ring.inverse T' * T' = 1 := Ring.inverse_mul_cancel T' hT'
  calc Ring.inverse T' - Ring.inverse T
      = Ring.inverse T' * (T * Ring.inverse T) -
          Ring.inverse T' * T' * Ring.inverse T := by rw [h1, h2, mul_one, one_mul]
    _ = Ring.inverse T' * (T - T') * Ring.inverse T := by noncomm_ring

/-- If a unit with inverse norm at most `margin⁻¹` becomes singular after adding
a perturbation, the perturbation has norm at least `margin` (geometric series). -/
private theorem margin_le_norm_perturbation
    (T Epert : H →L[ℂ] H) {margin : ℝ} (hmargin : 0 < margin)
    (hT : IsUnit T) (hTnorm : ‖Ring.inverse T‖ ≤ margin⁻¹)
    (hTE : ¬IsUnit (T + Epert)) : margin ≤ ‖Epert‖ := by
  by_contra hlt
  rw [not_le] at hlt
  have : Nontrivial (H →L[ℂ] H) := by
    rcases subsingleton_or_nontrivial (H →L[ℂ] H) with hsub | hn
    · exact absurd (by
        rw [Subsingleton.elim (T + Epert) (1 : H →L[ℂ] H)]
        exact isUnit_one) hTE
    · exact hn
  have hval : ((hT.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = Ring.inverse T :=
    (Ring.inverse_unit hT.unit).symm.trans (congrArg Ring.inverse hT.unit_spec)
  have hpos : (0 : ℝ) < ‖((hT.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖ :=
    Units.norm_pos _
  have hinvnorm : ‖((hT.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖ ≤ margin⁻¹ := by
    rw [hval]; exact hTnorm
  have hmarg : margin ≤ ‖((hT.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖⁻¹ := by
    rw [← inv_inv margin]
    gcongr
  have hu := (hT.unit.add Epert (lt_of_lt_of_le hlt hmarg)).isUnit
  rw [Units.val_add, hT.unit_spec] at hu
  exact hTE hu

/-- A resolvent-type pencil with a uniform norm bound on the circle is circle
integrable: it is continuous on the open set where the pencil is a unit and
identically zero elsewhere, hence a.e. strongly measurable, and it is bounded. -/
private theorem circleIntegrable_ringInverse_pencil
    (A : H →L[ℂ] H) (center radius M : ℝ) (hr : 0 ≤ radius)
    (hbound : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ ≤ M) :
    CircleIntegrable (fun z : ℂ => Ring.inverse (z • (1 : H →L[ℂ] H) - A))
      center radius := by
  rw [circleIntegrable_def]
  set g : ℝ → H →L[ℂ] H := fun θ =>
    circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A with hg
  have hgcont : Continuous g :=
    ((continuous_circleMap _ _).smul continuous_const).sub continuous_const
  have hVopen : IsOpen {θ : ℝ | IsUnit (g θ)} := Units.isOpen.preimage hgcont
  have hcontOn : ContinuousOn (fun θ => Ring.inverse (g θ))
      {θ : ℝ | IsUnit (g θ)} := by
    intro θ hθ
    have hcθ : ContinuousAt Ring.inverse (g θ) := by
      have h := NormedRing.inverse_continuousAt (hθ : IsUnit (g θ)).unit
      rwa [IsUnit.unit_spec] at h
    exact (hcθ.comp (f := g) hgcont.continuousAt).continuousWithinAt
  have heq : (fun θ => Ring.inverse (g θ)) =
      Set.indicator {θ : ℝ | IsUnit (g θ)} (fun θ => Ring.inverse (g θ)) := by
    funext θ
    by_cases hθ : IsUnit (g θ)
    · rw [Set.indicator_of_mem (show θ ∈ {θ : ℝ | IsUnit (g θ)} from hθ)]
    · rw [Set.indicator_of_notMem (show θ ∉ {θ : ℝ | IsUnit (g θ)} from hθ),
        Ring.inverse_non_unit _ hθ]
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => Ring.inverse (g θ))
      MeasureTheory.volume := by
    rw [heq]
    exact (aestronglyMeasurable_indicator_iff hVopen.measurableSet).mpr
      (hcontOn.aestronglyMeasurable hVopen.measurableSet)
  rw [intervalIntegrable_iff, Set.uIoc_of_le Real.two_pi_pos.le]
  refine MeasureTheory.Integrable.mono' (g := fun _ => M)
    (MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne)
    hmeas.restrict ?_
  filter_upwards with θ
  exact hbound _ (by
    simpa [mem_sphere_iff_norm] using circleMap_mem_sphere (center : ℂ) hr θ)

/-- Resolvent-identity norm bound for two circle Riesz projections.

The nonnegative-radius hypothesis is necessary: for negative radius the
resolvent hypotheses quantify over the empty sphere while the right-hand side
is negative and the left-hand side is a norm. -/
theorem norm_circleRieszProjection_sub_le
    (A E : H →L[ℂ] H) (center radius margin : ℝ) (hr : 0 ≤ radius)
    (hmargin : 0 < margin)
    (hAres : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ ≤ margin⁻¹)
    (hAEres : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - (A + E))‖ ≤ margin⁻¹) :
    ‖Frontier.circleRieszProjection (A + E) center radius -
        Frontier.circleRieszProjection A center radius‖ ≤
      radius * ‖E‖ / margin ^ 2 := by
  have hint : CircleIntegrable
      (fun z : ℂ => Ring.inverse (z • (1 : H →L[ℂ] H) - A)) center radius :=
    circleIntegrable_ringInverse_pencil A center radius margin⁻¹ hr hAres
  have hint' : CircleIntegrable
      (fun z : ℂ => Ring.inverse (z • (1 : H →L[ℂ] H) - (A + E))) center radius :=
    circleIntegrable_ringInverse_pencil (A + E) center radius margin⁻¹ hr hAEres
  have hpt : ∀ z ∈ Metric.sphere (center : ℂ) radius,
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - (A + E)) -
        Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ ≤ ‖E‖ / margin ^ 2 := by
    intro z hz
    have hzn : ‖z - (center : ℂ)‖ = radius := mem_sphere_iff_norm.mp hz
    set T : H →L[ℂ] H := z • (1 : H →L[ℂ] H) - A with hT
    set T' : H →L[ℂ] H := z • (1 : H →L[ℂ] H) - (A + E) with hT'
    have hTsub : T - T' = E := by rw [hT, hT']; abel
    have hbA : ‖Ring.inverse T‖ ≤ margin⁻¹ := hAres z hzn
    have hbAE : ‖Ring.inverse T'‖ ≤ margin⁻¹ := hAEres z hzn
    have hkey : margin ≤ ‖E‖ → margin⁻¹ ≤ ‖E‖ / margin ^ 2 := fun hEm => by
      rw [le_div_iff₀ (by positivity)]
      calc margin⁻¹ * margin ^ 2 = margin := by
            rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hmargin.ne', one_mul]
        _ ≤ ‖E‖ := hEm
    by_cases hTu : IsUnit T <;> by_cases hT'u : IsUnit T'
    · rw [ringInverse_sub_ringInverse T T' hTu hT'u, hTsub]
      calc ‖Ring.inverse T' * E * Ring.inverse T‖
          ≤ ‖Ring.inverse T' * E‖ * ‖Ring.inverse T‖ := norm_mul_le _ _
        _ ≤ ‖Ring.inverse T'‖ * ‖E‖ * ‖Ring.inverse T‖ := by
            gcongr
            exact norm_mul_le _ _
        _ ≤ margin⁻¹ * ‖E‖ * margin⁻¹ := by gcongr
        _ = ‖E‖ / margin ^ 2 := by
            rw [pow_two, div_eq_mul_inv, mul_inv]
            ring
    · rw [Ring.inverse_non_unit T' hT'u, zero_sub, norm_neg]
      have hEm : margin ≤ ‖E‖ := by
        have h := margin_le_norm_perturbation T (-E) hmargin hTu hbA (by
          intro hu
          rw [show T + -E = T' from by rw [hT, hT']; abel] at hu
          exact hT'u hu)
        rwa [norm_neg] at h
      exact hbA.trans (hkey hEm)
    · rw [Ring.inverse_non_unit T hTu, sub_zero]
      have hEm : margin ≤ ‖E‖ :=
        margin_le_norm_perturbation T' E hmargin hT'u hbAE (by
          intro hu
          rw [show T' + E = T from by rw [hT, hT']; abel] at hu
          exact hTu hu)
      exact hbAE.trans (hkey hEm)
    · rw [Ring.inverse_non_unit T hTu, Ring.inverse_non_unit T' hT'u, sub_zero,
        norm_zero]
      positivity
  have hsplit : Frontier.circleRieszProjection (A + E) center radius -
      Frontier.circleRieszProjection A center radius =
      (2 * Real.pi * Complex.I)⁻¹ •
        ∮ z in C((center : ℂ), radius),
          (Ring.inverse (z • (1 : H →L[ℂ] H) - (A + E)) -
            Ring.inverse (z • (1 : H →L[ℂ] H) - A)) := by
    rw [circleIntegral.integral_sub hint' hint, smul_sub]
    rfl
  rw [hsplit, mul_div_assoc]
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr hpt

/-- Norm continuity of the selected projection along a bounded affine
self-adjoint path.

The nonnegative-radius hypothesis is necessary: for negative radius the
resolvent hypothesis quantifies over the empty sphere, while the conclusion is
false in general. -/
theorem continuous_circleRieszProjection_path
    (A E : H →L[ℂ] H) (center radius : ℝ) (hr : 0 ≤ radius)
    (hres : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
        IsUnit (z • (1 : H →L[ℂ] H) - (A + t • E))) :
    ContinuousOn
      (fun t : ℝ => Frontier.circleRieszProjection (A + t • E) center radius)
      (Set.Icc 0 1) := by
  rw [continuousOn_iff_continuous_restrict]
  set F : Set.Icc (0 : ℝ) 1 → ℝ → (H →L[ℂ] H) := fun t θ =>
    deriv (circleMap (center : ℂ) radius) θ •
      Ring.inverse (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) -
        (A + (t : ℝ) • E)) with hF
  have hpencil : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
      circleMap (center : ℂ) radius p.2 • (1 : H →L[ℂ] H) -
        (A + (p.1 : ℝ) • E) :=
    (((continuous_circleMap _ _).comp continuous_snd).smul continuous_const).sub
      (continuous_const.add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const))
  have hderiv2 : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
      deriv (circleMap (center : ℂ) radius) p.2 := by
    have : Continuous fun θ : ℝ => deriv (circleMap (center : ℂ) radius) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 radius).mul continuous_const
    exact this.comp continuous_snd
  have hinv2 : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
      Ring.inverse (circleMap (center : ℂ) radius p.2 • (1 : H →L[ℂ] H) -
        (A + (p.1 : ℝ) • E)) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hunit : IsUnit (circleMap (center : ℂ) radius p.2 • (1 : H →L[ℂ] H) -
        (A + (p.1 : ℝ) • E)) :=
      hres p.1 p.1.2 _ (by
        simpa [mem_sphere_iff_norm] using
          circleMap_mem_sphere (center : ℂ) hr p.2)
    have hAt : ContinuousAt Ring.inverse
        (circleMap (center : ℂ) radius p.2 • (1 : H →L[ℂ] H) -
          (A + (p.1 : ℝ) • E)) := by
      have h := NormedRing.inverse_continuousAt hunit.unit
      rwa [IsUnit.unit_spec] at h
    exact hAt.comp (f := fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
      circleMap (center : ℂ) radius p.2 • (1 : H →L[ℂ] H) -
        (A + (p.1 : ℝ) • E)) hpencil.continuousAt
  have hFcont : Continuous (Function.uncurry F) := hderiv2.smul hinv2
  have hcont :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume) (f := F) hFcont 0 (2 * Real.pi)
  exact hcont.const_smul ((2 * Real.pi * Complex.I)⁻¹ : ℂ)

end RieszCircle
end Frontier
end Experimental
end DavisKahan
end ForMathlib
