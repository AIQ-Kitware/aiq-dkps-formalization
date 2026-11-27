/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import DavisKahan.SpectralTheory.CircleRieszProjection
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Cycle

/-!
# The two endpoints of the circle Riesz projection

`circleRieszProjection A center radius` is the contour integral
`(2 π i)⁻¹ ∮_{|z - c| = r} (z - A)⁻¹ dz`.  This file evaluates it in the two
degenerate positions of the circle relative to the spectrum:

* `circleRieszProjection_eq_zero`: the closed disc misses the spectrum
  entirely, so the integrand is holomorphic there and Cauchy's theorem gives
  `0`;
* `circleRieszProjection_eq_one`: the open disc contains the whole spectrum,
  so the projection is the identity.

Neither statement needs self-adjointness, and neither goes through the
measurable functional calculus: they are Cauchy theory for the resolvent, and
they hold for any bounded operator.  That is what makes them usable as the two
endpoints of the Rosenblum contour argument for the Sylvester equation
(`DavisKahan.Sylvester.RosenblumExistence`), which has no self-adjointness to
appeal to.

For the identity endpoint, the circle cycle lies in the resolvent set and
winds once around each spectral point. TauCeti's contour-cycle resolvent
integral then gives `2 π i` times the identity before normalization.
-/

public section

open Metric Set Filter Complex
open scoped Topology Real

namespace TauCeti
namespace DavisKahan

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

section Pencil

omit [CompleteSpace H] in
/-- Off the spectrum the resolvent pencil `z • 1 - A` is a unit.  This is
`spectrum.notMem_iff` in the `z • 1` normalisation that `circleRieszProjection`
uses. -/
theorem isUnit_smul_one_sub_of_notMem_spectrum {A : H →L[ℂ] H} {z : ℂ}
    (hz : z ∉ spectrum ℂ A) : IsUnit (z • (1 : H →L[ℂ] H) - A) := by
  have h := spectrum.notMem_iff.mp hz
  rwa [Algebra.algebraMap_eq_smul_one] at h

omit [CompleteSpace H] in
/-- The integrand of `circleRieszProjection` is Mathlib's `resolvent`. -/
theorem ringInverse_smul_one_sub_eq_resolvent (A : H →L[ℂ] H) (z : ℂ) :
    Ring.inverse (z • (1 : H →L[ℂ] H) - A) = resolvent A z := by
  rw [resolvent, Algebra.algebraMap_eq_smul_one]

/-- The resolvent is complex differentiable off the spectrum. -/
theorem differentiableAt_ringInverse_smul_one_sub (A : H →L[ℂ] H) {z : ℂ}
    (hz : z ∉ spectrum ℂ A) :
    DifferentiableAt ℂ
      (fun w : ℂ => Ring.inverse (w • (1 : H →L[ℂ] H) - A)) z := by
  have haff : DifferentiableAt ℂ (fun w : ℂ => w • (1 : H →L[ℂ] H) - A) z :=
    (differentiableAt_id.smul_const _).sub_const _
  exact (differentiableAt_inverse
    (isUnit_smul_one_sub_of_notMem_spectrum hz)).comp z haff

end Pencil

section Zero

/-- **The vanishing endpoint.**  A circle whose closed disc misses the spectrum
carries no Riesz projection: the resolvent is holomorphic on the disc, so
Cauchy's theorem applies. -/
theorem circleRieszProjection_eq_zero (A : H →L[ℂ] H) {center radius : ℝ}
    (hr : 0 < radius)
    (hspec : ∀ z : ℂ, z ∈ closedBall (center : ℂ) radius → z ∉ spectrum ℂ A) :
    circleRieszProjection A center radius = 0 := by
  have hdiff : DiffContOnCl ℂ
      (fun z : ℂ => Ring.inverse (z • (1 : H →L[ℂ] H) - A))
      (ball (center : ℂ) radius) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro z hz
    exact (differentiableAt_ringInverse_smul_one_sub A
      (hspec z hz)).differentiableWithinAt
  rw [circleRieszProjection, DiffContOnCl.circleIntegral_eq_zero hr.le hdiff,
    smul_zero]

end Zero

section One

variable (A : H →L[ℂ] H) {center radius : ℝ}

omit [CompleteSpace H] in
/-- The resolvent, split into its principal part at the centre and a remainder.
This is the algebraic heart of the `= 1` endpoint: the principal part carries
the whole `2 π i`, and the remainder is `O(|z - c|⁻¹)` times the resolvent, so
it dies at infinity. -/
theorem ringInverse_smul_one_sub_eq_principal_add_remainder
    {z : ℂ} (hz : z ∉ spectrum ℂ A) (hzc : z ≠ (center : ℂ)) :
    Ring.inverse (z • (1 : H →L[ℂ] H) - A) =
      (z - (center : ℂ))⁻¹ • (1 : H →L[ℂ] H) +
        (z - (center : ℂ))⁻¹ •
          ((A - (center : ℂ) • (1 : H →L[ℂ] H)) *
            Ring.inverse (z • (1 : H →L[ℂ] H) - A)) := by
  have hne : z - (center : ℂ) ≠ 0 := sub_ne_zero.mpr hzc
  set R := Ring.inverse (z • (1 : H →L[ℂ] H) - A) with hR
  have hcancel : (z • (1 : H →L[ℂ] H) - A) * R = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_smul_one_sub_of_notMem_spectrum hz)
  -- `(z - c) • R = 1 + (A - c) * R`, then divide by `z - c`.
  have hkey : (z - (center : ℂ)) • R =
      1 + (A - (center : ℂ) • (1 : H →L[ℂ] H)) * R := by
    have hsplit : z • (1 : H →L[ℂ] H) - A =
        (z - (center : ℂ)) • (1 : H →L[ℂ] H) -
          (A - (center : ℂ) • (1 : H →L[ℂ] H)) := by
      rw [sub_smul]; abel
    rw [hsplit, sub_mul, smul_mul_assoc, one_mul] at hcancel
    exact sub_eq_iff_eq_add.mp hcancel
  rw [← smul_add, ← hkey, smul_smul, inv_mul_cancel₀ hne, one_smul]

omit [CompleteSpace H] in
/-- The remainder term is bounded by the resolvent, uniformly on a circle. -/
theorem norm_remainder_le {z : ℂ} (hz : z ∉ spectrum ℂ A) (hzc : z ≠ (center : ℂ)) :
    ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A) -
        (z - (center : ℂ))⁻¹ • (1 : H →L[ℂ] H)‖ ≤
      ‖z - (center : ℂ)‖⁻¹ * ‖A - (center : ℂ) • (1 : H →L[ℂ] H)‖ *
        ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ := by
  conv_lhs => rw [ringInverse_smul_one_sub_eq_principal_add_remainder A hz hzc]
  rw [add_sub_cancel_left, norm_smul, norm_inv, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)

end One

/-- A circle whose open disc contains the whole spectrum carries the identity. -/
theorem circleRieszProjection_eq_one (A : H →L[ℂ] H) {center radius : ℝ}
    (hr : 0 < radius) (hspec : spectrum ℂ A ⊆ ball (center : ℂ) radius) :
    circleRieszProjection A center radius = 1 := by
  have hΓ : Contour.Cycle.IsIn (Contour.circleCycle (center : ℂ) radius)
      (resolventSet ℂ A) := by
    rw [Contour.Cycle.isIn_iff, Contour.Cycle.trace_circleCycle, abs_of_pos hr]
    intro z hz
    refine spectrum.notMem_iff.mp fun h => ?_
    exact (mem_ball.mp (hspec h)).ne (mem_sphere.mp hz)
  have hwind (z : ℂ) (hz : z ∈ spectrum ℂ A) :
      Contour.Cycle.windingNumber z (Contour.circleCycle (center : ℂ) radius) = 1 :=
    Contour.Cycle.windingNumber_circleCycle_eq_one_of_dist_lt (mem_ball.mp (hspec hz))
  rw [circleRieszProjection]
  simp_rw [ringInverse_smul_one_sub_eq_resolvent]
  rw [← Contour.Cycle.integral_circleCycle, Contour.Cycle.integral_resolvent hΓ hwind,
    smul_smul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]

end DavisKahan
end TauCeti
