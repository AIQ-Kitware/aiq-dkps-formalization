/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseCriticalAngle
import ForTauCeti.Algebra.Star.ProjectionOverlap
import ForTauCeti.Analysis.InnerProductSpace.SpectralTrace

/-!
# Strict sign of the projection-overlap curvature coefficient

The symmetrized product `A * B + B * A` has zero compression to both
small-phase complements. If the two large-phase projections overlap,
the squared compression sum is positive and its large-branch curvature
coefficient is strictly negative.

This module proves the algebraic sign in the conventional second-variation
argument. Identifying that coefficient with the second derivative of the
actual constrained Schatten curve remains a separate analytic obligation.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Overlap forces a strictly negative coefficient in the large-phase
second variation, with the Frobenius squares expressed by the actual trace. -/
theorem overlap_second_variation_coefficient_neg
    (p b : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hb : b ∈ Set.Ioo (criticalAngle p) Real.pi)
    (A B : E →L[ℂ] E) (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hAB : A * B ≠ 0) :
    4 * p * amplitudeDerivative p b *
      ((LinearMap.trace ℂ E ((A * B * A).adjoint * (A * B * A)).toLinearMap).re +
        (LinearMap.trace ℂ E ((B * A * B).adjoint * (B * A * B)).toLinearMap).re) < 0 := by
  have hABA : A * B * A ≠ 0 := fun h =>
    hAB ((projection_compression_eq_zero_iff_mul_eq_zero hA hB).1 h)
  have hpos := (ContinuousLinearMap.re_trace_adjoint_mul_self_pos_iff (A * B * A)).2 hABA
  have hnonneg := ContinuousLinearMap.re_trace_adjoint_mul_self_nonneg (B * A * B)
  have hcurvature : 4 * p * amplitudeDerivative p b < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by norm_num) (by linarith))
      (amplitudeDerivative_neg_of_criticalAngle_lt p b hp1 hp2 hb.1 hb.2)
  exact mul_neg_of_neg_of_pos hcurvature (add_pos_of_pos_of_nonneg hpos hnonneg)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
