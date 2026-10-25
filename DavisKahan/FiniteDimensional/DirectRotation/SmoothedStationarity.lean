/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedUnitaryVariation

/-!
# Stationarity of constrained Charbonnier transport

Right multiplication by `exp (i t H)` preserves a unitary transport from `P`
to `Q` whenever the Hermitian direction `H` commutes with `P`. At a local
minimum its first variation vanishes. This is the constrained analytic input
for the spectral block reduction in smoothed transport optimization.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The Charbonnier unitary gradient annihilates every Hermitian direction
commuting with the source projection at a local constrained minimum.
The feasibility argument only uses conjugacy, so `P,Q` need not be projections
for this particular theorem. -/
theorem re_trace_gradient_mul_eq_zero_of_isLocalMinOn_transports
    (tau : ℝ) (htau : 0 < tau)
    (P Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * P * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = Q}
      (U : E →L[ℂ] E))
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (hHP : Commute H P) :
    (LinearMap.trace ℂ E
      (smoothedUnitaryGradient tau (U : E →L[ℂ] E) * H).toLinearMap).re = 0 := by
  have hcurve := isLocalMin_unitary_right_variation_of_isLocalMinOn_conjugacy
    (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
    P Q U htrans hmin H hH hHP
  exact hcurve.hasDerivAt_eq_zero
    (hasDerivAt_smoothed_unitary_right_variation tau htau U H hH)

/-- **The constrained stationarity identity.** Reflection in the source
projection negates the self-adjoint unitary gradient at a local minimum.
Equivalently, its two diagonal compressions relative to `P` vanish. -/
theorem gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    (tau : ℝ) (htau : 0 < tau)
    (P Q : E →L[ℂ] E) (hP : IsStarProjection P)
    (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * P * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = Q}
      (U : E →L[ℂ] E)) :
    ((2 : ℂ) • P - 1) * smoothedUnitaryGradient tau (U : E →L[ℂ] E) *
        ((2 : ℂ) • P - 1) = -smoothedUnitaryGradient tau (U : E →L[ℂ] E) := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  have hG : IsSelfAdjoint G := isSelfAdjoint_smoothedUnitaryGradient _ _
  have hstat (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (hHP : Commute H P) :
      (LinearMap.trace ℂ E (G * H).toLinearMap).re = 0 :=
    re_trace_gradient_mul_eq_zero_of_isLocalMinOn_transports tau htau P Q U htrans hmin H hH hHP
  have hdiag := ContinuousLinearMap.projection_compression_eq_zero_of_trace_pairing_eq_zero
    G P hG hP hstat
  have hdiag' := ContinuousLinearMap.projection_compression_eq_zero_of_trace_pairing_eq_zero
    G (1 - P) hG hP.one_sub (fun H hH hHP => hstat H hH (by
      have heq := hHP.eq
      simp only [mul_sub, sub_mul, mul_one, one_mul] at heq
      change H * P = P * H
      simpa only [sub_sub_cancel] using congrArg (fun A => H - A) heq))
  change ((2 : ℂ) • P - 1) * G * ((2 : ℂ) • P - 1) = -G
  calc
    _ = -G + (P * G * P + P * G * P) +
        ((1 - P) * G * (1 - P) + (1 - P) * G * (1 - P)) := by
      simp only [two_smul]
      noncomm_ring
    _ = -G := by rw [hdiag, hdiag']; simp

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
