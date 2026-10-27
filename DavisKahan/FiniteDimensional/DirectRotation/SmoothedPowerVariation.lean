/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SmoothedPowerPhaseSymbol
public import ForTauCeti.Analysis.InnerProductSpace.UnitaryPhaseHessian
public import ForTauCeti.Analysis.CStarAlgebra.TwoPointDerivative

/-!
# A common second variation for smoothed-power transport penalties

The actual spectral trace for `(tau²+s²)^(p/2)-tau^p` has the common
compressed Hessian at equal-gradient phase pairs. The paired overlap
direction excludes intersecting negative-curvature spectral factors.

This extends the verified operator variation argument to all positively
smoothed convex powers, rather than dispatching to the existing Schatten
and Charbonnier optimization results. It is one structural ingredient of
the conjectural unrestricted decoupling theorem, not that theorem itself.
The analytic two-point CFC derivative and trace-Hessian mechanism are
classical ingredients reused from the donor layer; historical priority of
the resulting family transport theory remains unresolved.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The analytic extension is exactly the actual self-adjoint unitary
phase gradient, with no eigenphase argument choices. -/
theorem unitaryPhaseGradient_eq_cfc_extension (p tau : ℝ)
    (U : unitary (E →L[ℂ] E)) :
    unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E) =
      cfc (smoothedPowerPhaseExtension p tau) (U : E →L[ℂ] E) := by
  unfold unitaryPhaseGradient
  apply cfc_congr
  intro z hz
  symm
  exact smoothedPowerPhaseExtension_eq_of_norm_eq_one p tau z
    (by simpa only [Metric.mem_sphere, dist_zero_right] using
      spectrum.subset_circle_of_unitary U.2 hz)

/-- The actual gradient derivative has only the two spectral compressions
when the two phase-gradient values agree. No dimension restriction is
needed for this CFC statement. -/
theorem hasDerivAt_gradient_two_phase
    (p tau alpha beta : ℝ) (htau : 0 < tau)
    (hab : Complex.exp ((alpha : ℂ) * Complex.I) ≠
      Complex.exp ((beta : ℂ) * Complex.I))
    (hlevel : smoothedPowerPhaseSlope p tau alpha = smoothedPowerPhaseSlope p tau beta)
    (U : ℝ → E →L[ℂ] E) (x : ℝ) (H : E →L[ℂ] E)
    (hunit : ∀ t, U t ∈ unitary (E →L[ℂ] E))
    (hU : HasDerivAt U (U x * (Complex.I • H)) x)
    (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (hrepr : U x = Complex.exp ((alpha : ℂ) * Complex.I) • 1 +
      (Complex.exp ((beta : ℂ) * Complex.I) -
        Complex.exp ((alpha : ℂ) * Complex.I)) • P) :
    HasDerivAt (fun t => unitaryPhaseGradient
      (smoothedPowerDisplacementGradient p tau) (U t))
      ((smoothedPowerPhaseCurvature p tau alpha : ℂ) • ((1 - P) * H * (1 - P)) +
       (smoothedPowerPhaseCurvature p tau beta : ℂ) • (P * H * P)) x := by
  let a := Complex.exp ((alpha : ℂ) * Complex.I)
  let b := Complex.exp ((beta : ℂ) * Complex.I)
  have hfa : smoothedPowerPhaseExtension p tau a = (smoothedPowerPhaseSlope p tau alpha : ℂ) := by
    rw [smoothedPowerPhaseExtension_eq_of_norm_eq_one p tau _
      (Complex.norm_exp_ofReal_mul_I alpha), smoothedPowerPhaseDerivative_exp]
  have hfb : smoothedPowerPhaseExtension p tau b = (smoothedPowerPhaseSlope p tau alpha : ℂ) := by
    rw [smoothedPowerPhaseExtension_eq_of_norm_eq_one p tau _
      (Complex.norm_exp_ofReal_mul_I beta), smoothedPowerPhaseDerivative_exp, ← hlevel]
  have hd := hasDerivAt_cfc_unitary_tangent_of_affine_projection
    (smoothedPowerPhaseExtension p tau) a b (smoothedPowerPhaseSlope p tau alpha : ℂ)
    (smoothedPowerPhaseCurvature p tau alpha : ℂ) (smoothedPowerPhaseCurvature p tau beta : ℂ)
    hab hfa hfb (Metric.sphere (0 : ℂ) 1) (isCompact_sphere 0 1)
    (continuousOn_smoothedPowerPhaseExtension_circle p tau htau)
    (differentiableAt_smoothedPowerPhaseExtension p tau htau a
      (Complex.norm_exp_ofReal_mul_I alpha))
    (differentiableAt_smoothedPowerPhaseExtension p tau htau b
      (Complex.norm_exp_ofReal_mul_I beta))
    (smoothedPowerPhaseExtension_deriv_mul_I_exp p tau alpha htau)
    (smoothedPowerPhaseExtension_deriv_mul_I_exp p tau beta htau)
    U x H hU (fun t => isStarNormal_of_mem_unitary (hunit t))
    (fun t => spectrum.subset_circle_of_unitary (hunit t)) P hP hrepr
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    unitaryPhaseGradient_eq_cfc_extension p tau ⟨U t, hunit t⟩)

variable [FiniteDimensional ℂ E]

/-- The literal finite spectral trace of the common displacement penalty. -/
@[expose] def displacementCost (p tau : ℝ) (U : E →L[ℂ] E) : ℝ :=
  (LinearMap.trace ℂ E
    (cfc (fun z => (smoothedPowerDisplacementSymbol p tau z : ℂ)) U).toLinearMap).re

/-- **Ambient constrained stationarity for the family.** At every local
minimum on the full complex transport fiber, reflection in the source
projection negates the actual phase gradient. No invariant principal-plane
or paired-block hypothesis is assumed. The trace-compression argument adapts
`SmoothedStationarity`, with the common family first variation as input. -/
theorem gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    (p tau : ℝ) (hp : 1 ≤ p) (htau : 0 < tau)
    (P Q : E →L[ℂ] E) (hP : IsStarProjection P)
    (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * P * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn (displacementCost p tau)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = Q} (U : E →L[ℂ] E)) :
    let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
    ((2 : ℂ) • P - 1) * G * ((2 : ℂ) • P - 1) = -G := by
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  have hG : IsSelfAdjoint G := isSelfAdjoint_unitaryPhaseGradient _ _
  have hstat (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (hHP : Commute H P) :
      (LinearMap.trace ℂ E (G * H).toLinearMap).re = 0 := by
    have hcurve := isLocalMin_unitary_right_variation_of_isLocalMinOn_conjugacy
      (displacementCost p tau) P Q U htrans hmin H hH hHP
    have hfirst := hasDerivAt_smoothedPower_unitary_right_variation_at p tau hp htau U H hH 0
    simp only [zero_smul, NormedSpace.exp_zero, mul_one] at hfirst
    exact hcurve.hasDerivAt_eq_zero hfirst
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

/-- Actual second variation for the whole positively smoothed convex-power
family. Equal-gradient phases eliminate mixed spectral Hessian terms. -/
theorem hasDerivAt_deriv_cost_two_phase
    (p tau alpha beta : ℝ) (hp : 1 ≤ p) (htau : 0 < tau)
    (hab : Complex.exp ((alpha : ℂ) * Complex.I) ≠
      Complex.exp ((beta : ℂ) * Complex.I))
    (hlevel : smoothedPowerPhaseSlope p tau alpha = smoothedPowerPhaseSlope p tau beta)
    (U : unitary (E →L[ℂ] E)) (H P : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P)
    (hrepr : (U : E →L[ℂ] E) = Complex.exp ((alpha : ℂ) * Complex.I) • 1 +
      (Complex.exp ((beta : ℂ) * Complex.I) -
        Complex.exp ((alpha : ℂ) * Complex.I)) • P) :
    HasDerivAt (deriv (fun t : ℝ => displacementCost p tau
      ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H)))))
      (smoothedPowerPhaseCurvature p tau alpha * (LinearMap.trace ℂ E
        (((1 - P) * H * (1 - P)).adjoint * ((1 - P) * H * (1 - P))).toLinearMap).re +
       smoothedPowerPhaseCurvature p tau beta *
        (LinearMap.trace ℂ E ((P * H * P).adjoint * (P * H * P)).toLinearMap).re) 0 := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  let V : ℝ → E →L[ℂ] E := fun t =>
    (U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))
  have hunit (t : ℝ) : V t ∈ unitary (E →L[ℂ] E) := by
    apply mul_mem U.2
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  have hV0 : V 0 = (U : E →L[ℂ] E) := by simp only [V, zero_smul, NormedSpace.exp_zero, mul_one]
  have hV : HasDerivAt V (V 0 * (Complex.I • H)) 0 := by
    simpa only [V, zero_smul, NormedSpace.exp_zero, mul_one, one_mul] using
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • H) (0 : ℝ)).const_mul
        (U : E →L[ℂ] E)
  exact hasDerivAt_deriv_unitary_cost_of_compressed_gradient
    (displacementCost p tau) (unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau))
    U H P hH hP (smoothedPowerPhaseCurvature p tau alpha) (smoothedPowerPhaseCurvature p tau beta)
    (fun t => hasDerivAt_smoothedPower_unitary_right_variation_at p tau hp htau U H hH t)
    (hasDerivAt_gradient_two_phase p tau alpha beta htau hab hlevel V 0 H hunit hV P hP
      (hV0.trans hrepr))

/-- **Family-wide overlap exclusion.** At a local minimum of the actual
paired spectral cost, the high-phase factors are orthogonal whenever their
phase lies beyond the common critical surface. The coupled variation must
be feasible before applying this statement to an ambient transport fiber. -/
theorem highPhaseProjections_mul_eq_zero_of_localMin
    (p tau a b : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (hab : Complex.exp ((a : ℂ) * Complex.I) ≠ Complex.exp ((b : ℂ) * Complex.I))
    (hbalance : smoothedPowerPhaseSlope p tau a = smoothedPowerPhaseSlope p tau b)
    (hnegative : Real.cos b < smoothedPowerCriticalCosine p tau)
    (U V : unitary (E →L[ℂ] E)) (A B : E →L[ℂ] E)
    (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hU : (U : E →L[ℂ] E) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A)
    (hV : (V : E →L[ℂ] E) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B)
    (hmin : IsLocalMin (fun t : ℝ =>
      displacementCost p tau ((U : E →L[ℂ] E) *
        NormedSpace.exp (t • (Complex.I • (A * B + B * A)))) +
      displacementCost p tau ((V : E →L[ℂ] E) *
        NormedSpace.exp (t • (Complex.I • (A * B + B * A))))) 0) : A * B = 0 := by
  let X := A * B + B * A
  let CU := fun t : ℝ => displacementCost p tau
    ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • X)))
  let CV := fun t : ℝ => displacementCost p tau
    ((V : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • X)))
  have hX : IsSelfAdjoint X :=
    isSelfAdjoint_projection_overlap hA.isSelfAdjoint hB.isSelfAdjoint
  have hcb : smoothedPowerPhaseCurvature p tau b < 0 :=
    (smoothedPowerPhaseCurvature_neg_iff_cos_lt_critical p tau b hp hp2 htau).2 hnegative
  have habneg : Complex.exp (((-a : ℝ) : ℂ) * Complex.I) ≠
      Complex.exp (((-b : ℝ) : ℂ) * Complex.I) := by
    simp only [Complex.ofReal_neg, neg_mul, Complex.exp_neg]
    exact fun h => hab (inv_injective h)
  have hbalneg : smoothedPowerPhaseSlope p tau (-a) = smoothedPowerPhaseSlope p tau (-b) := by
    have hodd (t : ℝ) : smoothedPowerPhaseSlope p tau (-t) =
        -smoothedPowerPhaseSlope p tau t := by
      simp only [smoothedPowerPhaseSlope, Real.sin_neg, Real.cos_neg]
      ring
    rw [hodd, hodd, hbalance]
  have hDU := hasDerivAt_deriv_cost_two_phase p tau a b hp htau hab hbalance U X A hX hA hU
  have hDV := hasDerivAt_deriv_cost_two_phase p tau (-a) (-b) hp htau habneg hbalneg V X B hX hB hV
  simp only [smoothedPowerPhaseCurvature_neg] at hDV
  exact projection_overlap_eq_zero_of_paired_second_variations CU CV
    (fun t => by
      exact (hasDerivAt_smoothedPower_unitary_right_variation_at p tau hp htau U X hX t).differentiableAt)
    (fun t => by
      exact (hasDerivAt_smoothedPower_unitary_right_variation_at p tau hp htau V X hX t).differentiableAt)
    A B hA hB (smoothedPowerPhaseCurvature p tau a) (smoothedPowerPhaseCurvature p tau b)
    (smoothedPowerPhaseCurvature p tau a) (smoothedPowerPhaseCurvature p tau b)
    hcb hcb.le hDU hDV hmin

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
