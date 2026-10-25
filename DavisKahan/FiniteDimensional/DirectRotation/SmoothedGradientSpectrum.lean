/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedStationarity
public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction
public import ForTauCeti.Analysis.CStarAlgebra.TwoPointSpectrum

/-!
# Sharp gradient bounds and actual zero-gradient blocks

The squared scalar gradient deficit is an explicit nonnegative square.
It gives the sharp bound `1 / smoothingRadius tau`, with equality exactly
at the critical real part. On its actual gradient kernel every unitary
restricts to an orthogonal reflection. No minimizing hypothesis is needed
for this exceptional-block representation.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped ComplexConjugate

/-- Exact scalar gradient deficit on the unit circle. -/
theorem smoothedPhaseDerivative_sq_defect
    (tau : ℝ) (htau : 0 < tau) (z : ℂ) (hz : ‖z‖ = 1) :
    ((smoothingRadius tau)⁻¹) ^ 2 - (smoothedPhaseDerivative tau z) ^ 2 =
      (z.re - ((smoothingRadius tau)⁻¹) ^ 2) ^ 2 / (tau ^ 2 + ‖z - 1‖ ^ 2) := by
  let a := smoothingRadius tau
  have ha : 0 < a := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hprod : a ^ 2 * (a⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ha.ne', one_pow]
  have hsum := smoothingRadius_sq_add_inv_sq tau htau
  change a ^ 2 + (a⁻¹) ^ 2 = tau ^ 2 + 2 at hsum
  have hroot : (a⁻¹) ^ 2 * (tau ^ 2 + 2) = 1 + ((a⁻¹) ^ 2) ^ 2 := by
    nlinarith only [congrArg (fun r : ℝ => (a⁻¹) ^ 2 * r) hsum, hprod]
  have hcircle := Complex.norm_sub_one_sq_eq_of_norm_eq_one hz
  have hnorm := Complex.normSq_eq_norm_sq z
  rw [hz, one_pow, Complex.normSq_apply] at hnorm
  have hrad : 0 < tau ^ 2 + ‖z - 1‖ ^ 2 := by positivity
  rw [smoothedPhaseDerivative_eq, div_pow, Real.sq_sqrt hrad.le]
  apply (eq_div_iff hrad.ne').mpr
  rw [sub_mul, div_mul_cancel₀ _ hrad.ne']
  change (a⁻¹) ^ 2 * (tau ^ 2 + ‖z - 1‖ ^ 2) - z.im ^ 2 = _
  nlinarith only [hroot, hcircle, hnorm]

/-- The scalar phase gradient is bounded by the inverse smoothing radius. -/
theorem abs_smoothedPhaseDerivative_le
    (tau : ℝ) (htau : 0 < tau) (z : ℂ) (hz : ‖z‖ = 1) :
    |smoothedPhaseDerivative tau z| ≤ (smoothingRadius tau)⁻¹ := by
  have ha : 0 < smoothingRadius tau := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hd := smoothedPhaseDerivative_sq_defect tau htau z hz
  have hn : 0 ≤ (z.re - ((smoothingRadius tau)⁻¹) ^ 2) ^ 2 /
      (tau ^ 2 + ‖z - 1‖ ^ 2) := by positivity
  apply (sq_le_sq₀ (abs_nonneg _) (inv_nonneg.mpr ha.le)).mp
  rw [sq_abs]
  linarith

/-- Equality in the sharp gradient bound detects exactly the critical real part. -/
theorem abs_smoothedPhaseDerivative_eq_iff
    (tau : ℝ) (htau : 0 < tau) (z : ℂ) (hz : ‖z‖ = 1) :
    |smoothedPhaseDerivative tau z| = (smoothingRadius tau)⁻¹ ↔
      z.re = ((smoothingRadius tau)⁻¹) ^ 2 := by
  have ha : 0 < smoothingRadius tau := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  have hd := smoothedPhaseDerivative_sq_defect tau htau z hz
  have hrad : tau ^ 2 + ‖z - 1‖ ^ 2 ≠ 0 := by positivity
  constructor
  · intro heq
    have hs := congrArg (fun r : ℝ => r ^ 2) heq
    rw [sq_abs] at hs
    have hzero : (z.re - ((smoothingRadius tau)⁻¹) ^ 2) ^ 2 = 0 := by
      apply (div_eq_zero_iff.mp (show
        (z.re - ((smoothingRadius tau)⁻¹) ^ 2) ^ 2 / (tau ^ 2 + ‖z - 1‖ ^ 2) = 0 by
          linarith)).resolve_right hrad
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  · intro heq
    rw [heq, sub_self, zero_pow (by norm_num), zero_div, sub_eq_zero] at hd
    apply (sq_eq_sq₀ (abs_nonneg _) (inv_nonneg.mpr ha.le)).mp
    rw [sq_abs]
    exact hd.symm

/-- Every gradient level gives a quadratic equation for the real part.
This includes zero and maximal levels, with no phase-coordinate choice. -/
theorem smoothedPhaseDerivative_level_quadratic
    (tau : ℝ) (htau : 0 < tau) (g : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (hlevel : smoothedPhaseDerivative tau z = g) :
    (z.re - g ^ 2) ^ 2 = g ^ 4 - (tau ^ 2 + 2) * g ^ 2 + 1 := by
  rw [smoothedPhaseDerivative_eq] at hlevel
  have him := (div_eq_iff (charbonnier_radius_pos tau htau z).ne').mp hlevel
  have hs := congrArg (fun r : ℝ => r ^ 2) him
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hs
  have hcircle := Complex.norm_sub_one_sq_eq_of_norm_eq_one hz
  have hnorm := Complex.normSq_eq_norm_sq z
  rw [hz, one_pow, Complex.normSq_apply] at hnorm
  nlinarith only [hs, hcircle, hnorm]

/-- One of the two algebraic candidates on a smoothed phase-gradient level.
Only signs `1` and `-1` are used; existence of a level is a separate condition. -/
@[expose] def smoothedGradientCandidate (tau g sign : ℝ) : ℂ :=
  let c := g ^ 2 + sign * Real.sqrt (g ^ 4 - (tau ^ 2 + 2) * g ^ 2 + 1)
  (c : ℂ) + ((g * Real.sqrt (tau ^ 2 + 2 - 2 * c) : ℝ) : ℂ) * Complex.I

/-- The two explicit candidates exhaust every gradient level on the unit circle.
The candidates may coincide; their membership in the level is not asserted. -/
theorem smoothedPhaseDerivative_level_subset_pair
    (tau : ℝ) (htau : 0 < tau) (g : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (hlevel : smoothedPhaseDerivative tau z = g) :
    z = smoothedGradientCandidate tau g 1 ∨ z = smoothedGradientCandidate tau g (-1) := by
  have hquad := smoothedPhaseDerivative_level_quadratic tau htau g z hz hlevel
  have hs := congrArg Real.sqrt hquad
  rw [Real.sqrt_sq_eq_abs] at hs
  have hroots : z.re = g ^ 2 + Real.sqrt (g ^ 4 - (tau ^ 2 + 2) * g ^ 2 + 1) ∨
      z.re = g ^ 2 - Real.sqrt (g ^ 4 - (tau ^ 2 + 2) * g ^ 2 + 1) := by
    rcases le_total 0 (z.re - g ^ 2) with h | h
    · rw [abs_of_nonneg h] at hs
      exact Or.inl (by linarith)
    · rw [abs_of_nonpos h] at hs
      exact Or.inr (by linarith)
  rw [smoothedPhaseDerivative_eq] at hlevel
  have him := (div_eq_iff (charbonnier_radius_pos tau htau z).ne').mp hlevel
  rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one hz] at him
  have hform : z = (z.re : ℂ) +
      ((g * Real.sqrt (tau ^ 2 + 2 - 2 * z.re) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      convert him using 1
      congr 2
      ring
  rcases hroots with h | h
  · left
    rw [hform]
    simp only [smoothedGradientCandidate, one_mul, h]
  · right
    rw [hform]
    simp only [smoothedGradientCandidate, neg_one_mul, ← sub_eq_add_neg, h]

/-- The scalar bound is attained by an actual unit-circle phase. -/
theorem exists_smoothedPhaseDerivative_attaining_bound
    (tau : ℝ) (htau : 0 < tau) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ |smoothedPhaseDerivative tau z| = (smoothingRadius tau)⁻¹ := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb0 : 0 < a⁻¹ := inv_pos.mpr ha0
  have hb1 : a⁻¹ < 1 := (inv_lt_one₀ ha0).mpr ha
  have halpha : (a⁻¹) ^ 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith
  refine ⟨Complex.exp ((Real.arccos ((a⁻¹) ^ 2) : ℂ) * Complex.I),
    Complex.norm_exp_ofReal_mul_I _, ?_⟩
  apply (abs_smoothedPhaseDerivative_eq_iff tau htau _
    (Complex.norm_exp_ofReal_mul_I _)).mpr
  rw [Complex.exp_ofReal_mul_I_re]
  exact Real.cos_arccos halpha.1 halpha.2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
/-- The actual ambient phase gradient obeys the same sharp operator norm bound. -/
theorem norm_smoothedUnitaryGradient_le
    (tau : ℝ) (htau : 0 < tau) (U : unitary (E →L[ℂ] E)) :
    ‖smoothedUnitaryGradient tau (U : E →L[ℂ] E)‖ ≤ (smoothingRadius tau)⁻¹ := by
  have ha : 0 < smoothingRadius tau := zero_lt_one.trans (one_lt_smoothingRadius tau htau)
  change ‖cfc (fun z => (smoothedPhaseDerivative tau z : ℂ)) (U : E →L[ℂ] E)‖ ≤ _
  apply norm_cfc_le (inv_nonneg.mpr ha.le)
  intro z hz
  have hnorm : ‖z‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      spectrum.subset_circle_of_unitary U.property hz
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    abs_smoothedPhaseDerivative_le tau htau z hnorm

/-- An actual critical-phase eigenvector makes the operator norm bound sharp. -/
theorem norm_smoothedUnitaryGradient_eq_of_critical_eigenvector
    (tau : ℝ) (htau : 0 < tau) (U : unitary (E →L[ℂ] E))
    (x : E) (hx : x ≠ 0) (mu : ℂ) (hU : (U : E →L[ℂ] E) x = mu • x)
    (hcrit : mu.re = ((smoothingRadius tau)⁻¹) ^ 2) :
    ‖smoothedUnitaryGradient tau (U : E →L[ℂ] E)‖ = (smoothingRadius tau)⁻¹ := by
  have hnorm : ‖mu‖ = 1 := by
    have h := _root_.ContinuousLinearMap.norm_map_of_mem_unitary U.2 x
    rw [hU, norm_smul] at h
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hx) (by simpa using h)
  have hphase := (abs_smoothedPhaseDerivative_eq_iff tau htau mu hnorm).mpr hcrit
  have hbound := (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).le_opNorm x
  rw [smoothedUnitaryGradient_apply_of_apply_eq_smul tau _ x mu hU,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, hphase] at hbound
  exact le_antisymm (norm_smoothedUnitaryGradient_le tau htau U)
    ((mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx)).mp hbound)

set_option maxHeartbeats 600000 in
private theorem two_phase_representation_on_invariant_subspace
    (tau : ℝ) (htau : 0 < tau) (g : ℝ) (U : unitary (E →L[ℂ] E))
    (N : Submodule ℂ E) (hinv : ∀ x ∈ N, (U : E →L[ℂ] E) x ∈ N)
    (hlevel : ∀ x ∈ N, smoothedUnitaryGradient tau (U : E →L[ℂ] E) x = (g : ℂ) • x) :
    ∃ (V : N ≃ₗᵢ[ℂ] N) (S : N →L[ℂ] N), IsStarProjection S ∧
      (∀ x : N, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : N →L[ℂ] N) = smoothedGradientCandidate tau g 1 • 1 +
        (smoothedGradientCandidate tau g (-1) - smoothedGradientCandidate tau g 1) • S := by
  obtain ⟨V, hV, _, _⟩ :=
    (Unitary.linearIsometryEquiv U).exists_restriction_of_finite_invariant N hinv
  let : IsStarNormal (V : N →L[ℂ] N) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm V).property
  have hs : spectrum ℂ (V : N →L[ℂ] N) ⊆
      {smoothedGradientCandidate tau g 1, smoothedGradientCandidate tau g (-1)} := by
    intro mu hmu
    rw [_root_.ContinuousLinearMap.spectrum_eq] at hmu
    obtain ⟨x, hx⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.2 hmu).exists_hasEigenvector
    have hx0 : (x : E) ≠ 0 := fun h => hx.2 (Subtype.ext h)
    have hxU : (U : E →L[ℂ] E) (x : E) = mu • (x : E) :=
      (hV x).symm.trans (congrArg (fun y : N => (y : E)) hx.apply_eq_smul)
    have hnorm : ‖mu‖ = 1 := by
      have h := _root_.ContinuousLinearMap.norm_map_of_mem_unitary U.2 (x : E)
      rw [hxU, norm_smul] at h
      exact mul_right_cancel₀ (norm_ne_zero_iff.2 hx0) (by simpa using h)
    have hGx := smoothedUnitaryGradient_apply_of_apply_eq_smul tau _ _ mu hxU
    rw [hlevel x x.property] at hGx
    have hscalar : smoothedPhaseDerivative tau mu = g := by
      exact_mod_cast (smul_left_injective ℂ hx0 hGx).symm
    exact smoothedPhaseDerivative_level_subset_pair tau htau g mu hnorm hscalar
  obtain ⟨S, hS, hrepr⟩ := exists_isStarProjection_eq_affine_of_spectrum_subset_pair
    (V : N →L[ℂ] N) _ _ hs
  exact ⟨V, S, hS, hV, hrepr⟩

/-- Every actual phase-gradient eigenspace carries at most the two explicit
unitary phases, represented by an actual orthogonal projection. Zero and
maximal levels are included, with no local or global optimality hypothesis. -/
theorem smoothed_gradient_eigenspace_two_phase_representation
    (tau : ℝ) (htau : 0 < tau) (g : ℝ) (U : unitary (E →L[ℂ] E)) :
    let N := Module.End.eigenspace
      (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ (V : N ≃ₗᵢ[ℂ] N) (S : N →L[ℂ] N), IsStarProjection S ∧
      (∀ x : N, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : N →L[ℂ] N) = smoothedGradientCandidate tau g 1 • 1 +
        (smoothedGradientCandidate tau g (-1) - smoothedGradientCandidate tau g 1) • S := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  let N := Module.End.eigenspace G.toLinearMap (g : ℂ)
  have hinv : ∀ x ∈ N, (U : E →L[ℂ] E) x ∈ N := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change G x = (g : ℂ) • x at hx
    have hc := congrArg (fun A : E →L[ℂ] E => A x)
      (commute_smoothedUnitaryGradient tau (U : E →L[ℂ] E)).eq
    change G ((U : E →L[ℂ] E) x) = (U : E →L[ℂ] E) (G x) at hc
    change G ((U : E →L[ℂ] E) x) = (g : ℂ) • (U : E →L[ℂ] E) x
    rw [hc, hx, map_smul]
  exact two_phase_representation_on_invariant_subspace tau htau g U N hinv
    (fun x hx => Module.End.mem_eigenspace_iff.mp hx)

/-- The zero-gradient kernel carries the actual reflection restriction,
with its negative-phase projection. Empty kernels are allowed. -/
theorem smoothed_gradient_kernel_reflection_representation
    (tau : ℝ) (htau : 0 < tau) (U : unitary (E →L[ℂ] E)) :
    let N := (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap.ker
    ∃ (V : N ≃ₗᵢ[ℂ] N) (S : N →L[ℂ] N),
      IsStarProjection S ∧
      (∀ x : N, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : N →L[ℂ] N) = 1 - (2 : ℂ) • S := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  let N := G.toLinearMap.ker
  have hinv : ∀ x ∈ N, (U : E →L[ℂ] E) x ∈ N := by
    intro x hx
    have hc := congrArg (fun A : E →L[ℂ] E => A x)
      (commute_smoothedUnitaryGradient tau (U : E →L[ℂ] E)).eq
    change G ((U : E →L[ℂ] E) x) = (U : E →L[ℂ] E) (G x) at hc
    change G ((U : E →L[ℂ] E) x) = 0
    rw [hc, show G x = 0 from hx, map_zero]
  obtain ⟨V, S, hS, hV, hrepr⟩ := two_phase_representation_on_invariant_subspace
    tau htau 0 U N hinv (fun x hx => by
      change G x = 0 at hx
      simpa only [Complex.ofReal_zero, zero_smul] using hx)
  refine ⟨V, S, hS, hV, ?_⟩
  calc
    (V : N →L[ℂ] N) = 1 + ((-1 : ℂ) - 1) • S := by
      simpa [smoothedGradientCandidate] using hrepr
    _ = 1 - (2 : ℂ) • S := by module

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
