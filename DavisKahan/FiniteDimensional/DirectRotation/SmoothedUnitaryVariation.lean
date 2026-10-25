/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSpectralCost
public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierSpectralTrace
public import ForTauCeti.Analysis.InnerProductSpace.UnitarySpectralVariation

/-!
# Actual first variations of Charbonnier displacement

The literal singular-value objective has a self-adjoint phase gradient
along every Hermitian exponential variation. The proof differentiates
the normal spectral trace, so eigenvalue collisions and zero displacement
singular values need no exclusions.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped ComplexConjugate

/-- The scalar phase derivative in an argument-free form. -/
@[expose] def smoothedPhaseDerivative (tau : ℝ) (z : ℂ) : ℝ :=
  (conj (charbonnierDisplacementGradient tau z) * (Complex.I * z)).re

/-- The phase derivative is the imaginary coordinate divided by the
positive smoothed displacement radius. -/
theorem smoothedPhaseDerivative_eq (tau : ℝ) (z : ℂ) :
    smoothedPhaseDerivative tau z = z.im / Real.sqrt (tau ^ 2 + ‖z - 1‖ ^ 2) := by
  simp only [smoothedPhaseDerivative, charbonnierDisplacementGradient,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, div_eq_mul_inv]
  ring

/-- Zero phase gradient on the unit circle means eigenvalue `1` or `-1`. -/
theorem smoothedPhaseDerivative_eq_zero_iff_of_norm_eq_one
    (tau : ℝ) (htau : 0 < tau) (z : ℂ) (hz : ‖z‖ = 1) :
    smoothedPhaseDerivative tau z = 0 ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hzero
    rw [smoothedPhaseDerivative_eq] at hzero
    have him : z.im = 0 := (div_eq_zero_iff.mp hzero).resolve_right
      (charbonnier_radius_pos tau htau z).ne'
    have hsquare : z.re ^ 2 = 1 := by
      have h := Complex.normSq_eq_norm_sq z
      rw [hz, one_pow, Complex.normSq_apply, him] at h
      nlinarith
    rcases sq_eq_one_iff.mp hsquare with hre | hre
    · exact Or.inl (Complex.ext hre him)
    · exact Or.inr (Complex.ext (by simpa using hre) (by simpa using him))
  · rintro (rfl | rfl) <;> simp [smoothedPhaseDerivative_eq]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The actual Charbonnier unitary phase gradient. -/
@[expose] def smoothedUnitaryGradient (tau : ℝ) (U : E →L[ℂ] E) : E →L[ℂ] E :=
  unitaryPhaseGradient (charbonnierDisplacementGradient tau) U

omit [FiniteDimensional ℂ E] in
/-- The phase gradient is self-adjoint. -/
theorem isSelfAdjoint_smoothedUnitaryGradient (tau : ℝ) (U : E →L[ℂ] E) :
    IsSelfAdjoint (smoothedUnitaryGradient tau U) :=
  isSelfAdjoint_unitaryPhaseGradient _ _

omit [FiniteDimensional ℂ E] in
/-- The phase gradient commutes with the underlying normal operator. -/
theorem commute_smoothedUnitaryGradient
    (tau : ℝ) (U : E →L[ℂ] E) [IsStarNormal U] :
    Commute (smoothedUnitaryGradient tau U) U :=
  commute_unitaryPhaseGradient _ _

/-- Eigenvectors of the transporter have the scalar phase gradient. -/
theorem smoothedUnitaryGradient_apply_of_apply_eq_smul
    (tau : ℝ) (U : E →L[ℂ] E) [IsStarNormal U] (x : E) (mu : ℂ)
    (hx : U x = mu • x) :
    smoothedUnitaryGradient tau U x = (smoothedPhaseDerivative tau mu : ℂ) • x :=
  ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ hx

/-- The literal singular-value Charbonnier cost is a normal spectral trace. -/
theorem smoothedDisplacementCost_eq_re_trace_cfc
    (tau : ℝ) (W : E →L[ℂ] E) [IsStarNormal W] :
    smoothedDisplacementCost tau W.toLinearMap =
      (LinearMap.trace ℂ E
        (cfc (fun z => (charbonnierDisplacementSymbol tau z : ℂ)) W).toLinearMap).re := by
  let := ContinuousLinearMap.isStarNormal_toLinearMap W
  obtain ⟨e, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal W.toLinearMap
      (ι := Fin (Module.finrank ℂ E)) (by simp)
  have hD (i) : ((LinearMap.id : E →ₗ[ℂ] E) - W.toLinearMap) (e i) =
      (1 - mu i) • e i := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, hmu, sub_smul, one_smul]
  rw [smoothedDisplacementCost, sum_singularValues_eq_sum_norm_eigenvalues e _ _ hD
    (fun s : ℝ => Real.sqrt (tau ^ 2 + s ^ 2) - tau),
    ContinuousLinearMap.re_trace_cfc_eq_sum (charbonnierDisplacementSymbol tau) W e mu hmu]
  apply Finset.sum_congr rfl
  intro i _
  simp only [charbonnierDisplacementSymbol, norm_sub_rev]

/-- Every Hermitian right variation has the actual Charbonnier phase-gradient
derivative at every time, including at zero displacement. -/
theorem hasDerivAt_smoothed_unitary_right_variation_at
    (tau : ℝ) (htau : 0 < tau)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => smoothedDisplacementCost tau
        ((U : E →L[ℂ] E) * NormedSpace.exp (s • (Complex.I • H))).toLinearMap)
      (LinearMap.trace ℂ E
        (smoothedUnitaryGradient tau ((U : E →L[ℂ] E) *
          NormedSpace.exp (t • (Complex.I • H))) * H).toLinearMap).re t := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  have hd := hasDerivAt_unitary_spectral_right_variation_at
    (charbonnierDisplacementSymbol tau) (charbonnierDisplacementGradient tau)
    (continuous_charbonnierDisplacementGradient tau htau).continuousOn
    (fun z _ w _ => charbonnierDisplacement_support tau htau z w) U H hH t
  apply hd.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro s
  have hu : (U : E →L[ℂ] E) * NormedSpace.exp (s • (Complex.I • H)) ∈
      unitary (E →L[ℂ] E) := by
    apply mul_mem U.2
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  let := isStarNormal_of_mem_unitary hu
  exact smoothedDisplacementCost_eq_re_trace_cfc tau _

/-- The first variation at the initial unitary. -/
theorem hasDerivAt_smoothed_unitary_right_variation
    (tau : ℝ) (htau : 0 < tau)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) :
    HasDerivAt
      (fun t : ℝ => smoothedDisplacementCost tau
        ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))).toLinearMap)
      (LinearMap.trace ℂ E
        (smoothedUnitaryGradient tau (U : E →L[ℂ] E) * H).toLinearMap).re 0 := by
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one] using
    hasDerivAt_smoothed_unitary_right_variation_at tau htau U H hH 0

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
