/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator
public import ForTauCeti.Analysis.InnerProductSpace.Positive.SquareRoot.Eigenspace
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Principal sines of reflection-paired unitary eigenvectors

Suppose a source reflection exchanges two eigenvectors of a transporter,
whose eigenphases are `alpha` and `-beta`. The sine angle operator acts on
both vectors by the sine of their mean phase, when that mean is in the
principal-angle interval.

The proof computes the projection difference on the two vectors. Its two
off-diagonal coefficients are conjugates with norm equal to the claimed
principal sine. Squaring and using positivity of the sine operator gives
the eigenvector equations. No nonzero or orthogonality assumption on the
vector is needed; those enter only when assembling a basis.

This is classical two-projection geometry used to identify the angles in
the finite Schatten transport decomposition.
-/

public section

noncomputable section

namespace Submodule

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem symm_apply_of_phase_eigenvector (U : E ≃ₗᵢ[ℂ] E) (v : E)
    (lam : ℂ) (hlam : ‖lam‖ = 1) (hU : U v = lam • v) :
    U.symm v = star lam • v := by
  apply U.injective
  rw [U.apply_symm_apply, map_smul, hU, smul_smul]
  have hprod : star lam * lam = 1 := by
    change (starRingEnd ℂ) lam * lam = 1
    rw [RCLike.conj_mul, hlam]
    norm_num
  rw [hprod, one_smul]

omit [CompleteSpace E] in
private theorem projectionDifference_apply_paired_eigenvector
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (v : E) (lam nu : ℂ) (hlam : ‖lam‖ = 1)
    (hUv : U v = lam • v) (hUJv : U (K.reflection v) = nu • K.reflection v) :
    (K.starProjection - L.starProjection) v =
      ((1 / 2 : ℂ) * (1 - star lam * nu)) • K.reflection v := by
  have hP (x : E) : K.starProjection x = (1 / 2 : ℂ) • (x + K.reflection x) := by
    rw [reflection_apply]
    module
  have hinv := symm_apply_of_phase_eigenvector U v lam hlam hUv
  have hQbase : L.starProjection v = U (K.starProjection (U.symm v)) := by
    simpa only [hmap] using starProjection_map_apply U K v
  have hQ : L.starProjection v =
      (1 / 2 : ℂ) • (v + (star lam * nu) • K.reflection v) := by
    rw [hQbase, hP, map_smul, map_add, U.apply_symm_apply,
      hinv, map_smul, map_smul, hUJv, smul_smul]
  change K.starProjection v - L.starProjection v = _
  rw [hP, hQ]
  module

/-- The mean of two reflection-paired transporter eigenphases is a physical
principal angle: the sine angle operator acts on both paired vectors by its
sine. This includes zero and right angles. -/
theorem sinAngleOperator_apply_of_paired_phase_eigenvectors
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (v : E) (alpha beta : ℝ)
    (hUv : U v = Complex.exp ((alpha : ℂ) * Complex.I) • v)
    (hUJv : U (K.reflection v) =
      Complex.exp (((-beta : ℝ) : ℂ) * Complex.I) • K.reflection v)
    (hmean : (alpha + beta) / 2 ∈ Set.Icc 0 (Real.pi / 2)) :
    K.sinAngleOperator L v = (Real.sin ((alpha + beta) / 2) : ℂ) • v ∧
      K.sinAngleOperator L (K.reflection v) =
        (Real.sin ((alpha + beta) / 2) : ℂ) • K.reflection v := by
  let lam := Complex.exp ((alpha : ℂ) * Complex.I)
  let nu := Complex.exp (((-beta : ℝ) : ℂ) * Complex.I)
  let c := (1 / 2 : ℂ) * (1 - star lam * nu)
  let d := (1 / 2 : ℂ) * (1 - star nu * lam)
  have hlam : ‖lam‖ = 1 := Complex.norm_exp_ofReal_mul_I alpha
  have hnu : ‖nu‖ = 1 := Complex.norm_exp_ofReal_mul_I (-beta)
  have hD0 : (K.starProjection - L.starProjection) v = c • K.reflection v :=
    projectionDifference_apply_paired_eigenvector K L U hmap v lam nu hlam hUv hUJv
  have hD1 : (K.starProjection - L.starProjection) (K.reflection v) = d • v := by
    simpa only [K.reflection_reflection] using
      projectionDifference_apply_paired_eigenvector K L U hmap (K.reflection v) nu lam hnu
        hUJv (by simpa only [K.reflection_reflection] using hUv)
  have hstar : star c = d := by
    dsimp only [c, d]
    simp only [star_mul, star_sub, star_one, star_star]
    norm_num
    ring
  have hphase : star lam * nu = Complex.exp (((-(alpha + beta) : ℝ) : ℂ) * Complex.I) := by
    change (starRingEnd ℂ) (Complex.exp ((alpha : ℂ) * Complex.I)) *
      Complex.exp (((-beta : ℝ) : ℂ) * Complex.I) = _
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg,
      Complex.ofReal_add]
    ring
  have hs : 0 ≤ Real.sin ((alpha + beta) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hmean.1 (by linarith [hmean.2, Real.pi_pos])
  have hchord : ‖1 - star lam * nu‖ = 2 * Real.sin ((alpha + beta) / 2) := by
    rw [hphase, norm_sub_rev, mul_comm (((-(alpha + beta) : ℝ) : ℂ)) Complex.I,
      Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
      show -(alpha + beta) / 2 = -((alpha + beta) / 2) by ring,
      Real.sin_neg, mul_neg, abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) hs)]
  have hnorm : ‖c‖ = Real.sin ((alpha + beta) / 2) := by
    dsimp only [c]
    rw [norm_mul, norm_div, norm_one, RCLike.norm_ofNat, hchord]
    ring
  have hprod : c * d = (Real.sin ((alpha + beta) / 2) : ℂ) *
      (Real.sin ((alpha + beta) / 2) : ℂ) := by
    rw [← hstar]
    change c * (starRingEnd ℂ) c = _
    rw [RCLike.mul_conj, hnorm]
    rw [pow_two]
    rfl
  let S := K.sinAngleOperator L
  let D := K.starProjection - L.starProjection
  have hsq : S * S = D * D := by
    simpa only [sq] using K.sinAngleOperator_sq L
  have hS : S.toLinearMap.IsPositive := (K.isPositive_sinAngleOperator L).toLinearMap
  constructor
  · apply hS.apply_eq_smul_of_apply_apply_eq_smul hs
    have h := congrArg (fun T : E →L[ℂ] E => T v) hsq
    change S (S v) = D (D v) at h
    rw [hD0, map_smul, hD1, smul_smul, hprod] at h
    exact h
  · apply hS.apply_eq_smul_of_apply_apply_eq_smul hs
    have h := congrArg (fun T : E →L[ℂ] E => T (K.reflection v)) hsq
    change S (S (K.reflection v)) = D (D (K.reflection v)) at h
    rw [hD1, map_smul, hD0, smul_smul, mul_comm d c, hprod] at h
    exact h

end Submodule
