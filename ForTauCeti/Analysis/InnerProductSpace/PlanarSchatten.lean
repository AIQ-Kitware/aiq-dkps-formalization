/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus
public import Mathlib.LinearAlgebra.Determinant

/-!
# Planar normal displacement from trace and determinant

The trace and determinant recover a normal operator's two eigenvalues
as an unordered pair. This computes the actual Schatten displacement
power without choosing eigenvectors or ordering its singular values.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The Schatten displacement of a two-dimensional normal operator is
the sum of its two eigenvalue chord powers, as identified by trace and
determinant. No distinctness or nonzero displacement assumption is needed. -/
theorem schatten_displacement_rpow_eq_of_trace_det_fin_two
    (T : E →L[ℂ] E) [IsStarNormal T] (hE : Module.finrank ℂ E = 2)
    (a b : ℂ) (htrace : LinearMap.trace ℂ E T.toLinearMap = a + b)
    (hdet : LinearMap.det T.toLinearMap = a * b)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - T.toLinearMap) ^ p.toReal =
      ‖1 - a‖ ^ p.toReal + ‖1 - b‖ ^ p.toReal := by
  let := ContinuousLinearMap.isStarNormal_toLinearMap T
  obtain ⟨e, mu, he⟩ :=
    T.toLinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal
      (ι := Fin 2) (by simpa using hE.symm)
  have hdiag : T.toLinearMap = Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal mu) := by
    apply e.toBasis.ext
    intro i
    simpa [Matrix.toLin_self, Matrix.diagonal_apply] using he i
  have hsum : mu 0 + mu 1 = a + b := by
    simpa only [hdiag, Matrix.trace_toLin_eq, Matrix.trace_diagonal, Fin.sum_univ_two]
      using htrace
  have hprod : mu 0 * mu 1 = a * b := by
    simpa only [hdiag, LinearMap.det_toLin, Matrix.det_diagonal, Fin.prod_univ_two] using hdet
  have hroots : (mu 0 = a ∧ mu 1 = b) ∨ (mu 0 = b ∧ mu 1 = a) := by
    have hfactor : (mu 0 - a) * (mu 0 - b) = 0 := by
      calc
        _ = mu 0 * (mu 0 + mu 1 - (a + b)) + (a * b - mu 0 * mu 1) := by ring
        _ = 0 := by rw [hsum, hprod, sub_self, sub_self, mul_zero, add_zero]
    rcases mul_eq_zero.mp hfactor with ha | hb
    · left
      refine ⟨sub_eq_zero.mp ha, ?_⟩
      rw [sub_eq_zero.mp ha] at hsum
      exact add_left_cancel hsum
    · right
      refine ⟨sub_eq_zero.mp hb, ?_⟩
      rw [sub_eq_zero.mp hb, add_comm a b] at hsum
      exact add_left_cancel hsum
  have hdisp (i : Fin 2) : ((LinearMap.id : E →ₗ[ℂ] E) - T.toLinearMap) (e i) =
      (1 - mu i) • e i := by
    change e i - T.toLinearMap (e i) = _
    rw [he, sub_smul, one_smul]
  rw [schatten_rpow_eq_sum_norm_eigenvalues e _ _ hdisp p hp, Fin.sum_univ_two]
  rcases hroots with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, add_comm]

end TauCeti
