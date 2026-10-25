/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Coordinates for both components of the real orthogonal group in dimension two

The first column determines its angle, and the determinant determines the
second column. The proof uses the complex argument of the unit first column,
so it never divides by an individual coordinate. This includes the axis
rotations and reflections needed in degenerate transport blocks.
-/

public section

noncomputable section

namespace TauCeti.Matrix

/-- A planar rotation followed by the coordinate reflection when `e = -1`.
For `e = 1` this is the usual rotation. -/
@[expose] def planeOrthogonal (t e : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, -e * Real.sin t; Real.sin t, e * Real.cos t]

@[simp]
theorem det_planeOrthogonal (t e : ℝ) : (planeOrthogonal t e).det = e := by
  rw [planeOrthogonal, Matrix.det_fin_two_of]
  linear_combination e * Real.sin_sq_add_cos_sq t

/-- Both determinant signs give orthogonal matrices. This verifies the
attaining coordinate families without assuming a nonzero sine or cosine. -/
theorem transpose_mul_planeOrthogonal (t e : ℝ) (he : e ^ 2 = 1) :
    (planeOrthogonal t e).transpose * planeOrthogonal t e = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeOrthogonal, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- The cosine endpoint determines the actual matrix, without choosing a
representative modulo `2*pi`. -/
theorem planeOrthogonal_eq_at_zero_of_cos_eq_one (t e : ℝ) (ht : Real.cos t = 1) :
    planeOrthogonal t e = planeOrthogonal 0 e := by
  have hs : Real.sin t = 0 := by nlinarith [Real.sin_sq_add_cos_sq t]
  simp [planeOrthogonal, ht, hs]

/-- The other cosine endpoint likewise determines the actual matrix. -/
theorem planeOrthogonal_eq_at_pi_of_cos_eq_neg_one (t e : ℝ) (ht : Real.cos t = -1) :
    planeOrthogonal t e = planeOrthogonal Real.pi e := by
  have hs : Real.sin t = 0 := by nlinarith [Real.sin_sq_add_cos_sq t]
  simp [planeOrthogonal, ht, hs]

/-- Every real orthogonal two-by-two matrix has the rotation/reflection
coordinates above, with its actual determinant as the sign. No component
or exceptional first-column case is discarded. -/
theorem exists_planeOrthogonal_of_transpose_mul_eq_one
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.transpose * A = 1) :
    (A.det = 1 ∨ A.det = -1) ∧ ∃ t : ℝ, A = planeOrthogonal t A.det := by
  have hcol := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hA
  have hdot := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hA
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at hcol hdot
  have he : A.det ^ 2 = 1 := by
    have hdet := congrArg Matrix.det hA
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two] using hdet
  have hsign : A.det = 1 ∨ A.det = -1 := by
    rcases mul_eq_zero.mp (show (A.det - 1) * (A.det + 1) = 0 by nlinarith [he]) with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  let z : ℂ := ⟨A 0 0, A 1 0⟩
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    change Real.sqrt (A 0 0 ^ 2 + A 1 0 ^ 2) = 1
    rw [show A 0 0 ^ 2 + A 1 0 ^ 2 = 1 by nlinarith [hcol], Real.sqrt_one]
  have hz0 : z ≠ 0 := by
    intro hz0
    simp only [hz0, norm_zero, zero_ne_one] at hz
  have hc : Real.cos z.arg = A 0 0 := by rw [Complex.cos_arg hz0, hz, div_one]
  have hs : Real.sin z.arg = A 1 0 := by rw [Complex.sin_arg, hz, div_one]
  have h11 : A.det * A 0 0 = A 1 1 := by
    rw [Matrix.det_fin_two]
    linear_combination A 1 1 * hcol - A 1 0 * hdot
  have h01 : -A.det * A 1 0 = A 0 1 := by
    rw [Matrix.det_fin_two]
    linear_combination A 0 1 * hcol - A 0 0 * hdot
  refine ⟨hsign, z.arg, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeOrthogonal, hc, hs, h11, h01]

end TauCeti.Matrix
