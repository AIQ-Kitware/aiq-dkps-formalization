/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI GPT-5.6 Sol, Jon Crall
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.Sharpness
import DavisKahan.Sources.DavisKahan1970.Ideals.RankOneNormalization

/-!
# Davis--Kahan 1970, Example 6.1

The worked example preceding Theorem 6.3 proves that the one-sided spectral
placement in the `tan Theta` theorem is essential.  With gap `delta = 1`, the
directed tangent has every normalized unitary-invariant norm equal to `1`,
whereas the residual has norm `1 / sqrt 2`.

This module records the source's explicit spectral block and its norm failure.
The norm calculation is stated for the paper's complete normalized
unitary-invariant norm class, not only for one selected Schatten/Ky Fan norm.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section6Example61

open scoped InnerProductSpace ENNReal

noncomputable section

open TauCeti.DavisKahan.ExactSinTheta

/-! ## The literal three-dimensional model from the paper -/

/-- The ambient coordinate space of Example 6.1: one trial coordinate followed
by the two complementary coordinates. -/
abbrev Example61Ambient := EuclideanSpace ℝ (Fin 3)

/-- The constant `1 / √2` of Example 6.1, named so the example's arithmetic
reads as the paper's. -/
def example61InvSqrtTwo : ℝ := 1 / Real.sqrt 2

private theorem example61InvSqrtTwo_sq :
    example61InvSqrtTwo * example61InvSqrtTwo = (1 / 2 : ℝ) := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [example61InvSqrtTwo]
  field_simp [ne_of_gt hsqrt2]
  nlinarith

/-- The unperturbed `A` from Example 6.1.  Its first block is
`A₀ = 0` and its complementary block is the source's
`A₁ = [[0,1/√2],[1/√2,0]]`. -/
def example61AMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0;
     0, 0, example61InvSqrtTwo;
     0, example61InvSqrtTwo, 0]

/-- The perturbation `H` from Example 6.1.  It has `H₀ = H₁ = 0` and the
single off-diagonal residual row `B* = (0,1/√2)`. -/
def example61HMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, example61InvSqrtTwo;
     0, 0, 0;
     example61InvSqrtTwo, 0, 0]

/-- The source matrix of `A + H` in the `E₀ ⊕ E₁` coordinates.  Reading it
in blocks gives exactly
`A₀ + H₀ = 0`, `B* = (0, 1/√2)`, and
`A₁ + H₁ = [[0,1/√2],[1/√2,0]]`. -/
def example61SourceMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, example61InvSqrtTwo;
     0, 0, example61InvSqrtTwo;
     example61InvSqrtTwo, example61InvSqrtTwo, 0]

/-- The displayed `A + H` is literally the sum of the two source
blocks just defined. -/
theorem example6_1_sourceMatrix_eq_A_add_H :
    example61SourceMatrix = example61AMatrix + example61HMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [example61SourceMatrix, example61AMatrix, example61HMatrix]

/-- The paper's direct rotation assembled from
`C₀ = 1/√2`, `S₀* = (-1/√2,0)`, and `C₁ = diag(1/√2,1)`.
With the block convention `(C₀,-S₁; S₀,C₁)` this is the displayed matrix. -/
def example61DirectRotationMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![example61InvSqrtTwo, example61InvSqrtTwo, 0;
     -example61InvSqrtTwo, example61InvSqrtTwo, 0;
     0, 0, 1]

/-- The transpose/inverse of the paper's direct rotation. -/
def example61DirectRotationInvMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![example61InvSqrtTwo, -example61InvSqrtTwo, 0;
     example61InvSqrtTwo, example61InvSqrtTwo, 0;
     0, 0, 1]

/-- The source's diagonalized matrix `diag(Λ₀,Λ₁)`, with `Λ₀ = 0` and
`Λ₁ = [[0,1],[1,0]]`. -/
def example61DiagonalizedMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0;
     0, 0, 1;
     0, 1, 0]

/-- `A + H` as an operator on the literal source coordinates. -/
def example61SourceOperator : Example61Ambient →ₗ[ℝ] Example61Ambient :=
  Matrix.toEuclideanLin example61SourceMatrix

/-- The paper's direct rotation as an operator. -/
def example61DirectRotation : Example61Ambient →ₗ[ℝ] Example61Ambient :=
  Matrix.toEuclideanLin example61DirectRotationMatrix

/-- The inverse direct rotation as an operator. -/
def example61DirectRotationInv : Example61Ambient →ₗ[ℝ] Example61Ambient :=
  Matrix.toEuclideanLin example61DirectRotationInvMatrix

/-- The paper's diagonalized operator. -/
def example61Diagonalized : Example61Ambient →ₗ[ℝ] Example61Ambient :=
  Matrix.toEuclideanLin example61DiagonalizedMatrix

private theorem example61_matrix_apply
    (M : Matrix (Fin 3) (Fin 3) ℝ) (x : Example61Ambient) (i : Fin 3) :
    Matrix.toEuclideanLin M x i = ∑ j, M i j * x j := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- Coordinate form of the source's block data.  This is the literal
`A₀+H₀`, `B*`, `B`, and `A₁+H₁` calculation in Example 6.1. -/
theorem example6_1_source_block_coordinates (x : Example61Ambient) :
    example61SourceOperator x 0 = example61InvSqrtTwo * x 2 ∧
    example61SourceOperator x 1 = example61InvSqrtTwo * x 2 ∧
    example61SourceOperator x 2 =
      example61InvSqrtTwo * x 0 + example61InvSqrtTwo * x 1 := by
  constructor
  · rw [example61SourceOperator, example61_matrix_apply]
    simp [example61SourceMatrix, Fin.sum_univ_three]
  constructor
  · rw [example61SourceOperator, example61_matrix_apply]
    simp [example61SourceMatrix, Fin.sum_univ_three]
  · rw [example61SourceOperator, example61_matrix_apply]
    simp [example61SourceMatrix, Fin.sum_univ_three]

/-- Coordinate form of the direct-rotation blocks quoted by the source. -/
theorem example6_1_directRotation_block_coordinates (x : Example61Ambient) :
    example61DirectRotation x 0 =
        example61InvSqrtTwo * x 0 + example61InvSqrtTwo * x 1 ∧
    example61DirectRotation x 1 =
        -example61InvSqrtTwo * x 0 + example61InvSqrtTwo * x 1 ∧
    example61DirectRotation x 2 = x 2 := by
  constructor
  · rw [example61DirectRotation, example61_matrix_apply]
    simp [example61DirectRotationMatrix, Fin.sum_univ_three]
  constructor
  · rw [example61DirectRotation, example61_matrix_apply]
    simp [example61DirectRotationMatrix, Fin.sum_univ_three]
  · rw [example61DirectRotation, example61_matrix_apply]
    simp [example61DirectRotationMatrix, Fin.sum_univ_three]

/-- The displayed inverse matrix is the transpose of the direct rotation. -/
theorem example6_1_directRotationInvMatrix_eq_transpose :
    example61DirectRotationInvMatrix = example61DirectRotationMatrix.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [example61DirectRotationInvMatrix, example61DirectRotationMatrix,
      Matrix.transpose_apply]

/-- The quoted direct rotation is genuinely orthogonal: its displayed
transpose is a left inverse. -/
theorem example6_1_directRotationInvMatrix_mul_directRotationMatrix :
    example61DirectRotationInvMatrix * example61DirectRotationMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [example61DirectRotationInvMatrix, example61DirectRotationMatrix,
      Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [example61InvSqrtTwo_sq]

/-- The displayed transpose is also a right inverse. -/
theorem example6_1_directRotationMatrix_mul_directRotationInvMatrix :
    example61DirectRotationMatrix * example61DirectRotationInvMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [example61DirectRotationInvMatrix, example61DirectRotationMatrix,
      Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [example61InvSqrtTwo_sq]

/-- The explicit direct rotation diagonalizes the source matrix exactly as
claimed in Example 6.1:
`V* (A+H) V = diag(0, [[0,1],[1,0]])`. -/
theorem example6_1_directRotation_diagonalizes :
    example61DirectRotationInvMatrix * example61SourceMatrix *
        example61DirectRotationMatrix = example61DiagonalizedMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [example61DirectRotationInvMatrix, example61SourceMatrix,
      example61DirectRotationMatrix, example61DiagonalizedMatrix,
      Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [example61InvSqrtTwo_sq]

/-- The source's `Lambda_1 = [[0,1],[1,0]]`; its spectrum straddles
`Lambda_0 = 0`. -/
def example61LambdaOne : PaperPlane ℂ →ₗ[ℂ] PaperPlane ℂ :=
  Matrix.toEuclideanLin !![(0 : ℂ), 1; 1, 0]

/-- `+1` is an eigenvalue of the source's right spectral block. -/
theorem example6_1_lambdaOne_eigenvalue_pos :
    example61LambdaOne (paperPlaneE0 + paperPlaneE1) =
      paperPlaneE0 + paperPlaneE1 := by
  ext i
  fin_cases i <;>
    simp [example61LambdaOne, paperPlaneE0, paperPlaneE1,
      Matrix.toLpLin_apply]

/-- `-1` is an eigenvalue of the source's right spectral block. -/
theorem example6_1_lambdaOne_eigenvalue_neg :
    example61LambdaOne (paperPlaneE0 - paperPlaneE1) =
      -(paperPlaneE0 - paperPlaneE1) := by
  ext i
  fin_cases i <;>
    simp [example61LambdaOne, paperPlaneE0, paperPlaneE1,
      Matrix.toLpLin_apply]

/-- The complementary source block really has spectral mass on both sides of
`Λ₀ = 0`; the displayed eigenvectors are nonzero. -/
theorem example6_1_lambdaOne_spectrum_straddles_zero :
    (∃ x : PaperPlane ℂ, x ≠ 0 ∧ example61LambdaOne x = x) ∧
      (∃ y : PaperPlane ℂ, y ≠ 0 ∧ example61LambdaOne y = -y) := by
  have hplus : paperPlaneE0 + paperPlaneE1 ≠ (0 : PaperPlane ℂ) := by
    intro h
    have h0 := congrArg (fun x : PaperPlane ℂ => x 0) h
    simp [paperPlaneE0, paperPlaneE1] at h0
  have hminus : paperPlaneE0 - paperPlaneE1 ≠ (0 : PaperPlane ℂ) := by
    intro h
    have h0 := congrArg (fun x : PaperPlane ℂ => x 0) h
    simp [paperPlaneE0, paperPlaneE1] at h0
  exact ⟨⟨_, hplus, example6_1_lambdaOne_eigenvalue_pos⟩,
    ⟨_, hminus, example6_1_lambdaOne_eigenvalue_neg⟩⟩

/-- A rank-one singular-value representative of the paper's positive
`tan Θ₀`.  The literal one-dimensional `tan Θ₀` is the scalar `1`; this column
has the same sole singular value, so every source unitary-invariant norm sees
exactly the same quantity. -/
def example61Tangent : ℂ →L[ℂ] PaperPlane ℂ :=
  paperPlanarComplementMap

/-- A singular-value representative of the source residual row
`B* = (0,1/sqrt 2)`, represented by its adjoint rank-one column.  Unitary-
invariant norms are unchanged by taking adjoints. -/
def example61Residual : ℂ →L[ℂ] PaperPlane ℂ :=
  (((1 / Real.sqrt 2 : ℝ) : ℂ) • paperPlanarComplementMap)

/-- The tangent block has source norm exactly one for every normalized
unitary-invariant norm. -/
theorem example6_1_tangent_gauge
    (N : PaperUnitaryInvariantNorm) :
    N.gauge example61Tangent = 1 := by
  have hV := paperPlanarComplementMap_norm_rank (𝕜 := ℂ)
  exact N.gauge_rankOne hV.1 hV.2

/-- The residual block has source norm exactly `1/sqrt 2` for every normalized
unitary-invariant norm. -/
theorem example6_1_residual_gauge
    (N : PaperUnitaryInvariantNorm) :
    N.gauge example61Residual = 1 / Real.sqrt 2 := by
  have hV := paperPlanarComplementMap_norm_rank (𝕜 := ℂ)
  have hmem := N.mem_rankOne hV.1 hV.2
  rw [example61Residual, N.gauge_smul _ hmem, N.gauge_rankOne hV.1 hV.2,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- `1/sqrt 2 < 1`, the strict scalar inequality behind Example 6.1. -/
theorem example6_1_one_div_sqrt_two_lt_one :
    1 / Real.sqrt 2 < (1 : ℝ) := by
  have hsqrt : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  exact (div_lt_one (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))).2 hsqrt

/-- **Davis--Kahan 1970, Example 6.1.**  With the paper's `delta = 1`, the
conclusion `delta * ||tan Theta_0|| <= ||R||` fails for every normalized
unitary-invariant norm: the two sides are `1` and `1/sqrt 2`.

The preceding two eigenvector declarations certify the omitted hypothesis:
`Lambda_1` has spectral mass on both sides of `Lambda_0 = 0`. -/
theorem example6_1_tanTheta_conclusion_fails_every_norm
    (N : PaperUnitaryInvariantNorm) :
    N.gauge example61Residual <
      1 * N.gauge example61Tangent := by
  rw [example6_1_residual_gauge, example6_1_tangent_gauge, one_mul]
  exact example6_1_one_div_sqrt_two_lt_one

end

end Section6Example61
end DavisKahan1970
end TauCeti
