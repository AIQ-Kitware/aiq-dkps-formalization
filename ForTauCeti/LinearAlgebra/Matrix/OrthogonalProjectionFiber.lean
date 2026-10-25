/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Block

/-!
# The orthogonal transport fiber of a coordinate projection

Relative to one specified orthogonal transporter, every other transporter
is block diagonal on the source and its complement. The proof multiplies
the conjugacy identity by the inverse transporter and then reads the two
off-diagonal blocks of its commutation with the coordinate projection.
No rank, field-order or transversality assumptions are used.
-/

public section

namespace Matrix

variable {R n m : Type*} [CommRing R]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- An orthogonal projection fiber is the translate of its full block
orthogonal stabilizer. Empty source or complement blocks are allowed. -/
theorem exists_orthogonal_blocks_of_conjugate_projection
    (U W : Matrix (n ⊕ m) (n ⊕ m) R)
    (hU : U.transpose * U = 1) (hW : W.transpose * W = 1)
    (htrans : W * fromBlocks (1 : Matrix n n R) 0 0 (0 : Matrix m m R) * W.transpose =
      U * fromBlocks (1 : Matrix n n R) 0 0 (0 : Matrix m m R) * U.transpose) :
    ∃ A : Matrix n n R, ∃ B : Matrix m m R,
      A.transpose * A = 1 ∧ B.transpose * B = 1 ∧
      W = U * fromBlocks A 0 0 B := by
  let P := fromBlocks (1 : Matrix n n R) 0 0 (0 : Matrix m m R)
  let M := U.transpose * W
  have hUU : U * U.transpose = 1 := mul_eq_one_comm.mp hU
  have hMM : M.transpose * M = 1 := by
    simp only [M, transpose_mul, transpose_transpose, mul_assoc]
    rw [← mul_assoc U U.transpose W, hUU, one_mul, hW]
  have hconj : M * P * M.transpose = P := by
    calc
      _ = U.transpose * (W * P * W.transpose) * U := by
        simp only [M, transpose_mul, transpose_transpose, mul_assoc]
      _ = U.transpose * (U * P * U.transpose) * U := by rw [htrans]
      _ = P := by simp only [← mul_assoc, hU, one_mul]; rw [mul_assoc, hU, mul_one]
  have hcomm : M * P = P * M := by
    have hh := congrArg (fun N => N * M) hconj
    simpa only [mul_assoc, hMM, mul_one] using hh
  have hblocks : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    rw [← fromBlocks_toBlocks M] at hcomm
    simp only [P, fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, fromBlocks_inj] at hcomm
    exact (fromBlocks_toBlocks M).symm.trans (by rw [hcomm.2.1, hcomm.2.2.1])
  have hdiag := hMM
  rw [hblocks, fromBlocks_transpose, fromBlocks_multiply,
    ← fromBlocks_one] at hdiag
  simp only [transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    fromBlocks_inj] at hdiag
  refine ⟨M.toBlocks₁₁, M.toBlocks₂₂, hdiag.1, hdiag.2.2.2, ?_⟩
  rw [← hblocks]
  simp only [M, ← mul_assoc, hUU, one_mul]

end Matrix
