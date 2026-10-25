/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.LinearAlgebra.Matrix.OrthogonalProjectionFiber
public import ForTauCeti.LinearAlgebra.Matrix.RealOrthogonalTwo

/-!
# The full real four-dimensional transport fiber in cosine--sine coordinates

Every ambient orthogonal transporter of the coordinate source projection
to its cosine--sine target has two planar angle parameters and two
independent determinant signs. Conversely every such choice transports.
This is a parametrization of all ambient competitors, without a condition
that they preserve the individual principal planes. The angles may be
zero, repeated or right angles.

This coordinate reduction is classical. The cost optimization over these
parameters is downstream mathematics, not an assumption of this file.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open _root_.Matrix
open TauCeti.Matrix (planeOrthogonal)

/-- The source projection in two-by-two cosine--sine block coordinates. -/
@[expose] def fourSourceProjection : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  fromBlocks 1 0 0 0

/-- The canonical cosine--sine rotation of two prescribed principal planes. -/
@[expose] def fourCSRotation (theta : Fin 2 → ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  fromBlocks (diagonal (fun i => Real.cos (theta i)))
    (-diagonal (fun i => Real.sin (theta i)))
    (diagonal (fun i => Real.sin (theta i)))
    (diagonal (fun i => Real.cos (theta i)))

/-- All four components of the full orthogonal transport fiber. The two
planar rotations act on the source and complement, and can mix principal
planes. Their signs are independent. -/
@[expose] def fourTransport (theta : Fin 2 → ℝ) (a b e f : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  fourCSRotation theta * fromBlocks (planeOrthogonal a e) 0 0 (planeOrthogonal b f)

theorem transpose_mul_fourCSRotation (theta : Fin 2 → ℝ) :
    (fourCSRotation theta).transpose * fourCSRotation theta = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [fourCSRotation, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.diagonal_apply, Real.sin_sq_add_cos_sq,
      ← pow_two, Real.cos_sq_add_sin_sq] <;> ring

/-- Every signed coordinate choice is an actual ambient orthogonal
transporter, including all degenerate principal-angle cases. -/
theorem fourTransport_mem_fiber (theta : Fin 2 → ℝ) (a b e f : ℝ)
    (he : e ^ 2 = 1) (hf : f ^ 2 = 1) :
    (fourTransport theta a b e f).transpose * fourTransport theta a b e f = 1 ∧
    fourTransport theta a b e f * fourSourceProjection *
        (fourTransport theta a b e f).transpose =
      fourCSRotation theta * fourSourceProjection * (fourCSRotation theta).transpose := by
  let D := fromBlocks (planeOrthogonal a e) 0 0 (planeOrthogonal b f)
  have hD : D.transpose * D = 1 := by
    simp only [D, fromBlocks_transpose, transpose_zero, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      TauCeti.Matrix.transpose_mul_planeOrthogonal a e he,
      TauCeti.Matrix.transpose_mul_planeOrthogonal b f hf, fromBlocks_one]
  have hDP : D * fourSourceProjection * D.transpose = fourSourceProjection := by
    have hA := mul_eq_one_comm.mp
      (TauCeti.Matrix.transpose_mul_planeOrthogonal a e he)
    simp only [D, fourSourceProjection, fromBlocks_transpose, transpose_zero,
      fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
      add_zero, hA]
  constructor
  · change (fourCSRotation theta * D).transpose * (fourCSRotation theta * D) = 1
    simp only [transpose_mul, mul_assoc]
    rw [← mul_assoc (fourCSRotation theta).transpose (fourCSRotation theta) D,
      transpose_mul_fourCSRotation, one_mul, hD]
  · change fourCSRotation theta * D * fourSourceProjection *
        (fourCSRotation theta * D).transpose = _
    calc
      _ = fourCSRotation theta * (D * fourSourceProjection * D.transpose) *
          (fourCSRotation theta).transpose := by rw [transpose_mul]; simp only [mul_assoc]
      _ = _ := by rw [hDP]

/-- The displayed family exhausts **all** ambient real orthogonal
transporters of this source and target. In particular it does not assume
that a competitor respects either principal plane. -/
theorem exists_fourTransport_of_mem_fiber
    (theta : Fin 2 → ℝ) (W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
    (hW : W.transpose * W = 1)
    (htrans : W * fourSourceProjection * W.transpose =
      fourCSRotation theta * fourSourceProjection * (fourCSRotation theta).transpose) :
    ∃ a b e f : ℝ, (e = 1 ∨ e = -1) ∧ (f = 1 ∨ f = -1) ∧
      W = fourTransport theta a b e f := by
  obtain ⟨A, B, hA, hB, hform⟩ :=
    Matrix.exists_orthogonal_blocks_of_conjugate_projection
      (fourCSRotation theta) W (transpose_mul_fourCSRotation theta) hW htrans
  obtain ⟨he, a, ha⟩ := TauCeti.Matrix.exists_planeOrthogonal_of_transpose_mul_eq_one A hA
  obtain ⟨hf, b, hb⟩ := TauCeti.Matrix.exists_planeOrthogonal_of_transpose_mul_eq_one B hB
  exact ⟨a, b, A.det, B.det, he, hf, by simpa only [fourTransport, ← ha, ← hb] using hform⟩

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
