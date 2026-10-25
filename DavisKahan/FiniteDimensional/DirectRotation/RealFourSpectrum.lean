/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealFourCoordinates
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Characteristic polynomials of all real four-dimensional transport components

The coordinate family exhausts the ambient transport fiber. Its quartic
characteristic polynomial is computed with both independent determinant
signs retained. The determinant-negative components factor into the fixed
eigenvalues `1,-1` and a reciprocal quadratic; the determinant-positive
components give the phase rectangles used in the two-angle minimum.

The only coordinate calculation is a determinant pencil identity proved
from four unit-circle equations. It remains valid when phases coalesce or
displacement singular values vanish.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open _root_.Matrix Polynomial

/-- The full transport matrix in the ordered coordinates
`(source₁, source₂, complement₁, complement₂)`. -/
@[expose] def fourTransportMatrix (t u a b e f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![Real.cos t * Real.cos a, -e * Real.cos t * Real.sin a,
      -Real.sin t * Real.cos b, f * Real.sin t * Real.sin b;
    Real.cos u * Real.sin a, e * Real.cos u * Real.cos a,
      -Real.sin u * Real.sin b, -f * Real.sin u * Real.cos b;
    Real.sin t * Real.cos a, -e * Real.sin t * Real.sin a,
      Real.cos t * Real.cos b, -f * Real.cos t * Real.sin b;
    Real.sin u * Real.sin a, e * Real.sin u * Real.cos a,
      Real.cos u * Real.sin b, f * Real.cos u * Real.cos b]

/-- The literal matrix is exactly the full-fiber family in the coordinate
order used for its characteristic polynomial. -/
theorem fourTransportMatrix_submatrix (t u a b e f : ℝ) :
    (fourTransportMatrix t u a b e f).submatrix finSumFinEquiv finSumFinEquiv =
      fourTransport ![t, u] a b e f := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [fourTransportMatrix, fourTransport, fourCSRotation,
      TauCeti.Matrix.planeOrthogonal, Matrix.submatrix_apply,
      Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.diagonal_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] <;> ring

/-- Orthogonality of the literal matrix follows from the full-fiber
construction, through the exact coordinate permutation. -/
theorem transpose_mul_fourTransportMatrix (t u a b e f : ℝ)
    (he : e ^ 2 = 1) (hf : f ^ 2 = 1) :
    (fourTransportMatrix t u a b e f).transpose * fourTransportMatrix t u a b e f = 1 := by
  let q : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
  apply Matrix.submatrix_injective (r := q) (c := q) q.surjective q.surjective
  change ((fourTransportMatrix t u a b e f).transpose * fourTransportMatrix t u a b e f).submatrix
    q q = (1 : Matrix (Fin 4) (Fin 4) ℝ).submatrix q q
  rw [← Matrix.submatrix_mul_equiv _ _ _ q _, ← Matrix.transpose_submatrix]
  dsimp only [q]
  rw [fourTransportMatrix_submatrix, Matrix.submatrix_one_equiv]
  exact (fourTransport_mem_fiber ![t, u] a b e f he hf).1

private theorem det_pencil_fourTransport
    (c s d v a x b y e f z : ℝ)
    (hc : c ^ 2 + s ^ 2 = 1) (hd : d ^ 2 + v ^ 2 = 1)
    (ha : a ^ 2 + x ^ 2 = 1) (hb : b ^ 2 + y ^ 2 = 1) :
    (Matrix.scalar (Fin 4) z -
      !![c*a, -e*c*x, -s*b, f*s*y;
         d*x, e*d*a, -v*y, -f*v*b;
         s*a, -e*s*x, c*b, -f*c*y;
         v*x, e*v*a, d*y, f*d*b]).det =
      z ^ 4 - ((c + e*d)*a + (c + f*d)*b)*z ^ 3 +
        ((e+f)*c*d*(1+a*b) + (1+e*f)*a*b - (e+f)*s*v*x*y)*z ^ 2 -
        ((c*e*f+d*f)*a + (c*e*f+d*e)*b)*z + e*f := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply, Fin.succAbove]
  linear_combination
    (e*f*(d^2+v^2)*(a^2+x^2)*(b^2+y^2) -
      d*z*(e*b*(a^2+x^2)+f*a*(b^2+y^2)) + a*b*z^2) * hc +
    (e*f*((a^2+x^2)*(b^2+y^2) -
      c*z*(b*(a^2+x^2)+a*(b^2+y^2)) + a*b*z^2)) * hd +
    (e*(f*(b^2+y^2)-b*z*(c*f+d)+c*d*z^2)) * ha +
    (f*(e-a*z*(c*e+d)+c*d*z^2)) * hb

/-- The characteristic polynomial with both determinant parameters explicit.
The formula is algebraically valid for arbitrary real `e,f`; the orthogonal
fiber uses `e,f ∈ {1,-1}`. -/
theorem charpoly_fourTransportMatrix (t u a b e f : ℝ) :
    (fourTransportMatrix t u a b e f).charpoly =
      X ^ 4 - C ((Real.cos t + e*Real.cos u)*Real.cos a +
        (Real.cos t + f*Real.cos u)*Real.cos b)*X ^ 3 +
      C ((e+f)*Real.cos t*Real.cos u*(1+Real.cos a*Real.cos b) +
        (1+e*f)*Real.cos a*Real.cos b -
        (e+f)*Real.sin t*Real.sin u*Real.sin a*Real.sin b)*X ^ 2 -
      C ((Real.cos t*e*f+Real.cos u*f)*Real.cos a +
        (Real.cos t*e*f+Real.cos u*e)*Real.cos b)*X + C (e*f) := by
  apply Polynomial.funext
  intro z
  rw [Matrix.eval_charpoly]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  exact det_pencil_fourTransport _ _ _ _ _ _ _ _ _ _ _
    (Real.cos_sq_add_sin_sq t) (Real.cos_sq_add_sin_sq u)
    (Real.cos_sq_add_sin_sq a) (Real.cos_sq_add_sin_sq b)

/-- The actual determinant is the product of the independent source and
complement signs. -/
@[simp]
theorem det_fourTransportMatrix (t u a b e f : ℝ) :
    (fourTransportMatrix t u a b e f).det = e * f := by
  have h := congrArg (fun p : ℝ[X] => p.eval 0)
    (charpoly_fourTransportMatrix t u a b e f)
  norm_num [Matrix.eval_charpoly, Matrix.scalar_apply, Matrix.det_neg] at h
  exact h

@[simp]
theorem det_fourTransport (t u a b e f : ℝ) :
    (fourTransport ![t, u] a b e f).det = e * f := by
  rw [← fourTransportMatrix_submatrix, Matrix.det_submatrix_equiv_self,
    det_fourTransportMatrix]

theorem charpoly_fourTransport (t u a b e f : ℝ) :
    (fourTransport ![t, u] a b e f).charpoly =
      (fourTransportMatrix t u a b e f).charpoly := by
  rw [← fourTransportMatrix_submatrix]
  exact Matrix.charpoly_reindex finSumFinEquiv.symm _

/-- Both determinant-negative components have two compulsory real
eigenvalues and one conjugate pair, with their exact multiplicities
retained even when the quadratic has a repeated root. -/
theorem charpoly_fourTransportMatrix_opposite (t u a b e : ℝ) (he : e ^ 2 = 1) :
    (fourTransportMatrix t u a b e (-e)).charpoly =
      (X ^ 2 - 1) * (X ^ 2 -
        C ((Real.cos t + e*Real.cos u)*Real.cos a +
          (Real.cos t - e*Real.cos u)*Real.cos b)*X + 1) := by
  rw [charpoly_fourTransportMatrix]
  have hprod : e * -e = -1 := by nlinarith [he]
  have hlin : (Real.cos t*e*(-e)+Real.cos u*(-e))*Real.cos a +
      (Real.cos t*e*(-e)+Real.cos u*e)*Real.cos b =
      -((Real.cos t+e*Real.cos u)*Real.cos a +
        (Real.cos t-e*Real.cos u)*Real.cos b) := by
    linear_combination -(Real.cos t * (Real.cos a + Real.cos b)) * he
  rw [hlin]
  simp only [add_neg_cancel, zero_mul, hprod,
    sub_zero, map_zero, add_zero, map_neg, map_one]
  simp only [sub_eq_add_neg, neg_mul]
  ring

private theorem cos_add_mul_cos_sub (x y : ℝ) :
    Real.cos (x + y) * Real.cos (x - y) = Real.cos x ^ 2 + Real.cos y ^ 2 - 1 := by
  rw [Real.cos_add, Real.cos_sub]
  calc
    _ = Real.cos x ^ 2 * Real.cos y ^ 2 - Real.sin x ^ 2 * Real.sin y ^ 2 := by ring
    _ = _ := by rw [Real.sin_sq x, Real.sin_sq y]; ring

private theorem sin_add_mul_sin_sub (x y : ℝ) :
    Real.sin (x + y) * Real.sin (x - y) = Real.cos y ^ 2 - Real.cos x ^ 2 := by
  rw [Real.sin_add, Real.sin_sub]
  calc
    _ = Real.sin x ^ 2 * Real.cos y ^ 2 - Real.cos x ^ 2 * Real.sin y ^ 2 := by ring
    _ = _ := by rw [Real.sin_sq x, Real.sin_sq y]; ring

/-- In the rotation--rotation component the two phase coordinates have
cosines `cos h cos s` and `cos d cos r`. This is an identity of actual
characteristic polynomials, without any simple-spectrum assumption. -/
theorem charpoly_fourTransportMatrix_rotations (h d r s : ℝ) :
    (fourTransportMatrix (h+d) (h-d) (r+s) (r-s) 1 1).charpoly =
      X ^ 4 - C (4*(Real.cos h*Real.cos s)*(Real.cos d*Real.cos r))*X ^ 3 +
        C (4*(Real.cos h*Real.cos s)^2 + 4*(Real.cos d*Real.cos r)^2 - 2)*X ^ 2 -
        C (4*(Real.cos h*Real.cos s)*(Real.cos d*Real.cos r))*X + 1 := by
  rw [charpoly_fourTransportMatrix]
  norm_num only [one_mul, mul_one, one_add_one_eq_two, map_one]
  have htrace : (Real.cos (h+d)+Real.cos (h-d))*Real.cos (r+s) +
      (Real.cos (h+d)+Real.cos (h-d))*Real.cos (r-s) =
      4*(Real.cos h*Real.cos s)*(Real.cos d*Real.cos r) := by
    rw [Real.cos_add h d, Real.cos_sub h d, Real.cos_add r s, Real.cos_sub r s]
    ring
  have hmiddle : 2*Real.cos (h+d)*Real.cos (h-d)*(1+Real.cos (r+s)*Real.cos (r-s)) +
      2*Real.cos (r+s)*Real.cos (r-s) -
      2*Real.sin (h+d)*Real.sin (h-d)*Real.sin (r+s)*Real.sin (r-s) =
      4*(Real.cos h*Real.cos s)^2 + 4*(Real.cos d*Real.cos r)^2 - 2 := by
    calc
      _ = 2*(Real.cos (h+d)*Real.cos (h-d))*(1+Real.cos (r+s)*Real.cos (r-s)) +
          2*(Real.cos (r+s)*Real.cos (r-s)) -
          2*(Real.sin (h+d)*Real.sin (h-d))*(Real.sin (r+s)*Real.sin (r-s)) := by ring
      _ = _ := by rw [cos_add_mul_cos_sub, cos_add_mul_cos_sub,
        sin_add_mul_sin_sub, sin_add_mul_sin_sub]; ring
  rw [htrace, hmiddle]

/-- The two-reflection component has the same quartic with phase cosines
`sin h cos s` and `-sin d cos r`. Together with the preceding theorem this
retains both positive-determinant components of the full ambient fiber. -/
theorem charpoly_fourTransportMatrix_reflections (h d r s : ℝ) :
    (fourTransportMatrix (h+d) (h-d) (r+s) (r-s) (-1) (-1)).charpoly =
      X ^ 4 - C (4*(Real.sin h*Real.cos s)*(-Real.sin d*Real.cos r))*X ^ 3 +
        C (4*(Real.sin h*Real.cos s)^2 + 4*(-Real.sin d*Real.cos r)^2 - 2)*X ^ 2 -
        C (4*(Real.sin h*Real.cos s)*(-Real.sin d*Real.cos r))*X + 1 := by
  rw [charpoly_fourTransportMatrix]
  norm_num only [neg_one_mul, mul_neg_one, neg_neg, neg_mul, mul_one, map_one, map_neg]
  have htrace : (Real.cos (h+d)-Real.cos (h-d))*Real.cos (r+s) +
      (Real.cos (h+d)-Real.cos (h-d))*Real.cos (r-s) =
      4*(Real.sin h*Real.cos s)*(-Real.sin d*Real.cos r) := by
    rw [Real.cos_add h d, Real.cos_sub h d, Real.cos_add r s, Real.cos_sub r s]
    ring
  have hmiddle : -2*Real.cos (h+d)*Real.cos (h-d)*(1+Real.cos (r+s)*Real.cos (r-s)) +
      2*Real.cos (r+s)*Real.cos (r-s) +
      2*Real.sin (h+d)*Real.sin (h-d)*Real.sin (r+s)*Real.sin (r-s) =
      4*(Real.sin h*Real.cos s)^2 + 4*(-Real.sin d*Real.cos r)^2 - 2 := by
    calc
      _ = -2*(Real.cos (h+d)*Real.cos (h-d))*(1+Real.cos (r+s)*Real.cos (r-s)) +
          2*(Real.cos (r+s)*Real.cos (r-s)) +
          2*(Real.sin (h+d)*Real.sin (h-d))*(Real.sin (r+s)*Real.sin (r-s)) := by ring
      _ = _ := by
        rw [cos_add_mul_cos_sub, cos_add_mul_cos_sub,
          sin_add_mul_sin_sub, sin_add_mul_sin_sub]
        simp only [mul_pow, neg_sq, Real.sin_sq]
        ring
  calc
    _ = (X ^ 4 - C ((Real.cos (h+d)-Real.cos (h-d))*Real.cos (r+s) +
        (Real.cos (h+d)-Real.cos (h-d))*Real.cos (r-s))*X ^ 3 +
      C (-2*Real.cos (h+d)*Real.cos (h-d)*(1+Real.cos (r+s)*Real.cos (r-s)) +
        2*Real.cos (r+s)*Real.cos (r-s) +
        2*Real.sin (h+d)*Real.sin (h-d)*Real.sin (r+s)*Real.sin (r-s))*X ^ 2 -
      C ((Real.cos (h+d)-Real.cos (h-d))*Real.cos (r+s) +
        (Real.cos (h+d)-Real.cos (h-d))*Real.cos (r-s))*X + 1) := by
      simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one]
      ring
    _ = _ := by rw [htrace, hmiddle]; simp only [neg_mul]

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
