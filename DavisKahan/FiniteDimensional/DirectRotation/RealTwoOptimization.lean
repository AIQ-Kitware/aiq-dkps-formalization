/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealFourPrincipalAngles
public import ForTauCeti.LinearAlgebra.Matrix.RealOrthogonalTwo
public import ForTauCeti.Analysis.InnerProductSpace.NormalCharpolyCost

/-!
# Unrestricted real one-angle transport

Both determinant classes are retained. A rotation contributes two equal
chord singular values; a reflection contributes zero and two. The source
projection equation fixes the square of the first-column cosine, so the
shorter rotation gives the minimum in the positive determinant class.
This remains valid at zero and right angles and for arbitrary monotone
spectral penalties, without differentiability or strict monotonicity.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open _root_.Matrix Polynomial
open TauCeti.Matrix (planeOrthogonal)

/-- Full two-dimensional cost, counting a possible zero singular value. -/
@[expose] def twoDisplacementCost (rho : ℝ → ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ∑ i : Fin 2, rho ((LinearMap.id - W.toEuclideanLin).singularValues i)

/-- The coordinate source line's orthogonal projection. -/
@[expose] def twoSourceProjection : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- A rotation has the reciprocal characteristic polynomial determined by
its cosine. The full root multiset computes the cost even at repeated roots. -/
theorem twoDisplacementCost_rotation (rho : ℝ → ℝ) (t : ℝ) :
    twoDisplacementCost rho (planeOrthogonal t 1) =
      2 * rho (Real.sqrt (2 - 2 * Real.cos t)) := by
  obtain ⟨w, hadd, hmul, hw⟩ := TauCeti.exists_unit_circle_pair_of_trace_mem
    (2 * Real.cos t) ⟨by linarith [Real.neg_one_le_cos t], by linarith [Real.cos_le_one t]⟩
  have hquad : (X - C w) * (X - C (star w)) =
      X ^ 2 - C ((2 * Real.cos t : ℝ) : ℂ) * X + 1 := by
    calc
      _ = X ^ 2 - C (w + star w) * X + C (w * star w) := by
        simp only [map_add, map_mul]; ring
      _ = _ := by rw [hadd, hmul, map_one]
  have hpoly : (planeOrthogonal t 1).charpoly =
      X ^ 2 - C (2 * Real.cos t) * X + 1 := by
    rw [Matrix.charpoly_fin_two, TauCeti.Matrix.det_planeOrthogonal]
    simp [planeOrthogonal, Matrix.trace, Fin.sum_univ_two, two_mul]
  have hwstar : ‖1 - star w‖ = Real.sqrt (2 - 2 * Real.cos t) := by
    rw [← star_one (R := ℂ), ← star_sub, norm_star, hw]
  have hwconj : ‖1 - (starRingEnd ℂ) w‖ = Real.sqrt (2 - 2 * Real.cos t) := hwstar
  have hcost := Matrix.sum_displacement_singularValues_eq_complex_roots_of_orthogonal
    (planeOrthogonal t 1) (TauCeti.Matrix.transpose_mul_planeOrthogonal t 1 (by norm_num)) rho
  change twoDisplacementCost rho (planeOrthogonal t 1) = _ at hcost
  rw [hcost, hpoly]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_one, Polynomial.map_C]
  change ((X ^ 2 - C ((2 * Real.cos t : ℝ) : ℂ) * X + 1).roots.map
    (fun z => rho ‖1 - z‖)).sum = _
  rw [← hquad, Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero w)
    (Polynomial.X_sub_C_ne_zero (star w)))]
  simp [hw, hwconj, two_mul]

/-- Every real planar reflection has displacement singular values two and
zero, independent of its reflecting axis. -/
theorem twoDisplacementCost_reflection (rho : ℝ → ℝ) (t : ℝ) :
    twoDisplacementCost rho (planeOrthogonal t (-1)) = rho 0 + rho 2 := by
  have hpoly : (planeOrthogonal t (-1)).charpoly =
      (X - C 1) * (X - C (-1)) := by
    rw [Matrix.charpoly_fin_two, TauCeti.Matrix.det_planeOrthogonal]
    simp [planeOrthogonal, Matrix.trace, Fin.sum_univ_two]
    ring
  have hcost := Matrix.sum_displacement_singularValues_eq_complex_roots_of_orthogonal
    (planeOrthogonal t (-1))
    (TauCeti.Matrix.transpose_mul_planeOrthogonal t (-1) (by norm_num)) rho
  change twoDisplacementCost rho (planeOrthogonal t (-1)) = _ at hcost
  rw [hcost, hpoly]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one, Polynomial.map_neg, map_one, map_neg]
  rw [show (X - 1) * (X - -1) = (X - C (1 : ℂ)) * (X - C (-1 : ℂ)) by simp,
    Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero (1 : ℂ))
    (Polynomial.X_sub_C_ne_zero (-1 : ℂ))),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  norm_num

/-- Both determinant signs give actual transports to the same target line. -/
theorem planeOrthogonal_mem_transport_fiber (t e : ℝ) (he : e^2 = 1) :
    (planeOrthogonal t e).transpose * planeOrthogonal t e = 1 ∧
      planeOrthogonal t e * twoSourceProjection * (planeOrthogonal t e).transpose =
        planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose := by
  refine ⟨TauCeti.Matrix.transpose_mul_planeOrthogonal t e he, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoSourceProjection, planeOrthogonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every ambient orthogonal competitor has a first-column cosine whose
square is fixed by the transported line. This does not exclude reflections. -/
theorem exists_two_transport_coordinates
    (t : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) (hW : W.transpose * W = 1)
    (htrans : W * twoSourceProjection * W.transpose =
      planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose) :
    ∃ a e : ℝ, (e = 1 ∨ e = -1) ∧ W = planeOrthogonal a e ∧
      Real.cos a ^ 2 = Real.cos t ^ 2 := by
  obtain ⟨he, a, hform⟩ := TauCeti.Matrix.exists_planeOrthogonal_of_transpose_mul_eq_one W hW
  refine ⟨a, W.det, he, hform, ?_⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) htrans
  rw [hform] at h
  simpa [twoSourceProjection, planeOrthogonal, Matrix.mul_apply, Fin.sum_univ_two, pow_two]
    using h

/-- The one-angle minimum over all ambient orthogonal competitors is the
lesser of the shorter-rotation cost and the reflection cost. -/
theorem two_transport_cost_lower_bound
    (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2))
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0)
    (W : Matrix (Fin 2) (Fin 2) ℝ) (hW : W.transpose * W = 1)
    (htrans : W * twoSourceProjection * W.transpose =
      planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose) :
    min (2 * rho (Real.sqrt (2 - 2 * Real.cos t))) (rho 2) ≤
      twoDisplacementCost rho W := by
  obtain ⟨a, e, he, rfl, hcos⟩ := exists_two_transport_coordinates t W hW htrans
  rcases he with rfl | rfl
  · rw [twoDisplacementCost_rotation]
    have hct : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩
    have hca : Real.cos a ≤ Real.cos t := by nlinarith [sq_nonneg (Real.cos a - Real.cos t)]
    have hs : Real.sqrt (2 - 2 * Real.cos t) ≤
        Real.sqrt (2 - 2 * Real.cos a) := Real.sqrt_le_sqrt (by linarith)
    have hbound : Real.sqrt (2 - 2 * Real.cos a) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by norm_num, by linarith [Real.neg_one_le_cos a]⟩
    exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left
      (hrho ⟨Real.sqrt_nonneg _, hs.trans hbound⟩
        ⟨Real.sqrt_nonneg _, hbound⟩ hs) (by norm_num))
  · rw [twoDisplacementCost_reflection, hzero, zero_add]
    exact min_le_right _ _

/-- The minimum is attained in one of the two determinant classes. No
compactness or regularity of the penalty beyond monotonicity is required. -/
theorem exists_minimizing_two_transport
    (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2))
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0) :
    ∃ W : Matrix (Fin 2) (Fin 2) ℝ,
      W.transpose * W = 1 ∧
      W * twoSourceProjection * W.transpose =
        planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose ∧
      twoDisplacementCost rho W =
        min (2 * rho (Real.sqrt (2 - 2 * Real.cos t))) (rho 2) ∧
      IsMinOn (twoDisplacementCost rho)
        {A | A.transpose * A = 1 ∧ A * twoSourceProjection * A.transpose =
          planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose} W := by
  have hmin (W : Matrix (Fin 2) (Fin 2) ℝ) := two_transport_cost_lower_bound t ht rho hrho hzero W
  by_cases hle : 2 * rho (Real.sqrt (2 - 2 * Real.cos t)) ≤ rho 2
  · obtain ⟨hW, htrans⟩ := planeOrthogonal_mem_transport_fiber t 1 (by norm_num)
    refine ⟨planeOrthogonal t 1, hW, htrans, ?_, ?_⟩
    · rw [twoDisplacementCost_rotation, min_eq_left hle]
    · intro A hA
      rw [twoDisplacementCost_rotation, ← min_eq_left hle]
      exact hmin A hA.1 hA.2
  · obtain ⟨hW, htrans⟩ := planeOrthogonal_mem_transport_fiber t (-1) (by norm_num)
    refine ⟨planeOrthogonal t (-1), hW, htrans, ?_, ?_⟩
    · rw [twoDisplacementCost_reflection, hzero, zero_add, min_eq_right (le_of_not_ge hle)]
    · intro A hA
      rw [twoDisplacementCost_reflection, hzero, zero_add, ← min_eq_right (le_of_not_ge hle)]
      exact hmin A hA.1 hA.2

/-- The sharp one-angle canonical criterion, with full ambient comparison.
Equality includes both determinant classes among the minimizers. -/
theorem two_rotation_isMinOn_iff
    (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2))
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0) :
    IsMinOn (twoDisplacementCost rho)
      {A | A.transpose * A = 1 ∧ A * twoSourceProjection * A.transpose =
        planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose}
      (planeOrthogonal t 1) ↔
      2 * rho (Real.sqrt (2 - 2 * Real.cos t)) ≤ rho 2 := by
  constructor
  · intro h
    have hbound := h (planeOrthogonal_mem_transport_fiber t (-1) (by norm_num))
    change twoDisplacementCost rho (planeOrthogonal t 1) ≤
      twoDisplacementCost rho (planeOrthogonal t (-1)) at hbound
    simpa only [twoDisplacementCost_rotation, twoDisplacementCost_reflection,
      hzero, zero_add] using hbound
  · intro hle A hA
    rw [twoDisplacementCost_rotation, ← min_eq_left hle]
    exact two_transport_cost_lower_bound t ht rho hrho hzero A hA.1 hA.2

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
