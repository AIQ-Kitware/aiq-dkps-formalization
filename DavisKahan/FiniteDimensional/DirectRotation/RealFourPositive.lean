/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealFourNegative
public import DavisKahan.FiniteDimensional.DirectRotation.RealFourPhaseRectangle

/-!
# Literal costs in both positive-determinant transport components

Two reciprocal characteristic quadratics give two conjugate unit-circle
pairs. Their displacement cost is computed with full multiplicities and
then applied to both actual positive-component coordinate matrices.
The penalty is arbitrary: regularity and monotonicity enter only in the
subsequent phase-rectangle optimization.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open _root_.Matrix Polynomial

/-- Two reciprocal quadratic factors compute the literal real orthogonal
cost, without a separated-root or nonzero-displacement assumption. -/
theorem four_displacement_cost_of_reciprocal_quadratics
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.transpose * A = 1)
    (T S : ℝ) (hT : T ∈ Set.Icc (-2) 2) (hS : S ∈ Set.Icc (-2) 2)
    (hpoly : A.charpoly = (X ^ 2 - C T * X + 1) * (X ^ 2 - C S * X + 1))
    (rho : ℝ → ℝ) :
    (∑ i : Fin (Fintype.card n), rho ((LinearMap.id - A.toEuclideanLin).singularValues i)) =
      2 * rho (Real.sqrt (2 - T)) + 2 * rho (Real.sqrt (2 - S)) := by
  obtain ⟨w, hwadd, hwmul, hw⟩ := TauCeti.exists_unit_circle_pair_of_trace_mem T hT
  obtain ⟨v, hvadd, hvmul, hv⟩ := TauCeti.exists_unit_circle_pair_of_trace_mem S hS
  have hquad (z : ℝ) (a : ℂ) (ha : a + star a = (z : ℂ)) (hm : a * star a = 1) :
      (X - C a) * (X - C (star a)) = X ^ 2 - C (z : ℂ) * X + 1 := by
    calc
      _ = X ^ 2 - C (a + star a) * X + C (a * star a) := by
        simp only [map_add, map_mul]; ring
      _ = _ := by rw [ha, hm, map_one]
  have hwstar : ‖1 - (starRingEnd ℂ) w‖ = Real.sqrt (2 - T) := by
    change ‖1 - star w‖ = _
    rw [← star_one (R := ℂ), ← star_sub, norm_star, hw]
  have hvstar : ‖1 - (starRingEnd ℂ) v‖ = Real.sqrt (2 - S) := by
    change ‖1 - star v‖ = _
    rw [← star_one (R := ℂ), ← star_sub, norm_star, hv]
  let mu : Fin 4 → ℂ := ![w, star w, v, star v]
  have hfactor : A.charpoly.map Complex.ofRealHom = ∏ i : Fin 4, (X - C (mu i)) := by
    rw [hpoly]
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_C, Fin.prod_univ_four]
    change (X ^ 2 - C (T : ℂ) * X + 1) * (X ^ 2 - C (S : ℂ) * X + 1) =
      (X - C w) * (X - C (star w)) * (X - C v) * (X - C (star v))
    rw [← hquad T w hwadd hwmul, ← hquad S v hvadd hvmul]
    ring
  rw [Matrix.sum_displacement_singularValues_eq_complex_roots_of_orthogonal A hA rho,
    hfactor, Polynomial.roots_prod _ _ (by
      simp only [Finset.prod_ne_zero_iff]
      exact fun i _ => Polynomial.X_sub_C_ne_zero (mu i))]
  simp [mu, hw, hv, hwstar, hvstar]
  ring

/-- The two phase cosines in a positive-component quartic determine its
actual displacement cost. No bounds on `x,y` or penalty are needed. -/
theorem four_displacement_cost_of_positive_quartic
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.transpose * A = 1) (x y : ℝ)
    (hpoly : A.charpoly = X ^ 4 - C (4*Real.cos x*Real.cos y)*X ^ 3 +
      C (4*Real.cos x^2+4*Real.cos y^2-2)*X ^ 2 -
      C (4*Real.cos x*Real.cos y)*X + 1) (rho : ℝ → ℝ) :
    (∑ i : Fin (Fintype.card n), rho ((LinearMap.id - A.toEuclideanLin).singularValues i)) =
      2*rho (Real.sqrt (2-2*Real.cos (x+y))) +
        2*rho (Real.sqrt (2-2*Real.cos (x-y))) := by
  rw [positive_four_quartic_eq_phase_quadratics x y] at hpoly
  exact four_displacement_cost_of_reciprocal_quadratics A hA _ _
    ⟨by linarith [Real.neg_one_le_cos (x+y)], by linarith [Real.cos_le_one (x+y)]⟩
    ⟨by linarith [Real.neg_one_le_cos (x-y)], by linarith [Real.cos_le_one (x-y)]⟩ hpoly rho

/-- Exact literal cost in the full rotation--rotation component, expressed
using any two angles with the prescribed phase cosines. -/
theorem fourTransport_rotations_cost_of_phase_cosines
    (h d r s x y : ℝ)
    (hx : Real.cos x = Real.cos h*Real.cos s)
    (hy : Real.cos y = Real.cos d*Real.cos r) (rho : ℝ → ℝ) :
    fourDisplacementCost rho (fourTransport ![h+d, h-d] (r+s) (r-s) 1 1) =
      2*rho (Real.sqrt (2-2*Real.cos (x+y))) +
        2*rho (Real.sqrt (2-2*Real.cos (x-y))) := by
  have hpoly : (fourTransport ![h+d, h-d] (r+s) (r-s) 1 1).charpoly =
      X ^ 4 - C (4*Real.cos x*Real.cos y)*X ^ 3 +
      C (4*Real.cos x^2+4*Real.cos y^2-2)*X ^ 2 -
      C (4*Real.cos x*Real.cos y)*X + 1 := by
    rw [charpoly_fourTransport, charpoly_fourTransportMatrix_rotations, hx, hy]
  have hcost := four_displacement_cost_of_positive_quartic _
    (fourTransport_mem_fiber ![h+d, h-d] (r+s) (r-s) 1 1 (by norm_num) (by norm_num)).1
    x y hpoly rho
  rw [Fintype.card_sum, Fintype.card_fin] at hcost
  exact hcost

/-- Exact literal cost in the full two-reflection positive component.
It retains all competitors in that component, rather than prescribing
independent principal-plane transport. -/
theorem fourTransport_reflections_cost_of_phase_cosines
    (h d r s x y : ℝ)
    (hx : Real.cos x = Real.sin h*Real.cos s)
    (hy : Real.cos y = -Real.sin d*Real.cos r) (rho : ℝ → ℝ) :
    fourDisplacementCost rho (fourTransport ![h+d, h-d] (r+s) (r-s) (-1) (-1)) =
      2*rho (Real.sqrt (2-2*Real.cos (x+y))) +
        2*rho (Real.sqrt (2-2*Real.cos (x-y))) := by
  have hpoly : (fourTransport ![h+d, h-d] (r+s) (r-s) (-1) (-1)).charpoly =
      X ^ 4 - C (4*Real.cos x*Real.cos y)*X ^ 3 +
      C (4*Real.cos x^2+4*Real.cos y^2-2)*X ^ 2 -
      C (4*Real.cos x*Real.cos y)*X + 1 := by
    rw [charpoly_fourTransport, charpoly_fourTransportMatrix_reflections, hx, hy]
  have hcost := four_displacement_cost_of_positive_quartic _
    (fourTransport_mem_fiber ![h+d, h-d] (r+s) (r-s) (-1) (-1) (by norm_num) (by norm_num)).1
    x y hpoly rho
  rw [Fintype.card_sum, Fintype.card_fin] at hcost
  exact hcost

/-- Every rotation--rotation competitor has actual principal phase
coordinates in the full rectangle, with its literal cost retained. -/
theorem exists_fourTransport_rotations_phase_rectangle
    (h d r s : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hh : h ≤ Real.pi / 2)
    (rho : ℝ → ℝ) :
    ∃ x ∈ Set.Icc h (Real.pi-h), ∃ y ∈ Set.Icc d (Real.pi-d),
      Real.cos x = Real.cos h*Real.cos s ∧
      Real.cos y = Real.cos d*Real.cos r ∧
      fourDisplacementCost rho (fourTransport ![h+d, h-d] (r+s) (r-s) 1 1) =
        2*rho (Real.sqrt (2-2*Real.cos (x+y))) +
          2*rho (Real.sqrt (2-2*Real.cos (x-y))) := by
  obtain ⟨hx, hxmem⟩ := arccos_cos_mul_cos_data h s ⟨hd.trans hdh, hh⟩
  obtain ⟨hy, hymem⟩ := arccos_cos_mul_cos_data d r ⟨hd, hdh.trans hh⟩
  exact ⟨_, hxmem, _, hymem, hx, hy,
    fourTransport_rotations_cost_of_phase_cosines h d r s _ _ hx hy rho⟩

/-- After exchanging the two phase coordinates, every two-reflection
competitor lies in the rotation rectangle and has the same literal cost.
The containment uses the larger principal-angle bound `h+d <= pi/2`. -/
theorem exists_fourTransport_reflections_phase_rectangle
    (h d r s : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2)
    (rho : ℝ → ℝ) :
    ∃ x ∈ Set.Icc h (Real.pi-h), ∃ y ∈ Set.Icc d (Real.pi-d),
      Real.cos x = -Real.sin d*Real.cos r ∧
      Real.cos y = Real.sin h*Real.cos s ∧
      fourDisplacementCost rho (fourTransport ![h+d, h-d] (r+s) (r-s) (-1) (-1)) =
        2*rho (Real.sqrt (2-2*Real.cos (x+y))) +
          2*rho (Real.sqrt (2-2*Real.cos (x-y))) := by
  obtain ⟨hy, hymem⟩ := arccos_cos_mul_cos_data (Real.pi/2-h) s
    ⟨by linarith, by linarith⟩
  obtain ⟨hx, hxmem⟩ := arccos_cos_mul_cos_data (Real.pi/2-d) (r+Real.pi)
    ⟨by linarith, by linarith⟩
  let x := Real.arccos (Real.cos (Real.pi/2-d)*Real.cos (r+Real.pi))
  let y := Real.arccos (Real.cos (Real.pi/2-h)*Real.cos s)
  have hxcos : Real.cos x = -Real.sin d*Real.cos r := by
    simpa only [x, Real.cos_pi_div_two_sub, Real.cos_add_pi, mul_neg, neg_mul] using hx
  have hycos : Real.cos y = Real.sin h*Real.cos s := by
    simpa only [y, Real.cos_pi_div_two_sub] using hy
  refine ⟨x, ⟨by linarith [hxmem.1], by linarith [hxmem.2]⟩,
    y, ⟨by linarith [hymem.1], by linarith [hymem.2]⟩, hxcos, hycos, ?_⟩
  have hcost := fourTransport_reflections_cost_of_phase_cosines h d r s y x hycos hxcos rho
  have hdiff : Real.cos (y-x) = Real.cos (x-y) := by
    rw [← Real.cos_neg (x-y), neg_sub]
  simpa only [add_comm y x, hdiff] using hcost

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
