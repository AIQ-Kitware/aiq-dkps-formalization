/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCommutantOptimization

/-!
# Quantitative stability from the smoothed nuclear certificate

On a unitary competitor, the diagonal defect controls the squared Frobenius
distance from the identity. A uniform positive dual weight therefore turns
the exact global lower bound into a quantitative growth estimate.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped InnerProductSpace

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [Fintype κ]

/-- A lower bound for every dual diagonal weight controls the squared
Frobenius distance of a unitary competitor from the identity. -/
theorem mul_sq_frobenius_le_weightedDiagonalDefect
    (a b c : ℝ) (hc : c ≤ 1) (theta : ι → ℝ)
    (hweight : ∀ i, c ≤ dualReal a b (theta i))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (Z : E ≃ₗᵢ[ℂ] E) :
    c / 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
        (Z.toLinearMap - LinearMap.id) ^ 2 ≤ weightedDiagonalDefect a b theta e Z.toLinearMap := by
  let D := Z.toLinearMap - LinearMap.id
  have hdelta (j) :
      1 - (⟪e j, Z (e j)⟫_ℂ).re = ‖D (e j)‖ ^ 2 / 2 := by
    have h := norm_sub_sq (𝕜 := ℂ) (e j) (Z (e j))
    rw [e.norm_eq_one, Z.norm_map, e.norm_eq_one] at h
    change ‖e j - Z (e j)‖ ^ 2 = 1 ^ 2 - 2 * (⟪e j, Z (e j)⟫_ℂ).re + 1 ^ 2 at h
    change 1 - (⟪e j, Z (e j)⟫_ℂ).re = ‖Z (e j) - e j‖ ^ 2 / 2
    rw [norm_sub_rev]
    linarith
  have hpair (i) : c / 2 * (‖D (e (.inl (0, i)))‖ ^ 2 + ‖D (e (.inl (1, i)))‖ ^ 2) ≤
      dualReal a b (theta i) *
        (2 - (⟪e (.inl (0, i)), Z (e (.inl (0, i)))⟫_ℂ).re -
          (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).re) := by
    have hid :
        2 - (⟪e (.inl (0, i)), Z (e (.inl (0, i)))⟫_ℂ).re -
            (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).re =
          (‖D (e (.inl (0, i)))‖ ^ 2 + ‖D (e (.inl (1, i)))‖ ^ 2) / 2 := by
      linarith [hdelta (.inl (0, i)), hdelta (.inl (1, i))]
    rw [hid]
    have h := mul_le_mul_of_nonneg_right (hweight i)
      (show 0 ≤ (‖D (e (.inl (0, i)))‖ ^ 2 + ‖D (e (.inl (1, i)))‖ ^ 2) / 2 by positivity)
    linarith
  have hfixed (j) : c / 2 * ‖D (e (.inr j))‖ ^ 2 ≤
      1 - (⟪e (.inr j), Z (e (.inr j))⟫_ℂ).re := by
    rw [hdelta]
    have h := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖D (e (.inr j))‖)
    linarith
  calc
    _ = (∑ i, c / 2 * (‖D (e (.inl (0, i)))‖ ^ 2 + ‖D (e (.inl (1, i)))‖ ^ 2)) +
        ∑ j : κ, c / 2 * ‖D (e (.inr j))‖ ^ 2 := by
      rw [UnitarilyInvariantSeminorm.sq_frobenius_apply e,
        Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
        ← Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
    _ ≤ weightedDiagonalDefect a b theta e Z.toLinearMap :=
      add_le_add (Finset.sum_le_sum (fun i _ => hpair i))
        (Finset.sum_le_sum (fun j _ => hfixed j))

/-- The exact weighted commutant minimum has quadratic growth whenever
the dual diagonal weights have a common lower bound. The competitor may
mix all principal planes. -/
theorem weightedNuclear_growth_of_commute
    (a b c : ℝ) (hb : 0 ≤ b) (hab : b < a) (hc : c ≤ 1) (theta : ι → ℝ)
    (hweight : ∀ i, c ≤ dualReal a b (theta i))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j))
    (J : E ≃ₗᵢ[ℂ] E) (hJ0 : ∀ i, J (e (.inl (0, i))) = e (.inl (1, i)))
    (Z : E ≃ₗᵢ[ℂ] E) (hcomm : ∀ x, Z (J x) = J (Z x)) :
    b * c / 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
        (Z.toLinearMap - LinearMap.id) ^ 2 ≤
      UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z.toLinearMap) -
        ((∑ i, weightedPhaseMinimum a b (theta i)) + Fintype.card κ * (a - b)) := by
  have hdiag (i) :
      (⟪e (.inl (0, i)), Z (e (.inl (0, i)))⟫_ℂ).im =
        (⟪e (.inl (1, i)), Z (e (.inl (1, i)))⟫_ℂ).im := by
    have h := inner_diagonal_eq_of_commute J Z.toLinearMap hcomm (e (.inl (0, i)))
    rw [hJ0] at h
    exact (congrArg Complex.im h).symm
  have hraw := weightedNuclear_lowerBound_with_diagonal_defect
    a b hb hab theta e A Z.toLinearMap hA0 hA1 hAf hdiag
  have henergy := mul_sq_frobenius_le_weightedDiagonalDefect a b c hc theta hweight e Z
  have hscaled := mul_le_mul_of_nonneg_left henergy hb
  nlinarith

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
