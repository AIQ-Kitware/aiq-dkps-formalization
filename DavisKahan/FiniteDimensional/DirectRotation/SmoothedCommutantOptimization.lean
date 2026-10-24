/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedNuclearAttainment

/-!
# Exact weighted nuclear optimization in a reflection commutant

In supplied principal-rotation eigenbasis coordinates, the independent
optimal phases attain the minimum over every commuting contraction.
Consequently the relaxation from commuting unitaries to commuting
contractions has no gap.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped InnerProductSpace

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℂ E] in
/-- Commuting with an isometry makes the two matched diagonal entries
equal, including their imaginary parts. -/
theorem inner_diagonal_eq_of_commute (J : E ≃ₗᵢ[ℂ] E) (Z : E →ₗ[ℂ] E)
    (hcomm : ∀ x, Z (J x) = J (Z x)) (x : E) :
    ⟪J x, Z (J x)⟫_ℂ = ⟪x, Z x⟫_ℂ := by
  rw [hcomm, J.inner_map_map]

/-- The explicit nuclear certificate applies to every contraction commuting
with the source reflection, including competitors that mix its planes. -/
theorem weightedNuclear_lowerBound_of_commute
    (a b : ℝ) (hb : 0 ≤ b) (hab : b < a) (theta : ι → ℝ)
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j))
    (J : E ≃ₗᵢ[ℂ] E) (hJ0 : ∀ i, J (e (.inl (0, i))) = e (.inl (1, i)))
    (Z : E →L[ℂ] E) (hZ : ‖Z‖ ≤ 1) (hcomm : ∀ x, Z (J x) = J (Z x)) :
    (∑ i, weightedPhaseMinimum a b (theta i)) + Fintype.card κ * (a - b) ≤
      UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z.toLinearMap) := by
  apply weightedNuclear_lowerBound_of_paired_diagonals a b hb hab theta e A Z.toLinearMap
    hA0 hA1 hAf
  · intro j
    calc
      ‖Z (e j)‖ ≤ ‖Z‖ * ‖e j‖ := Z.le_opNorm _
      _ ≤ 1 := by rw [e.norm_eq_one, mul_one]; exact hZ
  · intro i
    have h := inner_diagonal_eq_of_commute J Z.toLinearMap hcomm (e (.inl (0, i)))
    rw [hJ0] at h
    exact (congrArg Complex.im h).symm

/-- The convex relaxation of the weighted nuclear commutant problem has
an actual unitary minimizer with the explicit independent optimal phases. -/
theorem exists_unitary_minimizing_commuting_contractions
    (a b : ℝ) (hb : 0 < b) (hab : b < a) (theta : ι → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Icc 0 (Real.pi / 2))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j))
    (J : E ≃ₗᵢ[ℂ] E) (hJ : Function.Involutive J)
    (hJ0 : ∀ i, J (e (.inl (0, i))) = e (.inl (1, i)))
    (eps : κ → ℂ) (hJf : ∀ j, J (e (.inr j)) = eps j • e (.inr j)) :
    ∃ V : E ≃ₗᵢ[ℂ] E,
      (∀ x, V (J x) = J (V x)) ∧
      UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • V.toLinearMap) =
        (∑ i, weightedPhaseMinimum a b (theta i)) + Fintype.card κ * (a - b) ∧
      ∀ Z : E →L[ℂ] E, ‖Z‖ ≤ 1 → (∀ x, Z (J x) = J (Z x)) →
        UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • V.toLinearMap) ≤
          UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • Z.toLinearMap) := by
  obtain ⟨V, hVp, hVf, hcost⟩ :=
    exists_unitary_attaining_weightedNuclear a b hb hab theta hθ e A hA0 hA1 hAf
  have hJ1 (i : ι) : J (e (.inl (1, i))) = e (.inl (0, i)) := by
    rw [← hJ0, hJ]
  have hcomm : ∀ x, V (J x) = J (V x) := by
    have hmaps : V.toLinearMap.comp J.toLinearMap = J.toLinearMap.comp V.toLinearMap := by
      apply e.toBasis.ext
      intro j
      change V (J (e j)) = J (V (e j))
      rcases j with ⟨r, i⟩ | j
      · by_cases hr : r = 0
        · subst r
          rw [hJ0, hVp, hVp, map_smul, hJ0]
        · have hr1 : r = 1 := by omega
          subst r
          rw [hJ1, hVp, hVp, map_smul, hJ1]
      · rw [hJf, map_smul, hVf, hJf]
    intro x
    exact DFunLike.congr_fun hmaps x
  refine ⟨V, hcomm, hcost, ?_⟩
  intro Z hZ hZcomm
  rw [hcost]
  exact weightedNuclear_lowerBound_of_commute a b hb.le hab theta e A hA0 hA1 hAf
    J hJ0 Z hZ hZcomm

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
