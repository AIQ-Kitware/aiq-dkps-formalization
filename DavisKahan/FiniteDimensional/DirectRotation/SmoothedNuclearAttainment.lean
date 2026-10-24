/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedNuclearCertificate
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Attainment of the smoothed nuclear certificate in principal coordinates

The independent optimal phases give an actual diagonal unitary. Its accepted
nuclear cost is exactly the sum of the scalar minima and the fixed-direction
cost. Thus the trace certificate is sharp, even for its enlarged competitor
class.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped ComplexConjugate InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

private theorem exists_diagonal_phase_isometry {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ E) (delta : ι → ℝ) :
    ∃ V : E ≃ₗᵢ[ℂ] E, ∀ j, V (e j) = circlePhase 1 (delta j) • e j := by
  classical
  let f := e.toBasis.constr ℂ (fun j => circlePhase 1 (delta j) • e j)
  have hf (j) : f (e j) = circlePhase 1 (delta j) • e j := e.toBasis.constr_basis ℂ _ j
  have horth : Orthonormal ℂ (f ∘ e.toBasis) := by
    rw [orthonormal_iff_ite]
    intro j k
    change ⟪f (e j), f (e k)⟫_ℂ = _
    rw [hf, hf, inner_smul_left, inner_smul_right, e.inner_eq_ite]
    by_cases hjk : j = k
    · subst k
      rw [ite_eq_left rfl, mul_one, RCLike.conj_mul, norm_circlePhase 1 _ zero_le_one]
      norm_num
    · rw [ite_eq_right hjk, mul_zero, mul_zero]
  let L := f.isometryOfOrthonormal e.orthonormal horth
  exact ⟨L.toLinearIsometryEquiv rfl, hf⟩

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The supplied principal-rotation eigenbasis admits an actual unitary
attaining the weighted nuclear lower bound. The same phase is used on both
members of each pair, and every fixed direction is fixed pointwise. -/
theorem exists_unitary_attaining_weightedNuclear
    (a b : ℝ) (hb : 0 < b) (hab : b < a) (theta : ι → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Icc 0 (Real.pi / 2))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j)) :
    ∃ V : E ≃ₗᵢ[ℂ] E,
      (∀ r i, V (e (.inl (r, i))) =
        circlePhase 1 (optimalWeightedPhase a b (theta i)) • e (.inl (r, i))) ∧
      (∀ j, V (e (.inr j)) = e (.inr j)) ∧
      UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • V.toLinearMap) =
        (∑ i, weightedPhaseMinimum a b (theta i)) + Fintype.card κ * (a - b) := by
  classical
  let delta : ((Fin 2 × ι) ⊕ κ) → ℝ :=
    Sum.elim (fun j => optimalWeightedPhase a b (theta j.2)) (fun _ => 0)
  obtain ⟨V, hV⟩ := exists_diagonal_phase_isometry e delta
  have hVp (r : Fin 2) (i : ι) : V (e (.inl (r, i))) =
      circlePhase 1 (optimalWeightedPhase a b (theta i)) • e (.inl (r, i)) := by
    simpa only [delta, Sum.elim_inl] using hV (.inl (r, i))
  have hVf (j : κ) : V (e (.inr j)) = e (.inr j) := by
    simpa [delta, circlePhase] using hV (.inr j)
  refine ⟨V, hVp, hVf, ?_⟩
  let lam : ((Fin 2 × ι) ⊕ κ) → ℂ := Sum.elim
    (fun j =>
      (if j.1 = 0 then
        ((a * Real.cos (theta j.2) : ℝ) : ℂ) + (a * Real.sin (theta j.2)) * Complex.I
      else ((a * Real.cos (theta j.2) : ℝ) : ℂ) - (a * Real.sin (theta j.2)) * Complex.I) -
        circlePhase b (optimalWeightedPhase a b (theta j.2)))
    (fun _ => ((a - b : ℝ) : ℂ))
  have heigen (j) : (A - (b : ℂ) • V.toLinearMap) (e j) = lam j • e j := by
    change A (e j) - (b : ℂ) • V (e j) = lam j • e j
    rcases j with ⟨r, i⟩ | j
    · by_cases hr : r = 0
      · subst r
        rw [hA0, hVp, smul_smul, ← sub_smul]
        simp [lam, circlePhase]
      · have hr1 : r = 1 := by omega
        subst r
        rw [hA1, hVp, smul_smul, ← sub_smul]
        simp [lam, circlePhase]
    · rw [hAf, hVf, ← sub_smul]
      simp [lam]
  rw [nuclear_eq_sum_norm_eigenvalues e _ lam heigen, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    have hcost := weightedPhaseCost_optimal a b (theta i) hb hab.le (hθ i)
    simpa [weightedPhaseCost, twoFocusCost, lam] using hcost
  · have hab0 : 0 ≤ a - b := sub_nonneg.mpr hab.le
    simp only [lam, Sum.elim_inr, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hab0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The identity factor attains the exact nuclear minimum when all supplied
rotation angles lie in the canonical regime, including its boundary. -/
theorem weightedNuclear_identity_attains_of_subcritical
    (a b : ℝ) (hb : 0 < b) (hab : b < a) (theta : ι → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Icc 0 (Real.pi / 2))
    (hsub : ∀ i, b ≤ a * Real.cos (theta i))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E) (A : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j)) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E (A - (b : ℂ) • LinearMap.id) =
      (∑ i, weightedPhaseMinimum a b (theta i)) + Fintype.card κ * (a - b) := by
  obtain ⟨Z, hZp, hZf, hcost⟩ :=
    exists_unitary_attaining_weightedNuclear a b hb hab theta hθ e A hA0 hA1 hAf
  have hphase (i) : optimalWeightedPhase a b (theta i) = 0 := by
    rw [optimalWeightedPhase, ite_eq_left (hsub i)]
  have hZid : Z.toLinearMap = LinearMap.id := by
    apply e.toBasis.ext
    intro j
    change Z (e j) = e j
    rcases j with ⟨r, i⟩ | j
    · rw [hZp, hphase]
      simp [circlePhase]
    · exact hZf j
  rw [hZid] at hcost
  exact hcost

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
