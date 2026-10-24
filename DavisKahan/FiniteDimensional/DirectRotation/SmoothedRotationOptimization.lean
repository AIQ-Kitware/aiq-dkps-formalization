/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCommutantOptimization
public import ForTauCeti.Analysis.InnerProductSpace.PairedRotationEigenbasis

/-!
# Exact weighted nuclear optimization without supplied coordinates

A rotation with positive real part and an anticommuting source reflection
admits the required paired eigenbasis canonically from its operator data.
The minimum over all commuting contractions is attained by a unitary and is
the spectral trace of the explicit angle cost.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The explicit weighted minimum as a spectral trace of the cosine
operator. Every nonzero angle occurs twice in the full ambient spectrum. -/
@[expose]
def weightedRotationMinimum (a b : ℝ) (C : E →L[ℂ] E) : ℝ :=
  (LinearMap.trace ℂ E
    (cfc (fun z : ℂ => (weightedPhaseMinimum a b (Real.arccos z.re) : ℂ)) C).toLinearMap).re / 2

theorem weightedRotationMinimum_eq_paired_sum
    (a b : ℝ) (hab : b ≤ a) (C : E →L[ℂ] E) [IsStarNormal C]
    {n m : ℕ} (theta : Fin n → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2))
    (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
    (hC0 : ∀ i, C (e (.inl (0, i))) = (Real.cos (theta i) : ℂ) • e (.inl (0, i)))
    (hC1 : ∀ i, C (e (.inl (1, i))) = (Real.cos (theta i) : ℂ) • e (.inl (1, i)))
    (hCf : ∀ j, C (e (.inr j)) = e (.inr j)) :
    weightedRotationMinimum a b C =
      (∑ i, weightedPhaseMinimum a b (theta i)) + m * (a - b) := by
  let lam : ((Fin 2 × Fin n) ⊕ Fin m) → ℂ :=
    Sum.elim (fun j => (Real.cos (theta j.2) : ℂ)) (fun _ => 1)
  have heigen (j) : C (e j) = lam j • e j := by
    rcases j with ⟨r, i⟩ | j
    · by_cases hr : r = 0
      · subst r
        exact hC0 i
      · have hr1 : r = 1 := by omega
        subst r
        exact hC1 i
    · simpa only [lam, Sum.elim_inr, one_smul] using hCf j
  have hacos (i) : Real.arccos (Real.cos (theta i)) = theta i :=
    Real.arccos_cos (hθ i).1.le (by linarith [(hθ i).2, Real.pi_pos])
  rw [weightedRotationMinimum,
    ContinuousLinearMap.re_trace_cfc_eq_sum
      (fun z => weightedPhaseMinimum a b (Real.arccos z.re)) C e lam heigen,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [lam, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_re, Complex.one_re,
    Real.arccos_one, hacos, weightedPhaseMinimum_zero a b hab,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The weighted nuclear commutant problem has an explicit spectral-trace
minimum and an attaining unitary. All coordinates are derived from the
positive cosine and symmetric sine data; competitors may mix all planes. -/
theorem exists_unitary_minimizing_weightedRotation
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (R J : E ≃ₗᵢ[ℂ] E) (C B : Module.End ℂ E)
    (hC : C.IsPositive) (hB : B.IsSymmetric)
    (hR : ∀ x, R x = C x + Complex.I • B x)
    (hpy : C * C + B * B = 1) (hJ : Function.Involutive J)
    (hanti : ∀ x, B (J x) = -J (B x)) :
    ∃ V : E ≃ₗᵢ[ℂ] E,
      (∀ x, V (J x) = J (V x)) ∧
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • R.toLinearMap - (b : ℂ) • V.toLinearMap) =
          weightedRotationMinimum a b (LinearMap.toContinuousLinearMap C) ∧
      ∀ Z : E →L[ℂ] E, ‖Z‖ ≤ 1 → (∀ x, Z (J x) = J (Z x)) →
        UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • R.toLinearMap - (b : ℂ) • V.toLinearMap) ≤
          UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • R.toLinearMap - (b : ℂ) • Z.toLinearMap) := by
  obtain ⟨n, m, e, theta, eps, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0, hJf⟩ :=
    exists_paired_rotation_eigenbasis R J C B hC hB hR hpy hJ hanti
  let A := (a : ℂ) • R.toLinearMap
  have hA0 (i) : A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)) := by
    change (a : ℂ) • R (e (.inl (0, i))) = _
    rw [hR0, smul_smul, Complex.exp_ofReal_mul_I]
    congr 1
    push_cast
    ring
  have hA1 (i) : A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)) := by
    change (a : ℂ) • R (e (.inl (1, i))) = _
    rw [hR1, smul_smul, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    congr 1
    push_cast
    ring
  have hAf (j) : A (e (.inr j)) = (a : ℂ) • e (.inr j) := by
    change (a : ℂ) • R (e (.inr j)) = _
    rw [hRf]
  obtain ⟨V, hcomm, hcost, hmin⟩ := exists_unitary_minimizing_commuting_contractions
    a b hb hab theta (fun i => ⟨(hθ i).1.le, (hθ i).2⟩) e A hA0 hA1 hAf
    J hJ hJ0 (fun j => (eps j : ℂ)) hJf
  have hCself : IsSelfAdjoint (LinearMap.toContinuousLinearMap C) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hC.isSymmetric
  let : IsStarNormal (LinearMap.toContinuousLinearMap C) := hCself.isStarNormal
  have hvalue := weightedRotationMinimum_eq_paired_sum a b hab.le (LinearMap.toContinuousLinearMap C)
    theta hθ e hC0 hC1 hCf
  simp only [Fintype.card_fin] at hcost
  exact ⟨V, hcomm, hcost.trans hvalue.symm, hmin⟩

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
