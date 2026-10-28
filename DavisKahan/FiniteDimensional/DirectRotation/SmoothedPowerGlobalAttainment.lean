/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerGlobalLowerBound
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPrincipalAngles
public import ForTauCeti.Analysis.InnerProductSpace.DiagonalUnitary

/-!
# Exact unrestricted complex transport minima for the smoothed-power family

The common ambient lower bound and independently minimizing phases in a
canonical CS basis give the exact minimum on the full complex transport
fiber. The construction includes zero and right angles. It does not classify
all optimizers and does not rely on the older penalty-specific optima.
The CS geometry and compact scalar attainment are classical ingredients;
historical priority of the family-wide transport extension is unresolved.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

private theorem penalty_norm_one_sub_exp (p tau t : ℝ) :
    penalty p tau ‖1 - Complex.exp ((t : ℂ) * Complex.I)‖ =
      smoothedPowerPhaseCost p tau t := by
  rw [penalty, norm_sub_rev,
    Complex.norm_sub_one_sq_eq_of_norm_eq_one (Complex.norm_exp_ofReal_mul_I t),
    Complex.exp_ofReal_mul_I_re, smoothedPowerPhaseCost]
  rw [show tau ^ 2 + 2 * (1 - Real.cos t) = tau ^ 2 + 2 - 2 * Real.cos t by ring]

/-- Literal cost additivity for a phase-modified canonical CS basis.
The phases here may be arbitrary real numbers. -/
theorem paired_phase_transport_cost
    (p tau : ℝ) (htau : 0 ≤ tau)
    {n m : ℕ} (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
    (theta delta : Fin n → ℝ)
    (R Z : E ≃ₗᵢ[ℂ] E)
    (hR0 : ∀ i, R (e (.inl (0, i))) =
      Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i)))
    (hR1 : ∀ i, R (e (.inl (1, i))) =
      Complex.exp (((-theta i : ℝ) : ℂ) * Complex.I) • e (.inl (1, i)))
    (hRf : ∀ j, R (e (.inr j)) = e (.inr j))
    (hZp : ∀ r i, Z (e (.inl (r, i))) =
      Complex.exp ((delta i : ℂ) * Complex.I) • e (.inl (r, i)))
    (hZf : ∀ j, Z (e (.inr j)) = e (.inr j)) :
    displacementCost p tau (Z.trans R : E →L[ℂ] E) =
      ∑ i, phaseCost p tau (theta i) (delta i) := by
  classical
  let lam : ((Fin 2 × Fin n) ⊕ Fin m) → ℂ := Sum.elim
    (fun j => 1 - Complex.exp
      (((if j.1 = 0 then theta j.2 + delta j.2 else -(theta j.2 - delta j.2) : ℝ) : ℂ) *
        Complex.I)) (fun _ => 0)
  have heigen (j) : ((LinearMap.id : E →ₗ[ℂ] E) - (Z.trans R).toLinearMap) (e j) =
      lam j • e j := by
    change e j - R (Z (e j)) = lam j • e j
    rcases j with ⟨r, i⟩ | j
    · by_cases hr : r = 0
      · subst r
        rw [hZp, map_smul, hR0, smul_smul, ← Complex.exp_add]
        dsimp only [lam, Sum.elim_inl, Prod.fst, Prod.snd]
        simp only [ite_true]
        rw [show (delta i : ℂ) * Complex.I + (theta i : ℂ) * Complex.I =
          ((theta i + delta i : ℝ) : ℂ) * Complex.I by push_cast; ring,
          sub_smul, one_smul]
      · have hr1 : r = 1 := by omega
        subst r
        rw [hZp, map_smul, hR1, smul_smul, ← Complex.exp_add]
        dsimp only [lam, Sum.elim_inl, Prod.fst, Prod.snd]
        simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false]
        rw [show (delta i : ℂ) * Complex.I + ((-theta i : ℝ) : ℂ) * Complex.I =
          ((-(theta i - delta i) : ℝ) : ℂ) * Complex.I by push_cast; ring,
          sub_smul, one_smul]
    · rw [hZf, hRf, sub_self]
      exact (zero_smul ℂ _).symm
  let U := Unitary.linearIsometryEquiv.symm (Z.trans R)
  let := isStarNormal_of_mem_unitary U.property
  change normalDisplacementSpectralCost (penalty p tau) (U : E →L[ℂ] E) = _
  have heigenU (j) :
      ((LinearMap.id : E →ₗ[ℂ] E) - (U : E →L[ℂ] E).toLinearMap) (e j) = lam j • e j := by
    change e j - R (Z (e j)) = lam j • e j
    exact heigen j
  rw [normalDisplacementSpectralCost_eq_sum_singularValues,
    sum_singularValues_eq_sum_norm_eigenvalues e _ lam heigenU (penalty p tau),
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [lam, Sum.elim_inr, norm_zero, penalty_zero p tau htau,
    Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Sum.elim_inl, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  rw [penalty_norm_one_sub_exp, penalty_norm_one_sub_exp]
  simp only [phaseCost, smoothedPowerPhaseCost, Real.cos_neg]

/-- Minimizing the independent canonical phases attains the principal-angle sum. -/
theorem exists_unitary_attaining_principalAngles
    (p tau : ℝ) (hp : 0 ≤ p) (htau : 0 ≤ tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    ∃ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
      displacementCost p tau (W : E →L[ℂ] E) =
          ∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i) := by
  classical
  let D := finiteCrossedDefectEquiv K L hKL
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, eps, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0, hJf⟩ :=
    SmoothedPhaseTransition.exists_subspace_paired_rotation_reflection_basis_complex K L hKL
  choose delta hδ hopt hmin using
    fun i => exists_attains_phaseMinimum_of_nonneg p tau (theta i) hp (hθ i).1.le
  obtain ⟨Z, hZp, hZf, hZcomm⟩ := e.exists_paired_diagonal_commuting_involution
    (fun i => Complex.exp ((delta i : ℂ) * Complex.I))
    (fun i => Complex.norm_exp_ofReal_mul_I (delta i)) K.reflection
    K.reflection_involutive hJ0 (fun j => (eps j : ℂ)) hJf
  let W := Z.trans R
  have hWmap : K.map W.toLinearMap = L := by
    apply (Submodule.map_eq_iff_intertwines_reflection K L W).mpr
    intro x
    change R (Z (K.reflection x)) = L.reflection (R (Z x))
    rw [hZcomm]
    exact nonacuteDirectRotation_reflection_intertwines K L D (Z x)
  have hcost := paired_phase_transport_cost p tau htau e theta delta R Z hR0 hR1 hRf hZp hZf
  have hsum := SmoothedPhaseTransition.sum_principalAngles_eq_paired_sum K L e theta hθ
    hC0 hC1 hCf hJ0 (phaseMinimum p tau) (phaseMinimum_zero p tau htau)
  refine ⟨W, hWmap, hcost.trans ?_⟩
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ => (hopt i).symm)

/-- **Exact unrestricted finite complex minimum for the positively smoothed
family.** Independent scalar phases attain the value, while every ambient
unitary transporter obeys the lower bound. This is C1b for `tau>0`. -/
theorem exists_unitary_minimizing_transport_principalAngles
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    ∃ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
      displacementCost p tau (W : E →L[ℂ] E) =
        (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i)) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i)) ≤
          displacementCost p tau (T : E →L[ℂ] E) := by
  obtain ⟨W, hW, hcost⟩ := exists_unitary_attaining_principalAngles p tau (by linarith) htau.le K L hKL
  refine ⟨W, hW, hcost, ?_⟩
  intro T hT
  have h := sum_phaseMinimum_le_transport p tau hp hp2 htau K L
    (Unitary.linearIsometryEquiv.symm T)
    (by simpa only [MulEquiv.apply_symm_apply] using hT)
  exact h

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
