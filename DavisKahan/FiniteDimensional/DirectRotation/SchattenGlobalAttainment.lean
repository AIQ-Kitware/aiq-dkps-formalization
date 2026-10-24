/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalLowerBound
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPrincipalAngles
import ForTauCeti.Analysis.InnerProductSpace.DiagonalUnitary

/-!
# Exact unrestricted complex Schatten transport minima

Independently minimizing scalar phases on the canonical principal planes
gives a unitary transport. Its literal Schatten power is the sum of the
scalar minima over the accepted principal angles. Together with the
unrestricted lower bound this proves the exact higher-rank minimum.
Zero and right principal angles and empty subspaces are included.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem exists_paired_phase_correction
    {n m : ℕ} (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
    (delta : Fin n → ℝ) (J : E ≃ₗᵢ[ℂ] E) (hJ : Function.Involutive J)
    (hJ0 : ∀ i, J (e (.inl (0, i))) = e (.inl (1, i)))
    (eps : Fin m → ℝ) (hJf : ∀ j, J (e (.inr j)) = (eps j : ℂ) • e (.inr j)) :
    ∃ Z : E ≃ₗᵢ[ℂ] E,
      (∀ r i, Z (e (.inl (r, i))) = Complex.exp ((delta i : ℂ) * Complex.I) •
        e (.inl (r, i))) ∧
      (∀ j, Z (e (.inr j)) = e (.inr j)) ∧ (∀ x, Z (J x) = J (Z x)) := by
  classical
  let lam : ((Fin 2 × Fin n) ⊕ Fin m) → ℂ :=
    Sum.elim (fun j => Complex.exp ((delta j.2 : ℂ) * Complex.I)) (fun _ => 1)
  obtain ⟨Z, hZ⟩ := e.exists_linearIsometryEquiv_apply_eq_smul lam (by
    rintro (⟨r, i⟩ | j)
    · exact Complex.norm_exp_ofReal_mul_I _
    · exact norm_one)
  have hZp (r i) : Z (e (.inl (r, i))) =
      Complex.exp ((delta i : ℂ) * Complex.I) • e (.inl (r, i)) := hZ _
  have hZf (j) : Z (e (.inr j)) = e (.inr j) := by
    simpa only [lam, Sum.elim_inr, one_smul] using hZ (.inr j)
  have hJ1 (i) : J (e (.inl (1, i))) = e (.inl (0, i)) := by rw [← hJ0, hJ]
  refine ⟨Z, hZp, hZf, ?_⟩
  have hmaps : Z.toLinearMap.comp J.toLinearMap = J.toLinearMap.comp Z.toLinearMap := by
    apply e.toBasis.ext
    intro j
    change Z (J (e j)) = J (Z (e j))
    rcases j with ⟨r, i⟩ | j
    · by_cases hr : r = 0
      · subst r
        rw [hJ0, hZp, hZp, map_smul, hJ0]
      · have hr1 : r = 1 := by omega
        subst r
        rw [hJ1, hZp, hZp, map_smul, hJ1]
    · rw [hJf, map_smul, hZf, hJf]
  exact fun x => DFunLike.congr_fun hmaps x

omit [CompleteSpace E] in
/-- The Schatten displacement of a phase-modified principal rotation is
the sum of its scalar phase power sums. -/
theorem schatten_paired_phase_transport_eq_sum_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {n m : ℕ} (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
    (theta delta : Fin n → ℝ)
    (hθ : ∀ i, theta i ∈ Icc 0 (Real.pi / 2))
    (hδ : ∀ i, delta i ∈ Icc 0 (theta i))
    (R Z : E ≃ₗᵢ[ℂ] E)
    (hR0 : ∀ i, R (e (.inl (0, i))) =
      Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i)))
    (hR1 : ∀ i, R (e (.inl (1, i))) =
      Complex.exp (((-theta i : ℝ) : ℂ) * Complex.I) • e (.inl (1, i)))
    (hRf : ∀ j, R (e (.inr j)) = e (.inr j))
    (hZp : ∀ r i, Z (e (.inl (r, i))) =
      Complex.exp ((delta i : ℂ) * Complex.I) • e (.inl (r, i)))
    (hZf : ∀ j, Z (e (.inr j)) = e (.inr j)) :
    UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - (Z.trans R).toLinearMap) ^ p.toReal =
      ∑ i, phasePower p.toReal (theta i) (delta i) := by
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
  have hp0 : p.toReal ≠ 0 :=
    (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp).ne'
  rw [schatten_rpow_eq_sum_norm_eigenvalues e _ lam heigen p hp,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [lam, Sum.elim_inr, norm_zero, Real.zero_rpow hp0,
    Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Sum.elim_inl, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  rw [norm_one_sub_exp_eq_phaseChord _ ⟨by linarith [(hθ i).1, (hδ i).1],
      by linarith [(hθ i).2, (hδ i).2]⟩,
    norm_one_sub_exp_neg_eq_phaseChord _ ⟨by linarith [(hδ i).2],
      by linarith [(hθ i).2, (hδ i).1, Real.pi_pos]⟩]
  rfl

/-- Independently minimizing the principal-plane phases attains the exact
principal-angle cost for any equal-rank complex subspace pair. -/
theorem exists_unitary_attaining_schatten_principalAngles_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    ∃ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal =
          ∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i) := by
  classical
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  let D := finiteCrossedDefectEquiv K L hKL
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, eps, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0, hJf⟩ :=
    SmoothedPhaseTransition.exists_subspace_paired_rotation_reflection_basis_complex K L hKL
  choose delta hδ hopt hmin using
    fun i => exists_attains_phaseMinimum p.toReal (theta i) hp1 (hθ i).1.le
  obtain ⟨Z, hZp, hZf, hZcomm⟩ := exists_paired_phase_correction e delta K.reflection
    K.reflection_involutive hJ0 eps hJf
  let W := Z.trans R
  have hWmap : K.map W.toLinearMap = L := by
    apply (Submodule.map_eq_iff_intertwines_reflection K L W).mpr
    intro x
    change R (Z (K.reflection x)) = L.reflection (R (Z x))
    rw [hZcomm]
    exact nonacuteDirectRotation_reflection_intertwines K L D (Z x)
  have hcost := schatten_paired_phase_transport_eq_sum_complex p hp e theta delta
    (fun i => ⟨(hθ i).1.le, (hθ i).2⟩) hδ R Z hR0 hR1 hRf hZp hZf
  have hsum := SmoothedPhaseTransition.sum_principalAngles_eq_paired_sum K L e theta hθ
    hC0 hC1 hCf hJ0 (phaseMinimum p.toReal) (phaseMinimum_zero_angle p.toReal hp1)
  refine ⟨W, hWmap, hcost.trans ?_⟩
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ => (hopt i).symm)

/-- **Exact unrestricted higher-rank Schatten minimum.** Some complex
unitary transport attains the scalar principal-angle sum, and every
admissible ambient unitary has at least that cost. -/
theorem exists_unitary_minimizing_schatten_transport_principalAngles_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    ∃ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
      UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal =
        (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i)) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i)) ≤
          UnitarilyInvariantSeminorm.schatten ℂ E E p
            (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  obtain ⟨W, hW, hcost⟩ := exists_unitary_attaining_schatten_principalAngles_complex p hp K L hKL
  refine ⟨W, hW, hcost, ?_⟩
  intro T hT
  have h := sum_phaseMinimum_le_schatten_transport_complex p hp hp1 hp2 K L
    (Unitary.linearIsometryEquiv.symm T)
    (by simpa only [MulEquiv.apply_symm_apply] using hT)
  exact h

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
