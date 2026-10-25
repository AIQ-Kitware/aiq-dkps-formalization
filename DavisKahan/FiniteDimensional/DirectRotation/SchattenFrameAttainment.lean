/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalAttainment

/-!
# Attaining arbitrary scalar minima in any paired rotation frame

The frame may be adapted to prescribed commuting projections or other
spectral data. Independently attaining signed phases produce an actual
ambient transport with exact principal-angle cost. Its minimizing property
is compared against all ambient unitary transports, without a frame
assumption on competitors.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every independently attaining signed phase choice in any supplied
paired rotation frame gives a global ambient minimum. Both the actual
transport and its relative phase actions are retained. -/
theorem exists_schatten_transport_attaining_phases_in_frame_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (R : E ≃ₗᵢ[ℂ] E) (hRmap : K.map R.toLinearMap = L)
    {n m : ℕ} (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
    (theta : Fin n → ℝ) (eps : Fin m → ℝ)
    (hθ : ∀ i, theta i ∈ Ioc 0 (Real.pi / 2))
    (hC0 : ∀ i, Proposition35.section3CosAngleOperator K L (e (.inl (0, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (0, i)))
    (hC1 : ∀ i, Proposition35.section3CosAngleOperator K L (e (.inl (1, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (1, i)))
    (hCf : ∀ j, Proposition35.section3CosAngleOperator K L (e (.inr j)) = e (.inr j))
    (hR0 : ∀ i, R (e (.inl (0, i))) =
      Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i)))
    (hR1 : ∀ i, R (e (.inl (1, i))) =
      Complex.exp (((-theta i : ℝ) : ℂ) * Complex.I) • e (.inl (1, i)))
    (hRf : ∀ j, R (e (.inr j)) = e (.inr j))
    (hJ0 : ∀ i, K.reflection (e (.inl (0, i))) = e (.inl (1, i)))
    (hJf : ∀ j, K.reflection (e (.inr j)) = (eps j : ℂ) • e (.inr j))
    (delta : Fin n → ℝ) (hδ : ∀ i, delta i ∈ Icc (-theta i) (theta i))
    (hscalar : ∀ i, phasePower p.toReal (theta i) (delta i) = phaseMinimum p.toReal (theta i)) :
    ∃ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
      (∀ i, W (e (.inl (0, i))) =
        Complex.exp (((theta i + delta i : ℝ) : ℂ) * Complex.I) • e (.inl (0, i))) ∧
      (∀ i, W (e (.inl (1, i))) =
        Complex.exp (((-theta i + delta i : ℝ) : ℂ) * Complex.I) • e (.inl (1, i))) ∧
      (∀ j, W (e (.inr j)) = e (.inr j)) ∧
      (∀ r i, (W.trans R.symm) (e (.inl (r, i))) =
        Complex.exp ((delta i : ℂ) * Complex.I) • e (.inl (r, i))) ∧
      (∀ j, (W.trans R.symm) (e (.inr j)) = e (.inr j)) ∧
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal =
          ∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i) ∧
      IsMinOn
        (fun V : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - V.toLinearMap) ^ p.toReal)
        {V | V ∈ unitary (E →L[ℂ] E) ∧ V * K.starProjection * star V = L.starProjection}
        (W : E →L[ℂ] E) := by
  classical
  obtain ⟨Z, hZp, hZf, hZcomm⟩ := e.exists_paired_diagonal_commuting_involution
    (fun i => Complex.exp ((delta i : ℂ) * Complex.I))
    (fun i => Complex.norm_exp_ofReal_mul_I (delta i)) K.reflection
    K.reflection_involutive hJ0 (fun j => (eps j : ℂ)) hJf
  let W := Z.trans R
  have hmap : K.map W.toLinearMap = L := by
    apply (Submodule.map_eq_iff_intertwines_reflection K L W).mpr
    intro x
    change R (Z (K.reflection x)) = L.reflection (R (Z x))
    rw [hZcomm]
    exact (Submodule.map_eq_iff_intertwines_reflection K L R).mp hRmap (Z x)
  have hcost := schatten_signed_paired_phase_transport_eq_sum_complex p hp e theta delta
    (fun i => ⟨(hθ i).1.le, (hθ i).2⟩) hδ R Z hR0 hR1 hRf hZp hZf
  have hsum := SmoothedPhaseTransition.sum_principalAngles_eq_paired_sum K L e theta hθ
    hC0 hC1 hCf hJ0 (phaseMinimum p.toReal) (phaseMinimum_zero_angle p.toReal hp1.le)
  have hatt : UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - W.toLinearMap) ^ p.toReal =
        ∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i) := by
    rw [hcost, hsum]
    exact Finset.sum_congr rfl (fun i _ => hscalar i)
  have hrel : W.trans R.symm = Z := by
    ext x
    exact R.symm_apply_apply (Z x)
  refine ⟨W, hmap, ?_, ?_, ?_, ?_, ?_, hatt, ?_⟩
  · intro i
    change R (Z (e (.inl (0, i)))) = _
    rw [hZp, map_smul, hR0, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · intro i
    change R (Z (e (.inl (1, i)))) = _
    rw [hZp, map_smul, hR1, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · intro j
    change R (Z (e (.inr j))) = _
    rw [hZf, hRf]
  · intro r i
    rw [hrel]
    exact hZp r i
  · intro j
    rw [hrel]
    exact hZf j
  · intro V hV
    change UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - W.toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - V.toLinearMap) ^ p.toReal
    rw [hatt]
    let V' : unitary (E →L[ℂ] E) := ⟨V, hV.1⟩
    exact sum_phaseMinimum_le_schatten_transport_complex p hp hp1 hp2 K L V'
      ((map_eq_iff_conjugate_starProjection_complex K L V').mpr hV.2)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
