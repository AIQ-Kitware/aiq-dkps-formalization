/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenCanonicalUniqueness
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenCanonicalOptimality
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenFrameAttainment

/-!
# Independent signed phases and the exact uniqueness criterion

One complete paired frame, derived from the actual subspace pair, realizes
every independent choice of attaining scalar phases. Each construction is
globally minimizing against all ambient competitors. Opposite phases give
distinct optimizers whenever any principal angle is supercritical. This
includes right angles and all multiplicities.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A common frame derived from the original pair realizes every
independently attaining signed phase choice as a global ambient minimum.
No coordinate decomposition is assumed of the input pair or competitors. -/
theorem exists_schatten_minimizers_with_independent_phases_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
      (theta : Fin n → ℝ),
      (∀ i, theta i ∈ Ioc 0 (Real.pi / 2)) ∧
      (∀ i, Proposition35.section3CosAngleOperator K L (e (.inl (0, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (0, i))) ∧
      (∀ i, Proposition35.section3CosAngleOperator K L (e (.inl (1, i))) =
        (Real.cos (theta i) : ℂ) • e (.inl (1, i))) ∧
      (∀ j, Proposition35.section3CosAngleOperator K L (e (.inr j)) = e (.inr j)) ∧
      (∀ i, K.reflection (e (.inl (0, i))) = e (.inl (1, i))) ∧
      ∀ delta : Fin n → ℝ,
        (∀ i, delta i ∈ Icc (-theta i) (theta i)) →
        (∀ i, phasePower p.toReal (theta i) (delta i) = phaseMinimum p.toReal (theta i)) →
        ∃ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
          (∀ i, W (e (.inl (0, i))) =
            Complex.exp (((theta i + delta i : ℝ) : ℂ) * Complex.I) • e (.inl (0, i))) ∧
          (∀ i, W (e (.inl (1, i))) =
            Complex.exp (((-theta i + delta i : ℝ) : ℂ) * Complex.I) • e (.inl (1, i))) ∧
          (∀ j, W (e (.inr j)) = e (.inr j)) ∧
          UnitarilyInvariantSeminorm.schatten ℂ E E p
            (LinearMap.id - W.toLinearMap) ^ p.toReal =
              ∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i) ∧
          IsMinOn
            (fun V : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
              (LinearMap.id - V.toLinearMap) ^ p.toReal)
            {V | V ∈ unitary (E →L[ℂ] E) ∧ V * K.starProjection * star V = L.starProjection}
            (W : E →L[ℂ] E) := by
  classical
  let D := finiteCrossedDefectEquiv K L hKL
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, eps, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0, hJf⟩ :=
    SmoothedPhaseTransition.exists_subspace_paired_rotation_reflection_basis_complex K L hKL
  change ∀ i, R (e (.inl (0, i))) =
    Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i)) at hR0
  change ∀ i, R (e (.inl (1, i))) =
    Complex.exp (((-theta i : ℝ) : ℂ) * Complex.I) • e (.inl (1, i)) at hR1
  change ∀ j, R (e (.inr j)) = e (.inr j) at hRf
  refine ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hJ0, ?_⟩
  intro delta hδ hscalar
  have hRmap : K.map R.toLinearMap = L := by
    apply (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
    exact nonacuteDirectRotation_reflection_intertwines K L D
  obtain ⟨W, hW, hW0, hW1, hWf, _, _, hcost, hmin⟩ :=
    exists_schatten_transport_attaining_phases_in_frame_complex p hp hp1 hp2 K L R hRmap
      e theta eps hθ hC0 hC1 hCf hR0 hR1 hRf hJ0 hJf delta hδ hscalar
  exact ⟨W, hW, hW0, hW1, hWf, hcost, hmin⟩

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
private theorem phase_eq_zero_of_exp_eq_negative (delta : ℝ)
    (hδ : delta ∈ Icc 0 (Real.pi / 2))
    (heq : Complex.exp ((delta : ℂ) * Complex.I) =
      Complex.exp (((-delta : ℝ) : ℂ) * Complex.I)) : delta = 0 := by
  have hi := congrArg Complex.im heq
  simp only [Complex.exp_ofReal_mul_I_im, Real.sin_neg] at hi
  apply Real.strictMonoOn_sin.injOn
    (show delta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [hδ.1, Real.pi_pos], hδ.2⟩)
    (show (0 : ℝ) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  rw [Real.sin_zero]
  linarith only [hi]

/-- Opposite phase constructions are globally minimizing and coincide
exactly when every accepted principal angle obeys the critical bound. -/
theorem exists_opposite_schatten_minimizers_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    ∃ U V : unitary (E →L[ℂ] E),
      (K.map (Unitary.linearIsometryEquiv U).toLinearMap = L ∧
        IsMinOn
          (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
            (LinearMap.id - W.toLinearMap) ^ p.toReal)
          {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
          (U : E →L[ℂ] E)) ∧
      (K.map (Unitary.linearIsometryEquiv V).toLinearMap = L ∧
        IsMinOn
          (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
            (LinearMap.id - W.toLinearMap) ^ p.toReal)
          {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
          (V : E →L[ℂ] E)) ∧
      (U = V ↔ ∀ i : Fin (Module.finrank ℂ K),
        K.principalAngles L i ≤ criticalAngle p.toReal) := by
  classical
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hJ0, hatt⟩ :=
    exists_schatten_minimizers_with_independent_phases_complex p hp hp1 hp2 K L hKL
  let delta := fun i => optimalPhase p.toReal (theta i)
  have hδ (i) : delta i ∈ Icc 0 (theta i) :=
    (optimalPhase_spec p.toReal (theta i) hp1.le (hθ i).1.le).1
  have hscalar (i) : phasePower p.toReal (theta i) (delta i) =
      phaseMinimum p.toReal (theta i) :=
    (optimalPhase_spec p.toReal (theta i) hp1.le (hθ i).1.le).2.1
  obtain ⟨W, hWmap, hW0, _, _, _, hWmin⟩ := hatt delta
    (fun i => ⟨by linarith [(hδ i).1, (hθ i).1], (hδ i).2⟩) hscalar
  obtain ⟨X, hXmap, hX0, _, _, _, hXmin⟩ := hatt (fun i => -delta i)
    (fun i => ⟨by linarith [(hδ i).2], by linarith [(hδ i).1, (hθ i).1]⟩)
    (fun i => by
      rw [phasePower, show theta i + -delta i = theta i - delta i by ring,
        show theta i - -delta i = theta i + delta i by ring, add_comm]
      exact hscalar i)
  let U := Unitary.linearIsometryEquiv.symm W
  let V := Unitary.linearIsometryEquiv.symm X
  have hUmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L := by
    simpa only [U, MulEquiv.apply_symm_apply] using hWmap
  have hVmap : K.map (Unitary.linearIsometryEquiv V).toLinearMap = L := by
    simpa only [V, MulEquiv.apply_symm_apply] using hXmap
  refine ⟨U, V, ⟨hUmap, hWmin⟩, ⟨hVmap, hXmin⟩, ?_⟩
  constructor
  · intro heq
    apply SmoothedPhaseTransition.principalAngles_le_of_paired_angles_le
      K L e theta hθ hC0 hC1 hCf hJ0 (criticalAngle p.toReal)
      (criticalAngle_mem p.toReal hp1 hp2).1.le
    intro i
    have hphase : Complex.exp (((theta i + delta i : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((theta i + -delta i : ℝ) : ℂ) * Complex.I) := by
      apply smul_left_injective ℂ (e.toBasis.ne_zero (.inl (0, i)))
      change Complex.exp (((theta i + delta i : ℝ) : ℂ) * Complex.I) • e (.inl (0, i)) =
        Complex.exp (((theta i + -delta i : ℝ) : ℂ) * Complex.I) • e (.inl (0, i))
      rw [← hW0, ← hX0]
      exact congrArg (fun A : unitary (E →L[ℂ] E) => (A : E →L[ℂ] E) (e (.inl (0, i)))) heq
    have hcoef : Complex.exp ((delta i : ℂ) * Complex.I) =
        Complex.exp (((-delta i : ℝ) : ℂ) * Complex.I) := by
      simp only [Complex.ofReal_add, add_mul, Complex.exp_add] at hphase
      exact mul_left_cancel₀ (Complex.exp_ne_zero _) hphase
    have hz := phase_eq_zero_of_exp_eq_negative (delta i)
      ⟨(hδ i).1, (hδ i).2.trans (hθ i).2⟩ hcoef
    have hcanonical := hscalar i
    rw [hz] at hcanonical
    exact (phaseMinimum_eq_canonical_iff_le_criticalAngle p.toReal (theta i) hp1 hp2
      ⟨(hθ i).1.le, (hθ i).2⟩).mp hcanonical.symm
  · intro hcrit
    apply Subtype.ext
    let D := finiteCrossedDefectEquiv K L hKL
    exact (eq_canonicalRotation_of_isLocalMinOn_angles_le_critical_complex
      p hp hp1 hp2 K L U hUmap hWmin.isLocalMinOn hcrit D).trans
      (eq_canonicalRotation_of_isLocalMinOn_angles_le_critical_complex
        p hp hp1 hp2 K L V hVmap hXmin.isLocalMinOn hcrit D).symm

/-- There is exactly one unrestricted finite complex Schatten transport
minimizer if and only if every principal angle lies at or below the
critical angle. In particular, any right angle rules out uniqueness. -/
theorem schatten_transport_unique_minimizer_iff_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    (∃! U : unitary (E →L[ℂ] E),
      K.map (Unitary.linearIsometryEquiv U).toLinearMap = L ∧
      IsMinOn
        (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
        {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
        (U : E →L[ℂ] E)) ↔
      ∀ i : Fin (Module.finrank ℂ K), K.principalAngles L i ≤ criticalAngle p.toReal := by
  constructor
  · rintro ⟨W, _, huni⟩
    obtain ⟨U, V, hU, hV, heq⟩ :=
      exists_opposite_schatten_minimizers_complex p hp hp1 hp2 K L hKL
    exact heq.mp ((huni U hU).trans (huni V hV).symm)
  · exact existsUnique_schatten_minimizer_of_angles_le_critical_complex p hp hp1 hp2 K L hKL

/-- The uniqueness criterion in isometric-equivalence coordinates, with
the objective compared directly against every feasible transporter. -/
theorem schatten_transport_unique_minimizer_linearIsometryEquiv_iff_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    (∃! U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      ∀ V : E ≃ₗᵢ[ℂ] E, K.map V.toLinearMap = L →
        UnitarilyInvariantSeminorm.schatten ℂ E E p
            (LinearMap.id - U.toLinearMap) ^ p.toReal ≤
          UnitarilyInvariantSeminorm.schatten ℂ E E p
            (LinearMap.id - V.toLinearMap) ^ p.toReal) ↔
      ∀ i : Fin (Module.finrank ℂ K), K.principalAngles L i ≤ criticalAngle p.toReal := by
  let P (U : unitary (E →L[ℂ] E)) : Prop :=
    K.map (Unitary.linearIsometryEquiv U).toLinearMap = L ∧
      IsMinOn
        (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
        {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
        (U : E →L[ℂ] E)
  let Q (U : E ≃ₗᵢ[ℂ] E) : Prop := K.map U.toLinearMap = L ∧
    ∀ V : E ≃ₗᵢ[ℂ] E, K.map V.toLinearMap = L →
      UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - U.toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - V.toLinearMap) ^ p.toReal
  have hpred (U) : P U ↔ Q (Unitary.linearIsometryEquiv U) := by
    constructor
    · rintro ⟨hmap, hmin⟩
      refine ⟨hmap, ?_⟩
      intro V hV
      let V' := Unitary.linearIsometryEquiv.symm V
      have hVmap : K.map (Unitary.linearIsometryEquiv V').toLinearMap = L := by
        simpa only [V', MulEquiv.apply_symm_apply] using hV
      have hUcoe : (Unitary.linearIsometryEquiv U).toLinearMap =
          (U : E →L[ℂ] E).toLinearMap := rfl
      have hVcoe : V.toLinearMap = (V' : E →L[ℂ] E).toLinearMap := rfl
      rw [hUcoe, hVcoe]
      exact hmin ⟨V'.property, (map_eq_iff_conjugate_starProjection_complex K L V').mp hVmap⟩
    · rintro ⟨hmap, hmin⟩
      refine ⟨hmap, ?_⟩
      intro V hV
      let V' : unitary (E →L[ℂ] E) := ⟨V, hV.1⟩
      have hh := hmin (Unitary.linearIsometryEquiv V')
        ((map_eq_iff_conjugate_starProjection_complex K L V').mpr hV.2)
      have hUcoe : (Unitary.linearIsometryEquiv U).toLinearMap =
          (U : E →L[ℂ] E).toLinearMap := rfl
      have hVcoe : (Unitary.linearIsometryEquiv V').toLinearMap = V.toLinearMap := rfl
      rw [hUcoe, hVcoe] at hh
      exact hh
  have heq := Unitary.linearIsometryEquiv.toEquiv.existsUnique_congr hpred
  change (∃! U, Q U) ↔ _
  rw [← heq]
  exact schatten_transport_unique_minimizer_iff_complex p hp hp1 hp2 K L hKL

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
