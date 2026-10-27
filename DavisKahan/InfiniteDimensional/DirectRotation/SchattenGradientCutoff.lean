/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenStationarity
public import ForTauCeti.Analysis.InnerProductSpace.SchattenLocalRestriction
public import ForTauCeti.Analysis.InnerProductSpace.Projection.AnticommutingModulus
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenNonacuteClassification
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenNativeLocalGlobal

/-!
# Finite spectral sectors of every Hilbert-space Schatten optimizer

Constrained stationarity makes the gradient modulus commute with the
source projection. Its positive spectral cutoffs are finite and reduce
the source, target and actual minimizing unitary. Their actual unitary
restrictions are unrestricted finite-dimensional global minimizers.
No block or canonical-tail assumption is supplied about the optimizer.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Actual finite spectral classification sectors for every
optimizer.** Every positive gradient-modulus cutoff reduces both
projections and the minimizing unitary, carries its actual forward and
inverse restrictions, and inherits unrestricted finite optimality.
Only the gradient, rather than displacement, is bounded on its tail. -/
theorem exists_locally_minimizing_restriction_on_gradient_cutoff_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U)
    (ε : ℝ) (hε : 0 < ε) :
    let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
    let M := eigenSpan G.modulus (Set.Ioi ε)
    ∃ hM : FiniteDimensional ℂ M,
      let _ : FiniteDimensional ℂ M := hM
      M.IsReducing K.starProjection.toLinearMap ∧
      M.IsReducing L.starProjection.toLinearMap ∧ M.IsReducing U.toLinearMap ∧
      ‖G ∘L Mᗮ.subtypeL‖ ≤ ε ∧
      ∃ V : M ≃ₗᵢ[ℂ] M,
        (∀ x : M, (V x : E) = U x) ∧ (∀ x : M, (V.symm x : E) = U.symm x) ∧
        (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (1 - (V : M →L[ℂ] M)) ≠ ∞ ∧
        IsLocalMinOn
          (fun W : M ≃ₗᵢ[ℂ] M => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            (1 - (W : M →L[ℂ] M)))
          {W | (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype} V := by
  dsimp only
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let A := G.modulus
  let M := eigenSpan A (Set.Ioi ε)
  let : IsStarNormal (U : E →L[ℂ] E) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm U).property
  have hG : IsSelfAdjoint G := isSelfAdjoint_schattenUnitaryGradient _ _
  have hUfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((U : E →L[ℂ] E) - 1) ≠ ∞ := by
    rw [← neg_sub 1 (U : E →L[ℂ] E), OperatorIdealFamily.gauge_neg]
    exact hfinite
  have hGc : IsCompactOperator G := isCompactOperator_schattenUnitaryGradient p.toReal hp1 U
    (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le _ hUfinite)
  have hAc : IsCompactOperator A := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hseq : A.singularValue = G.singularValue :=
      funext (fun n => ContinuousLinearMap.singularValue_modulus G n)
    rw [hseq]
    exact hGc.tendsto_singularValue
  have hAs : IsSelfAdjoint A := G.isSelfAdjoint_modulus
  have hM : FiniteDimensional ℂ M :=
    finiteDimensional_eigenSpan hAc hAs hε (fun _ hs => hs.le)
  let : FiniteDimensional ℂ M := hM
  have hPA : Commute K.starProjection A :=
    K.commute_starProjection_modulus_of_reflection_conjugate_eq_neg G hG
      (gradient_reflection_conjugate_eq_neg_of_schatten_isLocalMinOn_complex p hp hp1 K L U hmap hfinite hmin)
  have hK : M.IsReducing K.starProjection.toLinearMap := by
    apply (K.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule M).mpr
    exact eigenSpan_invariant_of_commute A K.starProjection hPA _
  have hUG : Commute (U : E →L[ℂ] E) G := (commute_schattenUnitaryGradient p.toReal _).symm
  have hUA : Commute (U : E →L[ℂ] E) A := by
    apply ContinuousLinearMap.commute_modulus_of_commute
    change Commute (U : E →L[ℂ] E) (star G * G)
    rw [hG.star_eq]
    exact hUG.mul_right hUG
  have hUM : ∀ x ∈ M, U x ∈ M := eigenSpan_invariant_of_commute A _ hUA _
  obtain ⟨_, _, _, hUred⟩ := U.exists_restriction_of_finite_invariant M hUM
  obtain ⟨V, hV, hlocal, hVfinite, hVmin⟩ := exists_schatten_locally_minimizing_finite_restriction p.toReal hp1.le
    K L M U hmap hfinite hmin hK hUM
  have hL : M.IsReducing L.starProjection.toLinearMap := by
    apply (L.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule M).mpr
    intro x hx
    change L.starProjection x ∈ M
    have h := K.starProjection_map_mem_of_isometry_restriction M U V hV
      hK.mem_invtSubmodule x hx
    simpa only [hmap] using h
  refine ⟨hM, hK, hL, hUred, ?_, V, hV, ?_, hlocal, hVfinite, hVmin⟩
  · have htail : ‖A ∘L Mᗮ.subtypeL‖ ≤ ε :=
      norm_comp_orthogonal_eigenSpan_le hAc hAs G.isPositive_modulus.re_inner_nonneg_left
        hε.le (fun _ hs => hs)
    apply ContinuousLinearMap.opNorm_le_bound _ hε.le
    intro x
    change ‖G (x : E)‖ ≤ ε * ‖x‖
    calc
      _ = ‖A (x : E)‖ := (G.norm_modulus_apply (x : E)).symm
      _ ≤ ‖A ∘L Mᗮ.subtypeL‖ * ‖x‖ := (A ∘L Mᗮ.subtypeL).le_opNorm x
      _ ≤ _ := mul_le_mul_of_nonneg_right htail (norm_nonneg x)
  · intro x
    apply U.injective
    rw [← hV, V.apply_symm_apply, U.apply_symm_apply]

/-- Global minimality supplies finite global cutoffs for every `p>1`.
This retains the broader exponent scope of the established endpoint. -/
theorem exists_minimizing_restriction_on_gradient_cutoff
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E)))
    (ε : ℝ) (hε : 0 < ε) :
    let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
    let M := eigenSpan G.modulus (Set.Ioi ε)
    ∃ hM : FiniteDimensional ℂ M,
      let _ : FiniteDimensional ℂ M := hM
      M.IsReducing K.starProjection.toLinearMap ∧
      M.IsReducing L.starProjection.toLinearMap ∧ M.IsReducing U.toLinearMap ∧
      ‖G ∘L Mᗮ.subtypeL‖ ≤ ε ∧
      ∃ V : M ≃ₗᵢ[ℂ] M,
        (∀ x : M, (V x : E) = U x) ∧ (∀ x : M, (V.symm x : E) = U.symm x) ∧
        (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
        ∀ W : M ≃ₗᵢ[ℂ] M,
          (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
          UnitarilyInvariantSeminorm.schatten ℂ M M p (LinearMap.id - V.toLinearMap) ^ p.toReal ≤
            UnitarilyInvariantSeminorm.schatten ℂ M M p
              (LinearMap.id - W.toLinearMap) ^ p.toReal := by
  dsimp only
  obtain ⟨hM, hK, hL, hUred, htail, V, hV, hVi, hlocal, _, _⟩ :=
    exists_locally_minimizing_restriction_on_gradient_cutoff_complex p hp hp1 K L U hmap hfinite
      (show IsMinOn
        (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U
        from fun T hT => hmin T hT).isLocalMinOn ε hε
  let M := eigenSpan (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).modulus (Set.Ioi ε)
  let : FiniteDimensional ℂ M := hM
  obtain ⟨V', hV', _, hVmin⟩ := exists_schatten_minimizing_finite_restriction p.toReal hp1.le
    K L M U hmap hfinite hmin hK hUred.mem_invtSubmodule
  have heq : V' = V := by
    ext x
    exact (hV' x).trans (hV x).symm
  subst V'
  refine ⟨hM, hK, hL, hUred, htail, V, hV, hVi, hlocal, ?_⟩
  intro W hW
  have h := ENNReal.rpow_le_rpow (hVmin W hW) (zero_lt_one.trans hp1).le
  rw [OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp,
      OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Every finite-cost local minimum for `1<p<2` has finite globally
minimizing gradient cutoffs, with actual forward and inverse actions. -/
theorem exists_minimizing_restriction_on_gradient_cutoff_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U)
    (ε : ℝ) (hε : 0 < ε) :
    let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
    let M := eigenSpan G.modulus (Set.Ioi ε)
    ∃ hM : FiniteDimensional ℂ M,
      let _ : FiniteDimensional ℂ M := hM
      M.IsReducing K.starProjection.toLinearMap ∧
      M.IsReducing L.starProjection.toLinearMap ∧ M.IsReducing U.toLinearMap ∧
      ‖G ∘L Mᗮ.subtypeL‖ ≤ ε ∧
      ∃ V : M ≃ₗᵢ[ℂ] M,
        (∀ x : M, (V x : E) = U x) ∧ (∀ x : M, (V.symm x : E) = U.symm x) ∧
        (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
        ∀ W : M ≃ₗᵢ[ℂ] M,
          (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
          UnitarilyInvariantSeminorm.schatten ℂ M M p (LinearMap.id - V.toLinearMap) ^ p.toReal ≤
            UnitarilyInvariantSeminorm.schatten ℂ M M p
              (LinearMap.id - W.toLinearMap) ^ p.toReal := by
  dsimp only
  obtain ⟨hM, hK, hL, hUred, htail, V, hV, hVi, hlocal, _, hVmin⟩ :=
    exists_locally_minimizing_restriction_on_gradient_cutoff_complex p hp hp1 K L U hmap hfinite hmin ε hε
  let M := eigenSpan (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).modulus (Set.Ioi ε)
  let : FiniteDimensional ℂ M := hM
  exact ⟨hM, hK, hL, hUred, htail, V, hV, hVi, hlocal,
    schatten_power_isMin_of_isLocalMinOn_complex p hp hp1 hp2
      (K.comap M.subtype) (L.comap M.subtype) V hlocal hVmin⟩

/-- Every positive gradient cutoff of every ambient global optimizer
has the complete compatible phase-projection and right-defect normal
form. The finite carrier and its source rank balance are proved, rather
than supplied as assumptions about the optimizer. -/
theorem exists_phase_and_defect_on_gradient_cutoff_of_schatten_minimal
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E)))
    (ε : ℝ) (hε : 0 < ε) :
    let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
    let M := eigenSpan G.modulus (Set.Ioi ε)
    ∃ hM : FiniteDimensional ℂ M,
      let _ : FiniteDimensional ℂ M := hM
      let K₀ := K.comap M.subtype
      let L₀ := L.comap M.subtype
      ∃ (V : M ≃ₗᵢ[ℂ] M) (hKL : Module.finrank ℂ K₀ = Module.finrank ℂ L₀),
        (∀ x : M, (V x : E) = U x) ∧ K₀.map V.toLinearMap = L₀ ∧
        let R := Unitary.linearIsometryEquiv
          (⟨nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL),
            nonacuteDirectRotation_mem_unitary K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL)⟩ :
              unitary (M →L[ℂ] M))
        let C := Proposition35.section3CosAngleOperator K₀ L₀
        let F := schattenPhaseFactor p.toReal C
        ∃ P : M →L[ℂ] M, IsStarProjection P ∧ Commute P (R : M →L[ℂ] M) ∧
          (∀ x, P (K₀.reflection x) = K₀.reflection (P x)) ∧
          ∃ D : halmosSourceDefect K₀ L₀ ≃ₗᵢ[ℂ] halmosTargetDefect K₀ L₀,
            (∀ x : halmosSourceDefect K₀ L₀, V x = (D x : M)) ∧
            (∀ y : halmosTargetDefect K₀ L₀, V y = (D.symm y : M)) ∧
            C * (V.trans R.symm : M →L[ℂ] M) = C * (F * P + star F * (1 - P)) := by
  dsimp only
  obtain ⟨hM, _, _, _, _, V, hV, _, hlocal, hVmin⟩ :=
    exists_minimizing_restriction_on_gradient_cutoff p hp hp1 K L U hmap hfinite hmin ε hε
  let M := eigenSpan (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).modulus (Set.Ioi ε)
  let : FiniteDimensional ℂ M := hM
  have hdim : Module.finrank ℂ (K.comap M.subtype) = Module.finrank ℂ (L.comap M.subtype) := by
    have h := V.toLinearEquiv.finrank_map_eq (K.comap M.subtype)
    rw [hlocal] at h
    exact h.symm
  refine ⟨hM, V, hdim, hV, hlocal, ?_⟩
  exact (schatten_transport_isMin_iff_phase_and_defect_complex
    p hp hp1 hp2 (K.comap M.subtype) (L.comap M.subtype) hdim V hlocal).mp hVmin

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
