/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierOptimizerTail
public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierGlobalAttainment
public import ForTauCeti.Analysis.InnerProductSpace.UnitaryTailAgreement

/-!
# Every complex Hilbert-space Charbonnier optimizer

Under the exact finite-cost feasibility conditions, an ambient unitary
minimizes the native smoothed trace precisely when it is canonical on
the infinite inactive tail and its actual finite active restriction has
the complete phase/defect form. Finite cost and block preservation are
conclusions, not hypotheses on the unitary being classified.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Global minimality is exactly canonical inactive action together with
unrestricted finite minimality on the actual active sine sector. The
ambient competitors need not preserve either sector. -/
theorem charbonnier_minimal_iff_canonical_tail_finite_minimal_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (smoothedCriticalAngle tau))
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let _ : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
      (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2 (by norm_num)
        (K.starProjection - L.starProjection) hD) c hc).1
    (∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau) ↔
      (∀ x ∈ Mᗮ, U x = nonacuteDirectRotation K L J x) ∧
      ∃ V : M ≃ₗᵢ[ℂ] M,
        (∀ x : M, (V x : E) = U x) ∧
        (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
        ∀ W : M ≃ₗᵢ[ℂ] M,
          (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
          smoothedDisplacementCost tau V.toLinearMap ≤
            smoothedDisplacementCost tau W.toLinearMap := by
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) (K.starProjection - L.starProjection) hD
  obtain ⟨hM, hK, _, _⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  have hRred : M.IsReducing R.toLinearMap :=
    sine_spectral_cutoff_isReducing_nonacuteDirectRotation K L J hcompact c hc
  obtain ⟨T, hTmap, hTtail, _, hTfinite, _, hTmin⟩ :=
    exists_charbonnier_minimizer_by_finite_correction tau hτ K L J hD c hc hc1 hcrit
  have hcost (W : M ≃ₗᵢ[ℂ] M) :
      (1 - (W : M →L[ℂ] M)).charbonnierCost tau =
        ENNReal.ofReal (smoothedDisplacementCost tau W.toLinearMap) := by
    rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
    rfl
  have hnonneg (W : M ≃ₗᵢ[ℂ] M) : 0 ≤ smoothedDisplacementCost tau W.toLinearMap := by
    unfold smoothedDisplacementCost
    apply Finset.sum_nonneg
    intro i _
    exact sub_nonneg.mpr (Real.le_sqrt_of_sq_le
      (by nlinarith [sq_nonneg ((LinearMap.id - W.toLinearMap).singularValues i)]))
  constructor
  · intro hmin
    have hfinite := ne_top_of_le_ne_top hTfinite (hmin T hTmap)
    have htail := apply_eq_nonacuteDirectRotation_on_inactive_tail_of_charbonnier_minimal_complex
      tau hτ K L J hD c hc hc1 hcrit U hmap hfinite hmin
    have hUred : M.IsReducing U.toLinearMap := U.isReducing_of_eq_on_orthogonal R M hRred htail
    obtain ⟨V, hV, hlocal, hVmin⟩ := exists_charbonnier_minimizing_finite_restriction
      tau hτ K L M U hmap hfinite hmin hK hUred.mem_invtSubmodule
    refine ⟨htail, V, hV, hlocal, ?_⟩
    intro W hW
    have h := hVmin W hW
    rw [hcost, hcost] at h
    exact (ENNReal.ofReal_le_ofReal_iff (hnonneg W)).mp h
  · rintro ⟨htail, V, hV, _, hVmin⟩
    have hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞ := by
      apply (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mpr
      exact ContinuousLinearMap.gauge_schatten_displacement_ne_top_of_finite_restriction_and_ideal_tail
        2 (by norm_num) M U (nonacuteDirectRotation K L J) V hV htail
        ((gauge_nonacuteDirectRotation_ne_top_iff_projection_sub
          (OperatorIdealFamily.schatten ℂ 2 (by norm_num)) K L J).mpr hD)
    have hTred : M.IsReducing T.toLinearMap := T.isReducing_of_eq_on_orthogonal R M hRred hTtail
    apply (charbonnier_minimal_iff_restriction_of_minimizing_reference_tail tau hτ
      K L M U T hmap hTmap hfinite hTmin hK hTred.mem_invtSubmodule
      (fun x hx => (htail x hx).trans (hTtail x hx).symm) V hV).mpr
    intro W hW
    rw [hcost, hcost]
    exact ENNReal.ofReal_le_ofReal (hVmin W hW)

/-- **Complete unrestricted Hilbert-space smoothed classification.**
All phase choices, repeated angles and right-angle defect isometries
occur on a finite active sector. The defect isometry is uniquely
recovered from the optimizer. All inactive ambient action is canonical.
There is no finite-cost or block-form hypothesis on the candidate. -/
theorem charbonnier_transport_isMin_iff_canonical_tail_phase_and_defect_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (smoothedCriticalAngle tau))
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let _ : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
      (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2 (by norm_num)
        (K.starProjection - L.starProjection) hD) c hc).1
    let K₀ := K.comap M.subtype
    let L₀ := L.comap M.subtype
    (∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau) ↔
      (∀ x ∈ Mᗮ, U x = nonacuteDirectRotation K L J x) ∧
      ∃ (V : M ≃ₗᵢ[ℂ] M) (hKL : Module.finrank ℂ K₀ = Module.finrank ℂ L₀),
        (∀ x : M, (V x : E) = U x) ∧ K₀.map V.toLinearMap = L₀ ∧
        let R₀ := Unitary.linearIsometryEquiv
          (⟨nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL),
            nonacuteDirectRotation_mem_unitary K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL)⟩ :
              unitary (M →L[ℂ] M))
        let C₀ := Proposition35.section3CosAngleOperator K₀ L₀
        let F₀ := weightedPhaseFactor (smoothingRadius tau) (smoothingRadius tau)⁻¹ C₀
        (∃! D : halmosSourceDefect K₀ L₀ ≃ₗᵢ[ℂ] halmosTargetDefect K₀ L₀,
          (∀ x : halmosSourceDefect K₀ L₀, V x = (D x : M)) ∧
          (∀ y : halmosTargetDefect K₀ L₀, V y = (D.symm y : M))) ∧
        ∃ P : M →L[ℂ] M, IsStarProjection P ∧ Commute P (R₀ : M →L[ℂ] M) ∧
          (∀ x, P (K₀.reflection x) = K₀.reflection (P x)) ∧
          (∀ x, C₀ x = 0 → P x = 0) ∧
          C₀ * (R₀.trans V.symm : M →L[ℂ] M) = C₀ * (F₀ * P + star F₀ * (1 - P)) := by
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  let : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
    (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2 (by norm_num)
      (K.starProjection - L.starProjection) hD) c hc).1
  have hiff := charbonnier_minimal_iff_canonical_tail_finite_minimal_complex
    tau hτ K L J hD c hc hc1 hcrit U hmap
  dsimp only at hiff
  refine hiff.trans ?_
  constructor
  · rintro ⟨htail, V, hV, hlocal, hVmin⟩
    have hdim : Module.finrank ℂ (K.comap M.subtype) =
        Module.finrank ℂ (L.comap M.subtype) := by
      have h := V.toLinearEquiv.finrank_map_eq (K.comap M.subtype)
      rw [hlocal] at h
      exact h.symm
    exact ⟨htail, V, hdim, hV, hlocal,
      (smoothed_transport_isMin_iff_phase_and_defect_equiv_complex tau hτ
        (K.comap M.subtype) (L.comap M.subtype) hdim V hlocal).mp hVmin⟩
  · rintro ⟨htail, V, hdim, hV, hlocal, hphase⟩
    exact ⟨htail, V, hV, hlocal,
      (smoothed_transport_isMin_iff_phase_and_defect_equiv_complex tau hτ
        (K.comap M.subtype) (L.comap M.subtype) hdim V hlocal).mpr hphase⟩

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
