/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenSubcriticalTail
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenFiniteCorrection
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenGlobalLowerBound
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCanonical
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReducingSpectralTrace

/-!
# The exact unrestricted Schatten minimum for infinite-rank pairs

For `1<p<2`, optimize a finite sine spectral sector and retain the
canonical rotation on its subcritical infinite tail. The actual ambient
cost is the intrinsic scalar-phase minimum sum. The unrestricted lower
bound compares this construction with every ambient unitary transporter.
The optimizer differs from direct rotation by finite rank, even when
the projection difference and the optimizer's displacement have infinite rank.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance attainmentComapSubtypeProjection
    (K N : Submodule ℂ E) [K.HasOrthogonalProjection] [CompleteSpace N] :
    (K.comap N.subtype).HasOrthogonalProjection :=
  K.hasOrthogonalProjection_comap_subtype_of_complete N

/-- **Exact global attainment by a finite phase correction.** Given
an actual defect completion and a Schatten projection difference,
every positive subcritical sine cutoff yields a global minimizer.
It agrees with the completed direct rotation on the whole infinite
tail and differs from it by rank at most the finite cutoff dimension. -/
theorem exists_schatten_minimizer_by_finite_correction
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (criticalAngle p.toReal)) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let R := nonacuteDirectRotation K L J
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (∀ x ∈ Mᗮ, U x = R x) ∧
      (R.toLinearMap - U.toLinearMap).rank ≤ Module.finrank ℂ M ∧
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (U : E →L[ℂ] E)) ≠ ∞ ∧
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (1 - (U : E →L[ℂ] E)) ^ p.toReal =
        (∑' j, ENNReal.ofReal (phaseMinimum p.toReal
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            (1 - (U : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            (1 - (T : E →L[ℂ] E)) := by
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    p.toReal hp1.le (K.starProjection - L.starProjection) hD
  obtain ⟨hM, hK, hL, _⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  have hRM : ∀ x ∈ M, nonacuteDirectRotation K L J x ∈ M :=
    (sine_spectral_cutoff_isReducing_nonacuteDirectRotation K L J hcompact c hc).mem_invtSubmodule
  obtain ⟨W, U, _, hWcost, hUmap, _, hUtail, hRank, hfinite, hfull⟩ :=
    exists_schatten_phase_correction_on_finite_block p hp hp1.le K L M J hD hK hRM
  let K₀ := K.comap M.subtype
  let L₀ := L.comap M.subtype
  have hhead : (∑' k, ((1 - (W : M →L[ℂ] M)).singularValue k : ℝ≥0∞) ^ p.toReal) =
      ∑' j, ENNReal.ofReal (phaseMinimum p.toReal
        (Real.arcsin ((K₀.sinThetaMap L₀).singularValue j : ℝ))) := by
    have hlin : (1 - (W : M →L[ℂ] M)).toLinearMap = LinearMap.id - W.toLinearMap := rfl
    have hf : ENNReal.ofReal (phaseMinimum p.toReal 0) = 0 := by
      rw [phaseMinimum_zero_angle p.toReal hp1.le, ENNReal.ofReal_zero]
    rw [← OperatorIdealFamily.gauge_schatten_rpow p.toReal hp1.le,
      OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp, hlin, hWcost,
      OperatorIdealFamily.tsum_singularValue_penalty_eq_sum _
        (fun s => ENNReal.ofReal (phaseMinimum p.toReal (Real.arcsin (s : ℝ))))
        (by simpa only [NNReal.coe_zero, Real.arcsin_zero] using hf)]
    simp_rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]
    have hnonneg (i : Fin (Module.finrank ℂ K₀)) :
        0 ≤ phaseMinimum p.toReal (K₀.principalAngles L₀ i) :=
      phaseMinimum_nonneg _ _ hp1.le
        ⟨K₀.principalAngles_nonneg L₀ i, K₀.principalAngles_le_pi_div_two L₀ i⟩
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)]
    exact Submodule.sum_principalAngles_eq_sum_singularValues_arcsin K₀ L₀
      (fun t => ENNReal.ofReal (phaseMinimum p.toReal t)) hf
  have hcost : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (U : E →L[ℂ] E)) ^ p.toReal =
      ∑' j, ENNReal.ofReal (phaseMinimum p.toReal
        (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) := by
    rw [hfull, hhead,
      schatten_canonical_cutoff_tail_rpow_eq_phaseMinimum_sum p hp hp1 hp2
        K L J hcompact c hc hc1 hcrit,
      Submodule.tsum_sine_penalty_eq_add_of_isReducing K L M hcompact hK hL
        (fun s => ENNReal.ofReal (phaseMinimum p.toReal (Real.arcsin (s : ℝ))))
        (by simp only [NNReal.coe_zero, Real.arcsin_zero,
          phaseMinimum_zero_angle p.toReal hp1.le, ENNReal.ofReal_zero])]
  refine ⟨U, hUmap, hUtail, hRank, hfinite, hcost, ?_⟩
  intro T hT
  apply (ENNReal.rpow_le_rpow_iff (zero_lt_one.trans hp1)).mp
  rw [hcost]
  exact sine_phaseMinimum_sum_le_schatten_transport p hp hp1.le hp2 K L T hT

/-- **Unrestricted infinite-rank Schatten attainment for `1<p<2`.**
A Schatten projection difference and equality of its finite crossed
defect dimensions give an actual finite-cost global minimizer, with
exact intrinsic angle cost. No ambient separability or rank restriction
is imposed, and every complex unitary transporter is a competitor. -/
theorem exists_unitary_minimizing_schatten_transport_of_projection_sub_ne_top
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (hbalance : Module.finrank ℂ (halmosSourceDefect K L) =
      Module.finrank ℂ (halmosTargetDefect K L)) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (U : E →L[ℂ] E)) ≠ ∞ ∧
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (1 - (U : E →L[ℂ] E)) ^ p.toReal =
        (∑' j, ENNReal.ofReal (phaseMinimum p.toReal
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            (1 - (U : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            (1 - (T : E →L[ℂ] E)) := by
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    p.toReal hp1.le (K.starProjection - L.starProjection) hD
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq K L
    hcompact hbalance
  let c := Real.sin (criticalAngle p.toReal) / 2
  have hangle := criticalAngle_mem p.toReal hp1 hp2
  have hsin : 0 < Real.sin (criticalAngle p.toReal) :=
    Real.sin_pos_of_pos_of_lt_pi hangle.1 (by linarith [hangle.2, Real.pi_pos])
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : c < 1 := by dsimp only [c]; linarith [Real.sin_le_one (criticalAngle p.toReal)]
  have hcrit : c ≤ Real.sin (criticalAngle p.toReal) := by dsimp only [c]; linarith
  obtain ⟨U, hmap, _, _, hfinite, hcost, hmin⟩ :=
    exists_schatten_minimizer_by_finite_correction p hp hp1 hp2 K L J hD c hc hc1 hcrit
  exact ⟨U, hmap, hfinite, hcost, hmin⟩

/-- At the exact critical sine cutoff, a global optimizer has an
explicit finite update budget controlled by the native projection
difference cost. Critical eigenspaces need no phase correction. -/
theorem exists_schatten_minimizer_with_critical_rank_budget
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞) :
    ∃ U : E ≃ₗᵢ[ℂ] E, ∃ n : ℕ,
      K.map U.toLinearMap = L ∧
      ((nonacuteDirectRotation K L J).toLinearMap - U.toLinearMap).rank ≤ n ∧
      (n : ℝ≥0∞) * ENNReal.ofReal (Real.sin (criticalAngle p.toReal)) ^ p.toReal ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (K.starProjection - L.starProjection) ^ p.toReal ∧
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (U : E →L[ℂ] E)) ≠ ∞ ∧
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (1 - (U : E →L[ℂ] E)) ^ p.toReal =
        (∑' j, ENNReal.ofReal (phaseMinimum p.toReal
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            (1 - (U : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            (1 - (T : E →L[ℂ] E)) := by
  let c := Real.sin (criticalAngle p.toReal)
  have hangle := criticalAngle_mem p.toReal hp1 hp2
  have hc : 0 < c := Real.sin_pos_of_pos_of_lt_pi hangle.1
    (by linarith [hangle.2, Real.pi_pos])
  have hc1 : c < 1 := by
    have h := Real.strictMonoOn_sin
      ⟨by linarith [hangle.1, Real.pi_pos], hangle.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hangle.2
    simpa only [Real.sin_pi_div_two] using h
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    p.toReal hp1.le (K.starProjection - L.starProjection) hD
  obtain ⟨U, hmap, _, hRank, hfinite, hcost, hmin⟩ :=
    exists_schatten_minimizer_by_finite_correction p hp hp1 hp2 K L J hD c hc hc1 le_rfl
  exact ⟨U, Module.finrank ℂ (eigenSpan (K.sinAngleOperator L) (Set.Ioi c)), hmap, hRank,
    finrank_sine_spectral_cutoff_mul_rpow_le_schatten_projection_sub p.toReal hp1.le
      K L hcompact c hc, hfinite, hcost, hmin⟩

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

namespace TauCeti.DavisKahan.InfiniteDimensional

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Schatten attainment at every finite exponent greater than one.**
Balanced Schatten projection pairs admit a finite-cost global minimizer.
Below two this uses the finite phase correction; at and above two the
canonical rotation itself is optimal. -/
theorem exists_unitary_minimizing_schatten_transport_of_projection_sub_ne_top
    (p : ℝ) (hp : 1 < p)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : (OperatorIdealFamily.schatten ℂ p hp.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (hbalance : Module.finrank ℂ (halmosSourceDefect K L) =
      Module.finrank ℂ (halmosTargetDefect K L)) :
    ∃ R : E ≃ₗᵢ[ℂ] E, K.map R.toLinearMap = L ∧
      (OperatorIdealFamily.schatten ℂ p hp.le).gauge (1 - (R : E →L[ℂ] E)) ≠ ∞ ∧
      ∀ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ p hp.le).gauge (1 - (R : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p hp.le).gauge (1 - (U : E →L[ℂ] E)) := by
  by_cases hp2 : 2 ≤ p
  · have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p
      hp.le (K.starProjection - L.starProjection) hD
    obtain ⟨J⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq K L hcompact hbalance
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
        unitary (E →L[ℂ] E))
    refine ⟨R, ?_, (gauge_nonacuteDirectRotation_ne_top_iff_projection_sub
      (OperatorIdealFamily.schatten ℂ p hp.le) K L J).mpr hD, ?_⟩
    · apply (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
      exact nonacuteDirectRotation_reflection_intertwines K L J
    · intro U hmap
      exact schatten_nonacuteDirectRotation_le_transport p hp2 K L J U hmap
  · let q := ENNReal.ofReal p
    have hqr : q.toReal = p := ENNReal.toReal_ofReal (by linarith)
    let : Fact (1 ≤ q) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    have hq1 : 1 < q.toReal := by rwa [hqr]
    have hq2 : q.toReal < 2 := by rw [hqr]; exact lt_of_not_ge hp2
    have hDq : (OperatorIdealFamily.schatten ℂ q.toReal hq1.le).gauge
        (K.starProjection - L.starProjection) ≠ ∞ := by simpa only [hqr] using hD
    obtain ⟨U, hmap, hfinite, _, hmin⟩ :=
      SchattenPhaseTransition.exists_unitary_minimizing_schatten_transport_of_projection_sub_ne_top
        q ENNReal.ofReal_ne_top hq1 hq2 K L hDq hbalance
    refine ⟨U, hmap, ?_, ?_⟩
    · simpa only [hqr] using hfinite
    · simpa only [hqr] using hmin

end TauCeti.DavisKahan.InfiniteDimensional
