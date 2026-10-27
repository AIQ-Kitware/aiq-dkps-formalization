/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenUniquenessThreshold
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCorrectionUniqueness

/-!
# Exact commutator criterion for unique Hilbert Schatten correction

For a unitary with Schatten commutator, the nearest unitary commuting
with a prescribed projection is unique exactly at or below the critical
commutator norm. No separate defect-balance hypothesis is needed: a
unique extended-gauge minimum has finite cost, so the classical compact
transport index obstruction vanishes automatically.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A closed commutator norm test is necessary and sufficient for a
unique nearest projection-commuting unitary. There is no separate
balance, separability, finite-rank or finite-candidate-cost assumption. -/
theorem existsUnique_nearest_schatten_commuting_unitary_iff_commutator
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E)
    (hcomm : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞) :
    (∃! C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) K.starProjection ∧
      ∀ W : E ≃ₗᵢ[ℂ] E, Commute (W : E →L[ℂ] E) K.starProjection →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            ((A : E →L[ℂ] E) - (W : E →L[ℂ] E))) ↔
      ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
        Real.sin (criticalAngle p.toReal) := by
  constructor
  · intro hunique
    let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
    have htransport := (Φ.existsUnique_correction_iff_transport K A).mp hunique
    obtain ⟨C, hC, huni⟩ := hunique
    have hfinite : Φ.gauge ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≠ ∞ := by
      intro htop
      have hall (W : E ≃ₗᵢ[ℂ] E) (hW : Commute (W : E →L[ℂ] E) K.starProjection) :
          Φ.gauge ((A : E →L[ℂ] E) - (W : E →L[ℂ] E)) = ∞ := by
        apply top_unique
        have h := hC.2 W hW
        change Φ.gauge ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
          Φ.gauge ((A : E →L[ℂ] E) - (W : E →L[ℂ] E)) at h
        rwa [htop] at h
      let I := LinearIsometryEquiv.refl ℂ E
      let N : E ≃ₗᵢ[ℂ] E := LinearIsometryEquiv.neg ℂ
      have hI : Commute (I : E →L[ℂ] E) K.starProjection := by
        change Commute 1 K.starProjection
        exact Commute.one_left _
      have hN : Commute (N : E →L[ℂ] E) K.starProjection := by
        ext x
        change -(K.starProjection x) = K.starProjection (-x)
        rw [map_neg]
      have hmin (W : E ≃ₗᵢ[ℂ] E) (hW : Commute (W : E →L[ℂ] E) K.starProjection) :
          ∀ V : E ≃ₗᵢ[ℂ] E, Commute (V : E →L[ℂ] E) K.starProjection →
            Φ.gauge ((A : E →L[ℂ] E) - (W : E →L[ℂ] E)) ≤
              Φ.gauge ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)) := by
        intro V hV
        rw [hall W hW, hall V hV]
      have heq : I = N := (huni I ⟨hI, hmin I hI⟩).trans (huni N ⟨hN, hmin N hN⟩).symm
      have hzero (x : E) : x = 0 := by
        have hx : x = -x := congrArg (fun U : E ≃ₗᵢ[ℂ] E => U x) heq
        have htwo : (2 : ℂ) • x = 0 := by
          rw [two_smul]
          exact add_eq_zero_iff_eq_neg.mpr hx
        exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero
      have hdiff : (A : E →L[ℂ] E) - (C : E →L[ℂ] E) = 0 := by
        ext x
        exact hzero _
      rw [hdiff, Φ.gauge_zero] at htop
      exact ENNReal.zero_ne_top htop
    let L := K.map A.toLinearMap
    let T := A.symm.trans C
    have hmap : L.map T.toLinearMap = K := by
      rw [K.map_correction_transport]
      exact (K.map_eq_self_iff_commute_starProjection C).mpr hC.1
    have hTfinite : Φ.gauge (1 - (T : E →L[ℂ] E)) ≠ ∞ := by
      rwa [← Φ.gauge_unitary_sub_eq_displacement A C]
    have hTc : IsCompactOperator (((T : E →L[ℂ] E) - 1) : E →L[ℂ] E) := by
      rw [← neg_sub 1 (T : E →L[ℂ] E)]
      exact (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
        p.toReal hp1.le _ hTfinite).neg
    obtain ⟨hcompact, hbalance⟩ :=
      (compact_transport_iff_compact_projection_sub_and_defect_balance L K).mp ⟨T, hmap, hTc⟩
    obtain ⟨J⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq
      L K hcompact hbalance
    have hD : Φ.gauge (L.starProjection - K.starProjection) ≠ ∞ := by
      rwa [Φ.gauge_projection_image_sub_eq_commutator K A]
    have htransport' : ∃! U : E ≃ₗᵢ[ℂ] E,
        U ∈ schattenHilbertTransportMinimizers p.toReal hp1.le L K := by
      simpa only [mem_schattenHilbertTransportMinimizers, L, Φ] using htransport
    have hgap := (schattenHilbertTransport_unique_minimizer_iff_projectionGap_of_defectEquiv
      p hp hp1 hp2 L K J hD).mp htransport'
    rw [Submodule.projectionGap_def, K.norm_projection_image_sub_eq_commutator A] at hgap
    exact hgap
  · exact exists_unique_nearest_schatten_commuting_unitary_of_commutator_le_critical
      p hp hp1 hp2 K A hcomm

/-- The exact correction uniqueness threshold as a closed-form scalar. -/
theorem existsUnique_nearest_schatten_commuting_unitary_iff_critical_norm
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E)
    (hcomm : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞) :
    (∃! C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) K.starProjection ∧
      ∀ W : E ≃ₗᵢ[ℂ] E, Commute (W : E →L[ℂ] E) K.starProjection →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            ((A : E →L[ℂ] E) - (W : E →L[ℂ] E))) ↔
      ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
        2 * Real.sqrt (p.toReal - 1) / p.toReal := by
  rw [existsUnique_nearest_schatten_commuting_unitary_iff_commutator p hp hp1 hp2 K A hcomm,
    sin_criticalAngle p.toReal hp1]

/-- The exact ambient transport uniqueness criterion needs no separate
defect-balance hypothesis. Above the threshold uniqueness fails even
when every feasible transporter has infinite Schatten displacement. -/
theorem schattenHilbertTransport_unique_minimizer_iff_projectionGap
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞) :
    (∃! U : E ≃ₗᵢ[ℂ] E,
      U ∈ schattenHilbertTransportMinimizers p.toReal hp1.le K L) ↔
      K.projectionGap L ≤ Real.sin (criticalAngle p.toReal) := by
  constructor
  · intro hunique
    obtain ⟨U, hU⟩ := hunique.exists
    have hmap := (mem_schattenHilbertTransportMinimizers _ _ _ _ U).mp hU |>.1
    have hLmap : L.map U.symm.toLinearMap = K :=
      (Submodule.map_symm_eq_iff U.toLinearEquiv).mpr hmap
    have hproj : (L.map U.symm.toLinearMap).starProjection = K.starProjection := by
      congr 1
    let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
    have hcomm : Φ.gauge ((U.symm : E →L[ℂ] E) * L.starProjection -
        L.starProjection * (U.symm : E →L[ℂ] E)) ≠ ∞ := by
      rw [← Φ.gauge_projection_image_sub_eq_commutator L U.symm, hproj]
      exact hD
    have htransport : ∃! T : E ≃ₗᵢ[ℂ] E,
        (L.map U.symm.toLinearMap).map T.toLinearMap = L ∧
          ∀ V : E ≃ₗᵢ[ℂ] E, (L.map U.symm.toLinearMap).map V.toLinearMap = L →
            Φ.gauge (1 - (T : E →L[ℂ] E)) ≤ Φ.gauge (1 - (V : E →L[ℂ] E)) := by
      simpa only [hLmap, mem_schattenHilbertTransportMinimizers, Φ] using hunique
    have hcorrection := (Φ.existsUnique_correction_iff_transport L U.symm).mpr htransport
    have hnorm := (existsUnique_nearest_schatten_commuting_unitary_iff_commutator
      p hp hp1 hp2 L U.symm hcomm).mp hcorrection
    rw [← L.norm_projection_image_sub_eq_commutator U.symm, hproj] at hnorm
    rwa [Submodule.projectionGap_def]
  · intro hgap
    have hc := criticalAngle_mem p.toReal hp1 hp2
    have hs1 : Real.sin (criticalAngle p.toReal) < 1 := by
      have h := Real.strictMonoOn_sin
        ⟨by linarith [hc.1, Real.pi_pos], hc.2.le⟩
        ⟨by linarith [Real.pi_pos], le_rfl⟩ hc.2
      simpa only [Real.sin_pi_div_two] using h
    have hacute : IsUniformlyAcute K L := hgap.trans_lt hs1
    have hz := halmosSourceDefect_eq_bot_of_isUniformlyAcute K L hacute
    have hz' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K L hacute
    let J := LinearIsometryEquiv.ofEq _ _ (hz.trans hz'.symm)
    exact (schattenHilbertTransport_unique_minimizer_iff_projectionGap_of_defectEquiv
      p hp hp1 hp2 K L J hD).mpr hgap

/-- The closed-form uniqueness threshold for every Schatten projection
pair, without a separate feasibility or index assumption. -/
theorem schattenHilbertTransport_unique_minimizer_iff_critical_norm
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞) :
    (∃! U : E ≃ₗᵢ[ℂ] E,
      U ∈ schattenHilbertTransportMinimizers p.toReal hp1.le K L) ↔
      K.projectionGap L ≤ 2 * Real.sqrt (p.toReal - 1) / p.toReal := by
  rw [schattenHilbertTransport_unique_minimizer_iff_projectionGap p hp hp1 hp2 K L hD,
    sin_criticalAngle p.toReal hp1]

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
