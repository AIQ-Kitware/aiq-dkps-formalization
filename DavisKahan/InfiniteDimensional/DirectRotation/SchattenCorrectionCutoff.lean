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
    have hfinite := Φ.gauge_unitary_sub_ne_top_of_unique_correction K A C hC huni
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

/-- Complete uniqueness criterion for an arbitrary unitary: Schatten
commutator membership and the closed critical norm bound are both
necessary and jointly sufficient. No compactness or feasibility is
assumed, and the objective retains its extended values. -/
theorem existsUnique_nearest_schatten_commuting_unitary_iff
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E) :
    (∃! C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) K.starProjection ∧
      ∀ W : E ≃ₗᵢ[ℂ] E, Commute (W : E →L[ℂ] E) K.starProjection →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            ((A : E →L[ℂ] E) - (W : E →L[ℂ] E))) ↔
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞ ∧
        ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
          2 * Real.sqrt (p.toReal - 1) / p.toReal := by
  constructor
  · intro hunique
    obtain ⟨C, hC, huni⟩ := hunique
    let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
    have hfinite := Φ.gauge_unitary_sub_ne_top_of_unique_correction K A C hC huni
    have hcomm := ne_top_of_le_ne_top hfinite
      (Φ.gauge_commutator_le_unitary_correction K A C hC.1)
    exact ⟨hcomm, (existsUnique_nearest_schatten_commuting_unitary_iff_critical_norm
      p hp hp1 hp2 K A hcomm).mp ⟨C, hC, huni⟩⟩
  · rintro ⟨hcomm, hnorm⟩
    exact (existsUnique_nearest_schatten_commuting_unitary_iff_critical_norm
      p hp hp1 hp2 K A hcomm).mpr hnorm

/-- Complete uniqueness criterion for arbitrary orthogonally
complemented projection pairs. Native Schatten membership is a
conclusion of uniqueness, not a standing assumption. This includes
noncompact pairs and pairs without a near-identity feasible transport. -/
theorem schattenHilbertTransport_unique_minimizer_iff
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃! U : E ≃ₗᵢ[ℂ] E,
      U ∈ schattenHilbertTransportMinimizers p.toReal hp1.le K L) ↔
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (K.starProjection - L.starProjection) ≠ ∞ ∧
        K.projectionGap L ≤ 2 * Real.sqrt (p.toReal - 1) / p.toReal := by
  constructor
  · intro hunique
    obtain ⟨U, hU⟩ := hunique.exists
    have hmap := (mem_schattenHilbertTransportMinimizers _ _ _ _ U).mp hU |>.1
    have hLmap : L.map U.symm.toLinearMap = K :=
      (Submodule.map_symm_eq_iff U.toLinearEquiv).mpr hmap
    have hproj : (L.map U.symm.toLinearMap).starProjection = K.starProjection := by
      congr 1
    let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
    have htransport : ∃! T : E ≃ₗᵢ[ℂ] E,
        (L.map U.symm.toLinearMap).map T.toLinearMap = L ∧
          ∀ V : E ≃ₗᵢ[ℂ] E, (L.map U.symm.toLinearMap).map V.toLinearMap = L →
            Φ.gauge (1 - (T : E →L[ℂ] E)) ≤ Φ.gauge (1 - (V : E →L[ℂ] E)) := by
      simpa only [hLmap, mem_schattenHilbertTransportMinimizers, Φ] using hunique
    have hcorrection := (Φ.existsUnique_correction_iff_transport L U.symm).mpr htransport
    have hcomm := ((existsUnique_nearest_schatten_commuting_unitary_iff
      p hp hp1 hp2 L U.symm).mp hcorrection).1
    have hD : Φ.gauge (K.starProjection - L.starProjection) ≠ ∞ := by
      rw [← Φ.gauge_projection_image_sub_eq_commutator L U.symm, hproj] at hcomm
      exact hcomm
    exact ⟨hD, (schattenHilbertTransport_unique_minimizer_iff_critical_norm
      p hp hp1 hp2 K L hD).mp hunique⟩
  · rintro ⟨hD, hnorm⟩
    exact (schattenHilbertTransport_unique_minimizer_iff_critical_norm
      p hp hp1 hp2 K L hD).mpr hnorm

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
