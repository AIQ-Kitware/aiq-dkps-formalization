/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCorrectionClassification

/-!
# A closed commutator certificate for unique optimal symmetry correction

When a unitary's commutator with a prescribed orthogonal projection has
norm at most the critical sine, every nearest commuting unitary is the
canonical polar correction. A Schatten commutator suffices for feasibility:
the norm bound automatically removes the pair-index obstruction.
The threshold includes equality, arbitrary Hilbert dimension and all
zero or repeated angles. No numerical or physical implementation claim
is made by this deterministic operator theorem.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem sin_criticalAngle_lt_one (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    Real.sin (criticalAngle p) < 1 := by
  have hc := criticalAngle_mem p hp1 hp2
  have h := Real.strictMonoOn_sin
    ⟨by linarith [hc.1, Real.pi_pos], hc.2.le⟩
    ⟨by linarith [Real.pi_pos], le_rfl⟩ hc.2
  simpa only [Real.sin_pi_div_two] using h

/-- Every nearest commuting unitary is the explicit canonical polar
correction when the actual commutator norm obeys the closed critical
bound. Finite candidate distance and defect balance are not assumed. -/
theorem eq_canonical_correction_of_schatten_minimal_of_commutator_le_critical
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (hcomm : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hnorm : ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
      Real.sin (criticalAngle p.toReal))
    (hmin : ∀ W : E ≃ₗᵢ[ℂ] E, Commute (W : E →L[ℂ] E) K.starProjection →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          ((A : E →L[ℂ] E) - (W : E →L[ℂ] E))) :
    (C : E →L[ℂ] E) = spectraCanonicalPolarFactor (K.map A.toLinearMap) K ∘L
      (A : E →L[ℂ] E) := by
  let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
  let T := A.symm.trans C
  have hsmall := hnorm.trans_lt (sin_criticalAngle_lt_one p.toReal hp1 hp2)
  obtain ⟨C₀, hC₀, hfinite₀, _⟩ :=
    exists_nearest_schatten_commuting_unitary_of_commutator_norm_lt_one
      p.toReal hp1 K A hsmall hcomm
  have hfinite : Φ.gauge (1 - (T : E →L[ℂ] E)) ≠ ∞ := by
    rw [← Φ.gauge_unitary_sub_eq_displacement A C]
    exact ne_top_of_le_ne_top hfinite₀ (hmin C₀ hC₀)
  have hmap : (K.map A.toLinearMap).map T.toLinearMap = K := by
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection C).mpr hC
  have hgap : (K.map A.toLinearMap).projectionGap K ≤ Real.sin (criticalAngle p.toReal) := by
    rw [Submodule.projectionGap_def]
    rwa [K.norm_projection_image_sub_eq_commutator A]
  have hcanonical := eq_canonicalPolarFactor_of_schatten_minimal_of_gap_le_critical
    p hp hp1 hp2 (K.map A.toLinearMap) K T hmap hfinite
      ((Φ.gauge_correction_isMin_iff_transport_isMin K A C).mp hmin) hgap
  calc
    (C : E →L[ℂ] E) = (T : E →L[ℂ] E) ∘L (A : E →L[ℂ] E) := by
      ext x
      exact (congrArg C (A.symm_apply_apply x)).symm
    _ = _ := congrArg (fun B : E →L[ℂ] E => B ∘L (A : E →L[ℂ] E)) hcanonical

/-- A Schatten commutator and the closed critical norm bound certify
existence and uniqueness of the nearest commuting unitary, without a
separate rank-balance hypothesis. The optimum compares with all ambient
commuting unitaries, including those at infinite Schatten distance. -/
theorem exists_unique_nearest_schatten_commuting_unitary_of_commutator_le_critical
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E)
    (hcomm : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hnorm : ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
      Real.sin (criticalAngle p.toReal)) :
    ∃! C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) K.starProjection ∧
      ∀ W : E ≃ₗᵢ[ℂ] E, Commute (W : E →L[ℂ] E) K.starProjection →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            ((A : E →L[ℂ] E) - (W : E →L[ℂ] E)) := by
  obtain ⟨C, hC, _, hCmin⟩ := exists_nearest_schatten_commuting_unitary_of_commutator_norm_lt_one
    p.toReal hp1 K A (hnorm.trans_lt (sin_criticalAngle_lt_one p.toReal hp1 hp2)) hcomm
  refine ⟨C, ⟨hC, hCmin⟩, ?_⟩
  intro V hV
  have hCeq := eq_canonical_correction_of_schatten_minimal_of_commutator_le_critical
    p hp hp1 hp2 K A C hC hcomm hnorm hCmin
  have hVeq := eq_canonical_correction_of_schatten_minimal_of_commutator_le_critical
    p hp hp1 hp2 K A V hV.1 hcomm hnorm hV.2
  ext x
  exact congrArg (fun B : E →L[ℂ] E => B x) (hVeq.trans hCeq.symm)

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
