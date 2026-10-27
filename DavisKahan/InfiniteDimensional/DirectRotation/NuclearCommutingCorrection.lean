/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenNuclearEndpoint
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCommutingCorrection
public import DavisKahan.InfiniteDimensional.DirectRotation.NuclearUniqueness

/-!
# Exact nuclear correction to a projection-preserving unitary

A trace-class commutator and balanced image/source crossed defects give
an actual nearest commuting unitary. Its exact nuclear distance is the
nuclear commutator cost. This includes genuinely infinite-rank data and
all ambient competitors. A commutator norm below one eliminates the
index obstruction, without requiring finite rank or a spectral cutoff.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Exact nearest commuting unitary in nuclear distance.** The native
commutator lower bound is attained over every ambient commuting unitary
when the commutator is trace class and the image/source defects balance.
The construction is the explicit nuclear phase transport followed by A. -/
theorem exists_nearest_nuclear_commuting_unitary_complex
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E)
    (hcomm : (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hbalance : Module.finrank ℂ (halmosSourceDefect (K.map A.toLinearMap) K) =
      Module.finrank ℂ (halmosTargetDefect (K.map A.toLinearMap) K)) :
    ∃ C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) K.starProjection ∧
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
        ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≠ ∞ ∧
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
          ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) =
        (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
          ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ∧
      ∀ V : E ≃ₗᵢ[ℂ] E, Commute (V : E →L[ℂ] E) K.starProjection →
        (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
            ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
            ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)) := by
  let Φ := OperatorIdealFamily.schatten ℂ 1 (by norm_num)
  have hD : Φ.gauge ((K.map A.toLinearMap).starProjection - K.starProjection) ≠ ∞ := by
    rwa [Φ.gauge_projection_image_sub_eq_commutator K A]
  obtain ⟨T, hmap, hfinite, hcost, _⟩ :=
    SchattenPhaseTransition.exists_unitary_minimizing_nuclear_transport_complex
      (K.map A.toLinearMap) K hD hbalance
  let C := A.trans T
  have hrel : A.symm.trans C = T := by ext x; simp [C]
  have hexact : Φ.gauge ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) =
      Φ.gauge ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) := by
    rw [Φ.gauge_unitary_sub_eq_displacement A C, hrel, hcost,
      Φ.gauge_projection_image_sub_eq_commutator K A]
  refine ⟨C, ?_, ?_, hexact, ?_⟩
  · apply (K.map_eq_self_iff_commute_starProjection C).mp
    rw [← K.map_correction_transport A C, hrel]
    exact hmap
  · rw [Φ.gauge_unitary_sub_eq_displacement A C, hrel]
    exact hfinite
  · intro V hV
    rw [hexact]
    exact Φ.gauge_commutator_le_unitary_correction K A V hV

/-- Below unit operator-norm commutator, nuclear ideal membership alone
gives exact finite-cost correction and its sharp commutator value. -/
theorem exists_nearest_nuclear_commuting_unitary_of_commutator_norm_lt_one_complex
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E)
    (hnorm : ‖(A : E →L[ℂ] E) * K.starProjection -
      K.starProjection * (A : E →L[ℂ] E)‖ < 1)
    (hcomm : (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞) :
    ∃ C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) K.starProjection ∧
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
        ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≠ ∞ ∧
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
          ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) =
        (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
          ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ∧
      ∀ V : E ≃ₗᵢ[ℂ] E, Commute (V : E →L[ℂ] E) K.starProjection →
        (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
            ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
            ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)) := by
  apply exists_nearest_nuclear_commuting_unitary_complex K A hcomm
  have hacute : IsUniformlyAcute (K.map A.toLinearMap) K := by
    simpa only [IsUniformlyAcute, Submodule.projectionGap_def,
      K.norm_projection_image_sub_eq_commutator A] using hnorm
  rw [halmosSourceDefect_eq_bot_of_isUniformlyAcute _ _ hacute,
    halmosTargetDefect_eq_bot_of_isUniformlyAcute _ _ hacute]

/-- A finite-cost globally nearest nuclear correction exists exactly
under trace-class commutator and balanced image/source defects. Thus
feasibility already implies exact attainment at the endpoint. -/
theorem exists_finite_nearest_nuclear_commuting_unitary_iff_complex
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E) :
    (∃ C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) K.starProjection ∧
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
        ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≠ ∞ ∧
      ∀ V : E ≃ₗᵢ[ℂ] E, Commute (V : E →L[ℂ] E) K.starProjection →
        (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
            ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
            ((A : E →L[ℂ] E) - (V : E →L[ℂ] E))) ↔
    (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
        ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞ ∧
      Module.finrank ℂ (halmosSourceDefect (K.map A.toLinearMap) K) =
        Module.finrank ℂ (halmosTargetDefect (K.map A.toLinearMap) K) := by
  constructor
  · rintro ⟨C, hC, hfinite, _⟩
    exact (schatten_commuting_correction_iff_commutator_and_defect_balance
      1 (by norm_num) K A).mp ⟨C, hC, hfinite⟩
  · rintro ⟨hcomm, hbalance⟩
    obtain ⟨C, hC, hfinite, _, hmin⟩ :=
      exists_nearest_nuclear_commuting_unitary_complex K A hcomm hbalance
    exact ⟨C, hC, hfinite, hmin⟩

/-- **Nuclear correction is unique only for an existing symmetry.**
For an arbitrary ambient unitary, the globally nearest projection-
commuting unitary is unique exactly when the input already commutes
with the projection. No ideal, norm-gap or defect hypotheses are needed. -/
theorem existsUnique_nearest_nuclear_commuting_unitary_iff_complex
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E) :
    (∃! C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) K.starProjection ∧
      ∀ V : E ≃ₗᵢ[ℂ] E, Commute (V : E →L[ℂ] E) K.starProjection →
        (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
            ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
            ((A : E →L[ℂ] E) - (V : E →L[ℂ] E))) ↔
      Commute (A : E →L[ℂ] E) K.starProjection := by
  rw [(OperatorIdealFamily.schatten ℂ 1 (by norm_num)).existsUnique_correction_iff_transport K A,
    SchattenPhaseTransition.nuclear_transport_unique_minimizer_iff_complex,
    K.map_eq_self_iff_commute_starProjection A]

end TauCeti.DavisKahan.InfiniteDimensional
