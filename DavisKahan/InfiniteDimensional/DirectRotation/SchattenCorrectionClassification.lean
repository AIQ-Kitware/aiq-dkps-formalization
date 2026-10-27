/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenOptimizerRank
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCommutingCorrection

/-!
# Every nearest projection-commuting unitary on a Hilbert space

The exact correction/transport correspondence identifies all nearest
commuting unitaries, not only an attaining one. Their entire freedom
is finite-dimensional and has the same compatible phase and reflecting
defect parameters as transport of the actual image back to the source.
The correspondence is classical; these are consequences of the proved
nonquadratic Hilbert-space optimizer classification.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Every Schatten-nearest commuting unitary has exactly the canonical
tail and finite compatible phase/defect data of the image/source pair.
The candidate need not be assumed to have finite distance or preserve
angle blocks; all ambient commuting competitors are compared. -/
theorem schatten_correction_isMin_iff_canonical_tail_phase_and_defect_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (J : halmosSourceDefect (K.map A.toLinearMap) K ≃ₗᵢ[ℂ]
      halmosTargetDefect (K.map A.toLinearMap) K)
    (hcomm : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (criticalAngle p.toReal)) :
    let L := K.map A.toLinearMap
    let T := A.symm.trans C
    let M := eigenSpan (L.sinAngleOperator K) (Set.Ioi c)
    let _ : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff L K
      (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
        (L.starProjection - K.starProjection)
          (by
            simpa only [L, OperatorIdealFamily.gauge_projection_image_sub_eq_commutator]
              using hcomm)) c hc).1
    let K₀ := L.comap M.subtype
    let L₀ := K.comap M.subtype
    (∀ W : E ≃ₗᵢ[ℂ] E, Commute (W : E →L[ℂ] E) K.starProjection →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          ((A : E →L[ℂ] E) - (W : E →L[ℂ] E))) ↔
      (∀ x ∈ Mᗮ, T x = nonacuteDirectRotation L K J x) ∧
      ∃ (V : M ≃ₗᵢ[ℂ] M) (hKL : Module.finrank ℂ K₀ = Module.finrank ℂ L₀),
        (∀ x : M, (V x : E) = T x) ∧ K₀.map V.toLinearMap = L₀ ∧
        let R₀ := Unitary.linearIsometryEquiv
          (⟨nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL),
            nonacuteDirectRotation_mem_unitary K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL)⟩ :
              unitary (M →L[ℂ] M))
        let C₀ := Proposition35.section3CosAngleOperator K₀ L₀
        let F₀ := schattenPhaseFactor p.toReal C₀
        ∃ P : M →L[ℂ] M, IsStarProjection P ∧ Commute P (R₀ : M →L[ℂ] M) ∧
          (∀ x, P (K₀.reflection x) = K₀.reflection (P x)) ∧
          ∃ D : halmosSourceDefect K₀ L₀ ≃ₗᵢ[ℂ] halmosTargetDefect K₀ L₀,
            (∀ x : halmosSourceDefect K₀ L₀, V x = (D x : M)) ∧
            (∀ y : halmosTargetDefect K₀ L₀, V y = (D.symm y : M)) ∧
            C₀ * (V.trans R₀.symm : M →L[ℂ] M) = C₀ * (F₀ * P + star F₀ * (1 - P)) := by
  let L := K.map A.toLinearMap
  let T := A.symm.trans C
  let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
  have hD : Φ.gauge (L.starProjection - K.starProjection) ≠ ∞ := by
    rwa [Φ.gauge_projection_image_sub_eq_commutator K A]
  have hmap : L.map T.toLinearMap = K := by
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection C).mpr hC
  exact (Φ.gauge_correction_isMin_iff_transport_isMin K A C).trans
    (schatten_transport_isMin_iff_canonical_tail_phase_and_defect_complex
      p hp hp1 hp2 L K J hD c hc hc1 hcrit T hmap)

/-- Every nearest commuting correction differs from the completed
canonical correction by finite rank, with the budget controlled by the
actual commutator Schatten power. All ambient commuting competitors
are included, and the candidate's finite distance is not assumed. -/
theorem schatten_nearest_commuting_unitary_has_critical_rank_budget
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (J : halmosSourceDefect (K.map A.toLinearMap) K ≃ₗᵢ[ℂ]
      halmosTargetDefect (K.map A.toLinearMap) K)
    (hcomm : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hmin : ∀ W : E ≃ₗᵢ[ℂ] E, Commute (W : E →L[ℂ] E) K.starProjection →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          ((A : E →L[ℂ] E) - (W : E →L[ℂ] E))) :
    let L := K.map A.toLinearMap
    let c := Real.sin (criticalAngle p.toReal)
    let M := eigenSpan (L.sinAngleOperator K) (Set.Ioi c)
    ((nonacuteDirectRotation L K J).toLinearMap.comp A.toLinearMap - C.toLinearMap).rank ≤
        Module.finrank ℂ M ∧
      (Module.finrank ℂ M : ℝ≥0∞) * ENNReal.ofReal c ^ p.toReal ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ^
            p.toReal := by
  let L := K.map A.toLinearMap
  let T := A.symm.trans C
  let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
  have hD : Φ.gauge (L.starProjection - K.starProjection) ≠ ∞ := by
    rwa [Φ.gauge_projection_image_sub_eq_commutator K A]
  have hmap : L.map T.toLinearMap = K := by
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection C).mpr hC
  have hTmin := (Φ.gauge_correction_isMin_iff_transport_isMin K A C).mp hmin
  obtain ⟨hRank, hbudget⟩ :=
    schatten_minimizer_has_critical_rank_budget p hp hp1 hp2 L K J hD T hmap hTmin
  refine ⟨?_, ?_⟩
  · have hfactor : (nonacuteDirectRotation L K J).toLinearMap.comp A.toLinearMap -
        C.toLinearMap = ((nonacuteDirectRotation L K J).toLinearMap - T.toLinearMap).comp
          A.toLinearMap := by
      ext x
      change nonacuteDirectRotation L K J (A x) - C x =
        nonacuteDirectRotation L K J (A x) - C (A.symm (A x))
      rw [A.symm_apply_apply]
    rw [hfactor]
    exact (LinearMap.rank_comp_le_left _ _).trans hRank
  · simpa only [L, OperatorIdealFamily.gauge_projection_image_sub_eq_commutator] using hbudget

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
