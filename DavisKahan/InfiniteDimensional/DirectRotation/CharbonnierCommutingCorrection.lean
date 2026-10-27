/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierUniquenessThreshold
public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierLocalGlobal
public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierOptimizerRank
public import ForTauCeti.Analysis.InnerProductSpace.Projection.CharbonnierCorrection

/-!
# Exact smoothed correction of projection symmetry

The Hilbert-space transport classification gives an exact correction
criterion for arbitrary unitaries: the nearest projection-commuting
unitary is unique precisely under Hilbert--Schmidt commutator membership
and the closed critical operator-norm bound. In that regime every
minimizing correction is the canonical polar correction. These are
operator approximation theorems, with no numerical performance claim.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Exact necessary and sufficient conditions for a unique nearest
projection-commuting unitary in native Charbonnier cost. Neither
compactness, finite distance nor index balance is assumed. -/
theorem existsUnique_nearest_charbonnier_commuting_unitary_iff_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E) :
    (∃! C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) K.starProjection ∧
      ∀ V : E ≃ₗᵢ[ℂ] E, Commute (V : E →L[ℂ] E) K.starProjection →
        ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)).charbonnierCost tau ≤
          ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)).charbonnierCost tau) ↔
      (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
          ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞ ∧
        ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
          Real.sin (smoothedCriticalAngle tau) := by
  refine (existsUnique_charbonnier_correction_iff_transport tau K A).trans ?_
  have h := charbonnierHilbertTransport_unique_minimizer_iff_complex tau hτ (K.map A.toLinearMap) K
  simp only [mem_charbonnierHilbertTransportMinimizers_complex, Submodule.projectionGap_def] at h
  rw [OperatorIdealFamily.gauge_projection_image_sub_eq_commutator,
    K.norm_projection_image_sub_eq_commutator A] at h
  exact h

/-- Every minimizing correction under the closed critical commutator
certificate equals the explicit canonical polar correction. The
candidate's finite distance follows from optimality. -/
theorem eq_canonical_correction_of_charbonnier_minimal_of_commutator_le_critical_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (hcomm : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hnorm : ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
      Real.sin (smoothedCriticalAngle tau))
    (hmin : ∀ V : E ≃ₗᵢ[ℂ] E, Commute (V : E →L[ℂ] E) K.starProjection →
      ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)).charbonnierCost tau ≤
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)).charbonnierCost tau) :
    (C : E →L[ℂ] E) = spectraCanonicalPolarFactor (K.map A.toLinearMap) K ∘L
      (A : E →L[ℂ] E) := by
  let L := K.map A.toLinearMap
  let T := A.symm.trans C
  have hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (L.starProjection - K.starProjection) ≠ ∞ := by
    rwa [(OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge_projection_image_sub_eq_commutator K A]
  have hgap : L.projectionGap K ≤ Real.sin (smoothedCriticalAngle tau) := by
    rw [Submodule.projectionGap_def, K.norm_projection_image_sub_eq_commutator A]
    exact hnorm
  have hmap : L.map T.toLinearMap = K := by
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection C).mpr hC
  have hTmin := (charbonnier_correction_isMin_iff_transport_isMin tau K A C).mp hmin
  obtain ⟨T₀, hT₀, huni⟩ := (charbonnierHilbertTransport_unique_minimizer_iff_complex
    tau hτ L K).mpr ⟨hD, hgap⟩
  have hT₀' := (mem_charbonnierHilbertTransportMinimizers_complex tau L K T₀).mp hT₀
  have hTfinite := charbonnierCost_displacement_ne_top_of_unique_transport tau hτ.le
    L K T₀ hT₀'.1 hT₀'.2 (fun V hV => huni V
      ((mem_charbonnierHilbertTransportMinimizers_complex tau L K V).mpr hV))
  have heq : T = T₀ := huni T ((mem_charbonnierHilbertTransportMinimizers_complex tau L K T).mpr
    ⟨hmap, hTmin⟩)
  have hfinite : (1 - (T : E →L[ℂ] E)).charbonnierCost tau ≠ ∞ := by
    rwa [heq]
  have hcanonical := eq_canonicalPolarFactor_of_charbonnier_minimal_of_gap_le_critical_complex
    tau hτ L K T hmap hfinite hTmin hgap
  calc
    (C : E →L[ℂ] E) = (T : E →L[ℂ] E) ∘L (A : E →L[ℂ] E) := by
      ext x
      exact (congrArg C (A.symm_apply_apply x)).symm
    _ = _ := congrArg (fun B : E →L[ℂ] E => B ∘L (A : E →L[ℂ] E)) hcanonical

/-- Balanced Hilbert--Schmidt commutator data admit an attaining nearest
commuting unitary with exact intrinsic principal-angle cost. Competing
commuting unitaries range over the full ambient unitary group. -/
theorem exists_nearest_charbonnier_commuting_unitary_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E)
    (hcomm : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hbalance : Module.finrank ℂ (halmosSourceDefect (K.map A.toLinearMap) K) =
      Module.finrank ℂ (halmosTargetDefect (K.map A.toLinearMap) K)) :
    ∃ C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) K.starProjection ∧
      ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)).charbonnierCost tau ≠ ∞ ∧
      ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)).charbonnierCost tau =
        ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
          (Real.arcsin (((K.map A.toLinearMap).sinThetaMap K).singularValue j : ℝ))) ∧
      ∀ V : E ≃ₗᵢ[ℂ] E, Commute (V : E →L[ℂ] E) K.starProjection →
        ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)).charbonnierCost tau ≤
          ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)).charbonnierCost tau := by
  have hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      ((K.map A.toLinearMap).starProjection - K.starProjection) ≠ ∞ := by
    rwa [(OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge_projection_image_sub_eq_commutator K A]
  obtain ⟨T, hmap, hfinite, hcost, hmin⟩ :=
    exists_unitary_minimizing_charbonnier_transport_of_projection_sub_ne_top
      tau hτ (K.map A.toLinearMap) K hD hbalance
  let C := A.trans T
  have hrel : A.symm.trans C = T := by ext x; simp [C]
  have hC : Commute (C : E →L[ℂ] E) K.starProjection := by
    apply (K.map_eq_self_iff_commute_starProjection C).mp
    rw [← K.map_correction_transport A C, hrel]
    exact hmap
  have hval := ContinuousLinearMap.charbonnierCost_unitary_sub_eq_displacement tau A C
  rw [hrel] at hval
  refine ⟨C, hC, by rwa [hval], hval.trans hcost, ?_⟩
  apply (charbonnier_correction_isMin_iff_transport_isMin tau K A C).mpr
  rwa [hrel]

/-- Every nearest commuting correction differs from the completed
canonical correction by finite rank, with the budget controlled by the
actual squared Hilbert--Schmidt commutator gauge. All ambient commuting competitors
are included, and the candidate's finite distance is not assumed. -/
theorem charbonnier_nearest_commuting_unitary_has_critical_rank_budget_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (J : halmosSourceDefect (K.map A.toLinearMap) K ≃ₗᵢ[ℂ]
      halmosTargetDefect (K.map A.toLinearMap) K)
    (hcomm : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hmin : ∀ V : E ≃ₗᵢ[ℂ] E, Commute (V : E →L[ℂ] E) K.starProjection →
      ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)).charbonnierCost tau ≤
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)).charbonnierCost tau) :
    let L := K.map A.toLinearMap
    let c := Real.sin (smoothedCriticalAngle tau)
    let M := eigenSpan (L.sinAngleOperator K) (Set.Ioi c)
    ((nonacuteDirectRotation L K J).toLinearMap.comp A.toLinearMap - C.toLinearMap).rank ≤
        Module.finrank ℂ M ∧
      (Module.finrank ℂ M : ℝ≥0∞) * ENNReal.ofReal c ^ (2 : ℝ) ≤
        (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
          ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ^
            (2 : ℝ) := by
  let L := K.map A.toLinearMap
  let T := A.symm.trans C
  let Φ := OperatorIdealFamily.schatten ℂ 2 (by norm_num)
  have hD : Φ.gauge (L.starProjection - K.starProjection) ≠ ∞ := by
    rwa [Φ.gauge_projection_image_sub_eq_commutator K A]
  have hmap : L.map T.toLinearMap = K := by
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection C).mpr hC
  have hTmin := (charbonnier_correction_isMin_iff_transport_isMin tau K A C).mp hmin
  obtain ⟨hRank, hbudget⟩ :=
    charbonnier_minimizer_has_critical_rank_budget_complex tau hτ L K J hD T hmap hTmin
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

/-- **Complete local landscape for unitary symmetry correction.**
A feasible commuting correction is locally nearest in operator norm iff
it is globally nearest or its difference from the input is noncompact.
The latter points lie on infinite-cost plateaus. No finite-distance,
commutator-ideal or index hypothesis is imposed. -/
theorem charbonnier_correction_isLocalMinOn_iff_global_or_noncompact_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection) :
    IsLocalMinOn
      (fun V : E ≃ₗᵢ[ℂ] E =>
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)).charbonnierCost tau)
      {V | Commute (V : E →L[ℂ] E) K.starProjection} C ↔
    IsMinOn
      (fun V : E ≃ₗᵢ[ℂ] E =>
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)).charbonnierCost tau)
      {V | Commute (V : E →L[ℂ] E) K.starProjection} C ∨
      ¬ IsCompactOperator
        (((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) : E →L[ℂ] E) := by
  let L := K.map A.toLinearMap
  let T := A.symm.trans C
  have hmap : L.map T.toLinearMap = K := by
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection C).mpr hC
  have hglobal :
      IsMinOn
        (fun V : E ≃ₗᵢ[ℂ] E =>
          ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)).charbonnierCost tau)
        {V | Commute (V : E →L[ℂ] E) K.starProjection} C ↔
      IsMinOn
        (fun V : E ≃ₗᵢ[ℂ] E => (1 - (V : E →L[ℂ] E)).charbonnierCost tau)
        {V | L.map V.toLinearMap = K} T := by
    constructor
    · intro hmin V hV
      exact (charbonnier_correction_isMin_iff_transport_isMin tau K A C).mp
        (fun W hW => @hmin W hW) V hV
    · intro hmin V hV
      exact (charbonnier_correction_isMin_iff_transport_isMin tau K A C).mpr
        (fun W hW => @hmin W hW) V hV
  have hcompact :
      IsCompactOperator (((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) : E →L[ℂ] E) ↔
      IsCompactOperator ((1 - (T : E →L[ℂ] E)) : E →L[ℂ] E) := by
    have hfactor : (A : E →L[ℂ] E) - (C : E →L[ℂ] E) =
        (1 - (T : E →L[ℂ] E)) ∘L (A : E →L[ℂ] E) := by
      ext x
      change A x - C x = A x - C (A.symm (A x))
      rw [A.symm_apply_apply]
    have hfactor' : 1 - (T : E →L[ℂ] E) =
        ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ∘L (A.symm : E →L[ℂ] E) := by
      ext x
      change x - C (A.symm x) = A (A.symm x) - C (A.symm x)
      rw [A.apply_symm_apply]
    constructor
    · intro h
      rw [hfactor']
      exact h.comp_clm (A.symm : E →L[ℂ] E)
    · intro h
      rw [hfactor]
      exact h.comp_clm (A : E →L[ℂ] E)
  exact (charbonnier_correction_isLocalMinOn_iff_transport_isLocalMinOn tau K A C hC).trans
    ((charbonnier_isLocalMinOn_iff_global_or_noncompact_complex tau hτ L K T hmap).trans
      (or_congr hglobal.symm (not_congr hcompact.symm)))

/-- A finite-cost local correction is globally nearest among all
projection-commuting ambient unitaries, including infinite-cost rivals. -/
theorem charbonnier_correction_isMin_of_isLocalMinOn_of_finite_cost_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (hfinite : ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : IsLocalMinOn
      (fun V : E ≃ₗᵢ[ℂ] E =>
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)).charbonnierCost tau)
      {V | Commute (V : E →L[ℂ] E) K.starProjection} C) :
    IsMinOn
      (fun V : E ≃ₗᵢ[ℂ] E =>
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)).charbonnierCost tau)
      {V | Commute (V : E →L[ℂ] E) K.starProjection} C := by
  have h := (charbonnier_correction_isLocalMinOn_iff_global_or_noncompact_complex
    tau hτ K A C hC).mp hmin
  apply h.resolve_right
  exact not_not.mpr (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) _
    ((ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hfinite))

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
