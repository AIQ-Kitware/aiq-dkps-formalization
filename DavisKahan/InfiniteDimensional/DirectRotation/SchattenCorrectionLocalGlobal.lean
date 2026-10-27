/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenLocalGlobal
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCorrectionUniqueness

/-!
# Complete strict Schatten local symmetry-correction landscape

Every operator-norm local correction is either globally nearest or has
noncompact difference from the input. Finite-cost local corrections are
globally nearest. Under the closed critical commutator certificate,
every compact local correction is the actual canonical polar correction.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Complete local landscape for unitary symmetry correction.**
A feasible commuting correction is locally nearest in operator norm iff
it is globally nearest or its difference from the input is noncompact.
The latter points lie on infinite-cost plateaus. No finite-distance,
commutator-ideal or index hypothesis is imposed. -/
theorem schatten_correction_isLocalMinOn_iff_global_or_noncompact_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection) :
    IsLocalMinOn
      (fun V : E ≃ₗᵢ[ℂ] E =>
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)))
      {V | Commute (V : E →L[ℂ] E) K.starProjection} C ↔
    IsMinOn
      (fun V : E ≃ₗᵢ[ℂ] E =>
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)))
      {V | Commute (V : E →L[ℂ] E) K.starProjection} C ∨
      ¬ IsCompactOperator
        (((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) : E →L[ℂ] E) := by
  let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
  let L := K.map A.toLinearMap
  let T := A.symm.trans C
  have hmap : L.map T.toLinearMap = K := by
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection C).mpr hC
  have hglobal :
      IsMinOn
        (fun V : E ≃ₗᵢ[ℂ] E =>
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)))
        {V | Commute (V : E →L[ℂ] E) K.starProjection} C ↔
      IsMinOn
        (fun V : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (V : E →L[ℂ] E)))
        {V | L.map V.toLinearMap = K} T := by
    constructor
    · intro hmin V hV
      exact (Φ.gauge_correction_isMin_iff_transport_isMin K A C).mp
        (fun W hW => @hmin W hW) V hV
    · intro hmin V hV
      exact (Φ.gauge_correction_isMin_iff_transport_isMin K A C).mpr
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
  exact (Φ.gauge_correction_isLocalMinOn_iff_transport_isLocalMinOn K A C hC).trans
    ((schatten_isLocalMinOn_iff_global_or_noncompact_complex p hp hp1 hp2 L K T hmap).trans
      (or_congr hglobal.symm (not_congr hcompact.symm)))

/-- A finite-cost local correction is globally nearest among all
projection-commuting ambient unitaries, including infinite-cost rivals. -/
theorem schatten_correction_isMin_of_isLocalMinOn_of_finite_cost_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun V : E ≃ₗᵢ[ℂ] E =>
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)))
      {V | Commute (V : E →L[ℂ] E) K.starProjection} C) :
    IsMinOn
      (fun V : E ≃ₗᵢ[ℂ] E =>
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)))
      {V | Commute (V : E →L[ℂ] E) K.starProjection} C := by
  have h := (schatten_correction_isLocalMinOn_iff_global_or_noncompact_complex
    p hp hp1 hp2 K A C hC).mp hmin
  apply h.resolve_right
  exact not_not.mpr (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    p.toReal hp1.le _ hfinite)

/-- A locally nearest compact correction is the canonical polar
correction under the closed critical commutator certificate. Finite
candidate Schatten distance and index balance are not assumed. -/
theorem eq_canonical_correction_of_schatten_isLocalMinOn_of_compact_of_commutator_le_critical_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (hcompact : IsCompactOperator
      (((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) : E →L[ℂ] E))
    (hcomm : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hnorm : ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
      Real.sin (criticalAngle p.toReal))
    (hmin : IsLocalMinOn
      (fun V : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        ((A : E →L[ℂ] E) - (V : E →L[ℂ] E)))
      {V | Commute (V : E →L[ℂ] E) K.starProjection} C) :
    (C : E →L[ℂ] E) = spectraCanonicalPolarFactor (K.map A.toLinearMap) K ∘L
      (A : E →L[ℂ] E) := by
  have hglobal := ((schatten_correction_isLocalMinOn_iff_global_or_noncompact_complex
    p hp hp1 hp2 K A C hC).mp hmin).resolve_right (not_not.mpr hcompact)
  exact eq_canonical_correction_of_schatten_minimal_of_commutator_le_critical
    p hp hp1 hp2 K A C hC hcomm hnorm (fun V hV => @hglobal V hV)

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
