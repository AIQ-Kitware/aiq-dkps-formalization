/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenOptimizerClassification
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenFeasibility

/-!
# No nonglobal finite-cost Hilbert Schatten local minima

For `1<p<2`, actual local stationarity and finite landscape rigidity
force canonical action on the entire inactive tail. The exact cutoff
criterion proves global minimality against all ambient competitors.
The full gradient kernel, zero-angle sector and right defects are retained.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Every finite-cost operator-norm local Schatten transport minimum
is globally minimizing for `1<p<2`, in arbitrary complete complex Hilbert
dimension. Native finite feasibility supplies all ideal/index conditions;
no separability, finite-rank or prescribed-block hypothesis is imposed. -/
theorem schatten_isMin_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U) :
    ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E)) := by
  obtain ⟨hD, hbalance⟩ :=
    (schatten_transport_iff_projection_sub_ne_top_and_defect_balance p.toReal hp1.le K L).mp
      ⟨U, hmap, hfinite⟩
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    p.toReal hp1.le (K.starProjection - L.starProjection) hD
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq
    K L hcompact hbalance
  let c := Real.sin (criticalAngle p.toReal) / 2
  have hangle := criticalAngle_mem p.toReal hp1 hp2
  have hsin : 0 < Real.sin (criticalAngle p.toReal) :=
    Real.sin_pos_of_pos_of_lt_pi hangle.1 (by linarith [hangle.2, Real.pi_pos])
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : c < 1 := by dsimp only [c]; linarith [Real.sin_le_one (criticalAngle p.toReal)]
  have hcrit : c ≤ Real.sin (criticalAngle p.toReal) := by dsimp only [c]; linarith
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  obtain ⟨hM, hK, _, _⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  have hUS := commute_sinAngleOperator_of_schatten_isLocalMinOn_complex
    p hp hp1 hp2 K L U hmap hfinite hmin
  obtain ⟨V, hV, hVmap, _, hVmin⟩ := exists_schatten_locally_minimizing_finite_restriction
    p.toReal hp1.le K L M U hmap hfinite hmin hK
      (eigenSpan_invariant_of_commute (K.sinAngleOperator L) _ hUS _)
  have htail := apply_eq_nonacuteDirectRotation_on_inactive_tail_of_schatten_isLocalMinOn_complex
    p hp hp1 hp2 K L J hD c hc hc1 hcrit U hmap hfinite hmin
  obtain ⟨W, hW, _, hiff⟩ := schatten_minimal_iff_finite_restriction_of_canonical_tail
    p hp hp1 hp2 K L J hD c hc hc1 hcrit U hmap hfinite htail
  have heq : W = V := by
    ext x
    exact (hW x).trans (hV x).symm
  subst W
  exact hiff.mpr (schatten_power_isMin_of_isLocalMinOn_complex p hp hp1 hp2
    (K.comap M.subtype) (L.comap M.subtype) V hVmap hVmin)

/-- Native local and global minima coincide on the finite-cost part
of the strict-exponent transport fiber, in operator-norm topology. -/
theorem schatten_isLocalMinOn_iff_isMinOn_of_finite_cost_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞) :
    IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U ↔
    IsMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U := by
  constructor
  · intro hmin
    exact fun T hT => schatten_isMin_of_isLocalMinOn_complex p hp hp1 hp2 K L U
      hmap hfinite hmin T hT
  · exact IsMinOn.isLocalMinOn

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
