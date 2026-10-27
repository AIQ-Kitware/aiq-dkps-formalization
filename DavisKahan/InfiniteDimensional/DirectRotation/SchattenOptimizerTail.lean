/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCanonicalUniqueness
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCutoffClassification

/-!
# Every Hilbert-space optimizer has canonical inactive action

The principal-sine cutoff is proved to reduce every optimizer.
Its actual infinite tail inherits global optimality and has gap below
or at the critical sine. Closed-threshold canonical uniqueness then
identifies that entire tail with every completed ambient rotation.
The cutoff and canonical tail are conclusions, not hypotheses.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance optimizerTailComapProjection
    (K N : Submodule ℂ E) [K.HasOrthogonalProjection] [CompleteSpace N] :
    (K.comap N.subtype).HasOrthogonalProjection :=
  K.hasOrthogonalProjection_comap_subtype_of_complete N

/-- **Canonical-tail necessity for every optimizer.** For every
positive cutoff below or at the critical sine, every finite-cost local
optimizer agrees with every completed direct rotation on the full
complementary sector. Neither canonical-tail action nor block
preservation is assumed of the optimizer. -/
theorem apply_eq_nonacuteDirectRotation_on_inactive_tail_of_schatten_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (criticalAngle p.toReal))
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U) :
    ∀ x ∈ (eigenSpan (K.sinAngleOperator L) (Set.Ioi c))ᗮ,
      U x = nonacuteDirectRotation K L J x := by
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  let N := Mᗮ
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    p.toReal hp1.le (K.starProjection - L.starProjection) hD
  obtain ⟨hM, hK, _, _⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  have hUS := commute_sinAngleOperator_of_schatten_isLocalMinOn_complex p hp hp1 hp2 K L U hmap hfinite hmin
  have hUM : ∀ x ∈ M, U x ∈ M :=
    eigenSpan_invariant_of_commute (K.sinAngleOperator L) _ hUS _
  obtain ⟨_, _, _, hUred⟩ := U.exists_restriction_of_finite_invariant M hUM
  have hUN : N.IsReducing U.toLinearMap :=
    (Submodule.isReducing_orthogonal_iff M U.toLinearMap).mpr hUred
  have hKN : N.IsReducing K.starProjection.toLinearMap :=
    (Submodule.isReducing_orthogonal_iff M K.starProjection.toLinearMap).mpr hK
  obtain ⟨V, hV, hlocal, hVfinite, hVmin⟩ := exists_schatten_locally_minimizing_reducing_restriction p.toReal hp1.le
    K L N U hmap hfinite hmin hKN hUN
  obtain ⟨W, hW, _, hWcanonical, hgap⟩ :=
    exists_canonical_tail_of_finite_sine_cutoff K L J hcompact c hc hc1
  have hVcanonical := eq_canonicalPolarFactor_of_schatten_isLocalMinOn_of_gap_le_critical_complex
    p hp hp1 hp2 (K.comap N.subtype) (L.comap N.subtype) V hlocal
      hVfinite hVmin (hgap.trans hcrit)
  intro x hx
  calc
    U x = (V ⟨x, hx⟩ : E) := (hV ⟨x, hx⟩).symm
    _ = (W ⟨x, hx⟩ : E) := congrArg Subtype.val
      (congrArg (fun T : N →L[ℂ] N => T ⟨x, hx⟩) (hVcanonical.trans hWcanonical.symm))
    _ = _ := hW _

/-- Global inactive-tail necessity follows from local canonical rigidity. -/
theorem apply_eq_nonacuteDirectRotation_on_inactive_tail_of_schatten_minimal
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (criticalAngle p.toReal))
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E))) :
    ∀ x ∈ (eigenSpan (K.sinAngleOperator L) (Set.Ioi c))ᗮ,
      U x = nonacuteDirectRotation K L J x := by
  exact apply_eq_nonacuteDirectRotation_on_inactive_tail_of_schatten_isLocalMinOn_complex p hp hp1 hp2 K L J hD c hc hc1 hcrit U hmap hfinite
    (show IsMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U
      from fun T hT => hmin T hT).isLocalMinOn

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
