/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenLocalGlobal
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Topology

/-!
# Native Schatten local minima on finite unitary transport groups

Transfer native extended-gauge local optimality through the actual
operator-norm embedding to the finite powered Schatten landscape.
The positive exponent preserves order, including at zero displacement.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Filter
open scoped ENNReal Topology TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Native gauge local minima minimize the full finite powered objective,
including all repeated, zero, critical and right principal angles. -/
theorem schatten_power_isMin_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U) :
    ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - U.toLinearMap) ^ p.toReal ≤
        UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - T.toLinearMap) ^ p.toReal := by
  let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
  let f (T : E ≃ₗᵢ[ℂ] E) : E →L[ℂ] E := T
  let F (T : E →L[ℂ] E) :=
    UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - T.toLinearMap) ^ p.toReal
  let S := {T : E ≃ₗᵢ[ℂ] E | K.map T.toLinearMap = L}
  let C := {T : E →L[ℂ] E |
    T ∈ unitary (E →L[ℂ] E) ∧ T * K.starProjection * star T = L.starProjection}
  have himage : f '' S = C := by
    ext T
    constructor
    · rintro ⟨V, hV, rfl⟩
      exact ⟨(Unitary.linearIsometryEquiv.symm V).property,
        (K.map_eq_iff_conjugate_starProjection L V).mp hV⟩
    · rintro ⟨hT, hconj⟩
      let V := Unitary.linearIsometryEquiv (⟨T, hT⟩ : unitary (E →L[ℂ] E))
      exact ⟨V, (K.map_eq_iff_conjugate_starProjection L V).mpr hconj, rfl⟩
  have hvalue (T : E ≃ₗᵢ[ℂ] E) : Φ.gauge (1 - (T : E →L[ℂ] E)) ^ p.toReal =
      ENNReal.ofReal (F (f T)) := by
    rw [OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp]
    rfl
  have hreal : IsLocalMinOn (fun T => F (f T)) S U := by
    filter_upwards [hmin] with T hT
    have h := ENNReal.rpow_le_rpow hT (zero_lt_one.trans hp1).le
    rw [hvalue, hvalue] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by dsimp [F]; positivity)).mp h
  have hCLM : IsLocalMinOn F C (f U) := by
    change ∀ᶠ (T : E →L[ℂ] E) in 𝓝[C] (f U), F (f U) ≤ F T
    have hfilter : Filter.map f (𝓝[S] U) = 𝓝[C] (f U) := by
      rw [← himage]
      exact LinearIsometryEquiv.isEmbedding_toContinuousLinearMap.map_nhdsWithin_eq S U
    rw [← hfilter]
    exact hreal
  have hg : IsMinOn F C (f U) := isMinOn_of_isLocalMinOn_transports_complex
    p hp hp1 hp2 K L (Unitary.linearIsometryEquiv.symm U) hmap hCLM
  intro T hT
  change F (f U) ≤ F (f T)
  exact @hg (f T) ⟨(Unitary.linearIsometryEquiv.symm T).property,
    (K.map_eq_iff_conjugate_starProjection L T).mp hT⟩

/-- Every native finite-dimensional Schatten transport local minimum
is globally minimizing for `1<p<2`, in operator-norm topology. -/
theorem schatten_isMin_of_isLocalMinOn_finite_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (T : E →L[ℂ] E))) {T | K.map T.toLinearMap = L} U) :
    ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E)) := by
  intro T hT
  have h := schatten_power_isMin_of_isLocalMinOn_complex p hp hp1 hp2 K L U hmap hmin T hT
  have hvalue (V : E ≃ₗᵢ[ℂ] E) :
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (V : E →L[ℂ] E)) ^ p.toReal =
      ENNReal.ofReal (UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - V.toLinearMap) ^ p.toReal) := by
    rw [OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp]
    rfl
  apply (ENNReal.rpow_le_rpow_iff (zero_lt_one.trans hp1)).mp
  rw [hvalue, hvalue]
  exact ENNReal.ofReal_le_ofReal h

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
