/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedLocalGlobal
public import ForTauCeti.Analysis.OperatorIdeal.CharbonnierFinite
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Topology

/-!
# Native-cost local minima on the finite unitary transport group

Use the actual operator-norm embedding to transfer native ENNReal local
optimality to the real finite spectral landscape theorem. Positivity of
the finite penalty justifies recovering real inequalities from `ofReal`.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open Filter
open scoped ENNReal Topology TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A native Charbonnier local minimum in the operator-norm unitary
group minimizes the unrestricted finite real spectral objective. -/
theorem smoothed_isMin_of_charbonnier_isLocalMinOn_complex
    (tau : ℝ) (hτ : 0 < tau) (K L : Submodule ℂ E)
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
      {T | K.map T.toLinearMap = L} U) :
    ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      smoothedDisplacementCost tau U.toLinearMap ≤
        smoothedDisplacementCost tau T.toLinearMap := by
  let f (T : E ≃ₗᵢ[ℂ] E) : E →L[ℂ] E := T
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
  have hcost (T : E ≃ₗᵢ[ℂ] E) : (1 - (T : E →L[ℂ] E)).charbonnierCost tau =
      ENNReal.ofReal (smoothedDisplacementCost tau T.toLinearMap) := by
    rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
    rfl
  have hnonneg (T : E ≃ₗᵢ[ℂ] E) : 0 ≤ smoothedDisplacementCost tau T.toLinearMap := by
    unfold smoothedDisplacementCost
    apply Finset.sum_nonneg
    intro i _
    exact sub_nonneg.mpr (Real.le_sqrt_of_sq_le
      (by nlinarith [sq_nonneg ((LinearMap.id - T.toLinearMap).singularValues i)]))
  have hreal : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => smoothedDisplacementCost tau T.toLinearMap) S U := by
    filter_upwards [hmin] with T hT
    rw [hcost, hcost] at hT
    exact (ENNReal.ofReal_le_ofReal_iff (hnonneg T)).mp hT
  have hCLM : IsLocalMinOn
      (fun T : E →L[ℂ] E => smoothedDisplacementCost tau T.toLinearMap) C (f U) := by
    change ∀ᶠ (T : E →L[ℂ] E) in 𝓝[C] (f U),
      smoothedDisplacementCost tau (f U).toLinearMap ≤
        smoothedDisplacementCost tau T.toLinearMap
    have hfilter : Filter.map f (𝓝[S] U) = 𝓝[C] (f U) := by
      rw [← himage]
      exact LinearIsometryEquiv.isEmbedding_toContinuousLinearMap.map_nhdsWithin_eq S U
    rw [← hfilter]
    exact hreal
  have hg := isMinOn_of_isLocalMinOn_transports_complex tau hτ K L
    (Unitary.linearIsometryEquiv.symm U) hmap hCLM
  intro T hT
  exact @hg (T : E →L[ℂ] E) (show (T : E →L[ℂ] E) ∈ C from
    ⟨(Unitary.linearIsometryEquiv.symm T).property,
      (K.map_eq_iff_conjugate_starProjection L T).mp hT⟩)

/-- No nonglobal local minima for the literal finite native smoothed
trace, with operator-norm topology on actual unitary transports. -/
theorem charbonnier_isMin_of_isLocalMinOn_finite_complex
    (tau : ℝ) (hτ : 0 < tau) (K L : Submodule ℂ E)
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
      {T | K.map T.toLinearMap = L} U) :
    ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau := by
  intro T hT
  have h := smoothed_isMin_of_charbonnier_isLocalMinOn_complex tau hτ K L U hmap hmin T hT
  have hcost (V : E ≃ₗᵢ[ℂ] E) : (1 - (V : E →L[ℂ] E)).charbonnierCost tau =
      ENNReal.ofReal (smoothedDisplacementCost tau V.toLinearMap) := by
    rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
    rfl
  rw [hcost, hcost]
  exact ENNReal.ofReal_le_ofReal h

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
