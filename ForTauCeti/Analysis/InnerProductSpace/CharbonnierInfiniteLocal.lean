/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.Charbonnier
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Topology
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Infinite-cost local plateaus in operator norm

Every unitary with noncompact displacement lies in an operator-norm
neighborhood on which the native smoothed cost is infinite. Thus the
finite-cost hypothesis in infinite-dimensional landscape results is
essential: negative identity is locally minimizing but is not globally
minimizing, even for transport of a subspace to itself.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped ENNReal Topology TauCeti.LinearIsometryEquivOperatorNorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Noncompact displacement forces infinite native Charbonnier cost at
every positive smoothing scale. -/
theorem charbonnierCost_displacement_eq_top_of_not_isCompactOperator
    (tau : ℝ) (hτ : 0 < tau) (U : E ≃ₗᵢ[𝕜] E)
    (hU : ¬ IsCompactOperator ((1 - (U : E →L[𝕜] E)) : E →L[𝕜] E)) :
    (1 - (U : E →L[𝕜] E)).charbonnierCost tau = ∞ := by
  by_contra hfinite
  exact hU (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) _
    ((ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hfinite))

/-- Every unitary with noncompact displacement is a local minimum of
the native extended smoothed cost in operator norm, because all costs
in an entire neighborhood are infinite. No constraint is required. -/
theorem isLocalMin_charbonnierCost_of_not_isCompactOperator
    (tau : ℝ) (hτ : 0 < tau) (U : E ≃ₗᵢ[𝕜] E)
    (hU : ¬ IsCompactOperator ((1 - (U : E →L[𝕜] E)) : E →L[𝕜] E)) :
    IsLocalMin
      (fun V : E ≃ₗᵢ[𝕜] E => (1 - (V : E →L[𝕜] E)).charbonnierCost tau) U := by
  have hc : Continuous (fun V : E ≃ₗᵢ[𝕜] E => (1 - (V : E →L[𝕜] E))) :=
    continuous_const.sub LinearIsometryEquiv.isEmbedding_toContinuousLinearMap.continuous
  have hclosed : IsClosed {V : E ≃ₗᵢ[𝕜] E |
      IsCompactOperator ((1 - (V : E →L[𝕜] E)) : E →L[𝕜] E)} :=
    isClosed_setOfPred_isCompactOperator.preimage hc
  have hopen := hclosed.isOpen_compl
  have hnear := hopen.mem_nhds hU
  filter_upwards [hnear] with V hV
  rw [charbonnierCost_displacement_eq_top_of_not_isCompactOperator tau hτ U hU,
    charbonnierCost_displacement_eq_top_of_not_isCompactOperator tau hτ V hV]

/-- On every infinite-dimensional real or complex Hilbert space,
negative identity preserves any prescribed subspace and is a native
operator-norm local minimum of infinite cost, while identity has cost
zero. Thus unrestricted infinite-dimensional local-to-global is false. -/
theorem neg_isLocalMinOn_not_isMinOn_charbonnier_self_transport
    (tau : ℝ) (hτ : 0 < tau) (hInfinite : ¬ FiniteDimensional 𝕜 E)
    (K : Submodule 𝕜 E) :
    let N : E ≃ₗᵢ[𝕜] E := LinearIsometryEquiv.neg 𝕜
    K.map N.toLinearMap = K ∧
      (1 - (N : E →L[𝕜] E)).charbonnierCost tau = ∞ ∧
      IsLocalMinOn
        (fun V : E ≃ₗᵢ[𝕜] E => (1 - (V : E →L[𝕜] E)).charbonnierCost tau)
        {V | K.map V.toLinearMap = K} N ∧
      ¬ IsMinOn
        (fun V : E ≃ₗᵢ[𝕜] E => (1 - (V : E →L[𝕜] E)).charbonnierCost tau)
        {V | K.map V.toLinearMap = K} N := by
  dsimp only
  let N : E ≃ₗᵢ[𝕜] E := LinearIsometryEquiv.neg 𝕜
  have hmap : K.map N.toLinearMap = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change -y ∈ K
      exact K.neg_mem hy
    · intro hx
      refine ⟨-x, K.neg_mem hx, ?_⟩
      change -(-x) = x
      exact neg_neg x
  have hnoncompact : ¬ IsCompactOperator ((1 - (N : E →L[𝕜] E)) : E →L[𝕜] E) := by
    intro hcompact
    have heq : 1 - (N : E →L[𝕜] E) = (2 : 𝕜) • (1 : E →L[𝕜] E) := by
      ext x
      change x - (-x) = (2 : 𝕜) • x
      rw [sub_neg_eq_add, two_smul]
    rw [heq] at hcompact
    have hI : IsCompactOperator (1 : E →L[𝕜] E) :=
      (IsCompactOperator.smul_iff₀ (two_ne_zero : (2 : 𝕜) ≠ 0)).mp hcompact
    exact hInfinite (FiniteDimensional.of_isCompactOperator_id hI)
  have hcost := charbonnierCost_displacement_eq_top_of_not_isCompactOperator tau hτ N hnoncompact
  refine ⟨hmap, hcost,
    (isLocalMin_charbonnierCost_of_not_isCompactOperator tau hτ N hnoncompact).isLocalMinOn _, ?_⟩
  intro hglobal
  have h := @hglobal (LinearIsometryEquiv.refl 𝕜 E) (by
    change K.map (LinearMap.id : E →ₗ[𝕜] E) = K
    simp only [Submodule.map_id])
  have hz : 1 - (LinearIsometryEquiv.refl 𝕜 E : E →L[𝕜] E) = 0 := by
    ext x
    change x - x = 0
    exact sub_self x
  change (1 - (N : E →L[𝕜] E)).charbonnierCost tau ≤
    (1 - (LinearIsometryEquiv.refl 𝕜 E : E →L[𝕜] E)).charbonnierCost tau at h
  rw [hcost, hz, (ContinuousLinearMap.charbonnierCost_eq_zero_iff tau hτ.le _).mpr rfl] at h
  exact ENNReal.zero_ne_top (le_antisymm zero_le h)

end TauCeti
