/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenTransportDensity
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Topology
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Infinite-cost local plateaus in operator norm

Every unitary with noncompact displacement lies in an operator-norm
neighborhood on which the native Schatten cost is infinite. Thus the
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

/-- Noncompact displacement forces infinite native Schatten cost at
every finite exponent at least one. -/
theorem gauge_schatten_displacement_eq_top_of_not_isCompactOperator
    (p : ℝ) (hp : 1 ≤ p) (U : E ≃ₗᵢ[𝕜] E)
    (hU : ¬ IsCompactOperator ((1 - (U : E →L[𝕜] E)) : E →L[𝕜] E)) :
    (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : E →L[𝕜] E)) = ∞ := by
  by_contra hfinite
  exact hU (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p hp _ hfinite)

/-- Every unitary with noncompact displacement is a local minimum of
the native extended Schatten cost in operator norm, because all costs
in an entire neighborhood are infinite. No constraint is required. -/
theorem isLocalMin_schatten_of_not_isCompactOperator
    (p : ℝ) (hp : 1 ≤ p) (U : E ≃ₗᵢ[𝕜] E)
    (hU : ¬ IsCompactOperator ((1 - (U : E →L[𝕜] E)) : E →L[𝕜] E)) :
    IsLocalMin
      (fun V : E ≃ₗᵢ[𝕜] E => (OperatorIdealFamily.schatten 𝕜 p hp).gauge
        (1 - (V : E →L[𝕜] E))) U := by
  have hc : Continuous (fun V : E ≃ₗᵢ[𝕜] E => (1 - (V : E →L[𝕜] E))) :=
    continuous_const.sub LinearIsometryEquiv.isEmbedding_toContinuousLinearMap.continuous
  have hclosed : IsClosed {V : E ≃ₗᵢ[𝕜] E |
      IsCompactOperator ((1 - (V : E →L[𝕜] E)) : E →L[𝕜] E)} :=
    isClosed_setOfPred_isCompactOperator.preimage hc
  have hopen := hclosed.isOpen_compl
  have hnear := hopen.mem_nhds hU
  filter_upwards [hnear] with V hV
  rw [gauge_schatten_displacement_eq_top_of_not_isCompactOperator p hp U hU,
    gauge_schatten_displacement_eq_top_of_not_isCompactOperator p hp V hV]

/-- On every infinite-dimensional real or complex Hilbert space,
negative identity preserves any prescribed subspace and is a native
operator-norm local minimum of infinite cost, while identity has cost
zero. Thus unrestricted infinite-dimensional local-to-global is false. -/
theorem neg_isLocalMinOn_not_isMinOn_schatten_self_transport
    (p : ℝ) (hp : 1 ≤ p) (hInfinite : ¬ FiniteDimensional 𝕜 E)
    (K : Submodule 𝕜 E) :
    let N : E ≃ₗᵢ[𝕜] E := LinearIsometryEquiv.neg 𝕜
    K.map N.toLinearMap = K ∧
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (N : E →L[𝕜] E)) = ∞ ∧
      IsLocalMinOn
        (fun V : E ≃ₗᵢ[𝕜] E => (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (V : E →L[𝕜] E)))
        {V | K.map V.toLinearMap = K} N ∧
      ¬ IsMinOn
        (fun V : E ≃ₗᵢ[𝕜] E => (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (V : E →L[𝕜] E)))
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
  have hcost := gauge_schatten_displacement_eq_top_of_not_isCompactOperator p hp N hnoncompact
  refine ⟨hmap, hcost,
    (isLocalMin_schatten_of_not_isCompactOperator p hp N hnoncompact).isLocalMinOn _, ?_⟩
  intro hglobal
  have h := @hglobal (LinearIsometryEquiv.refl 𝕜 E) (by
    change K.map (LinearMap.id : E →ₗ[𝕜] E) = K
    simp only [Submodule.map_id])
  have hz : 1 - (LinearIsometryEquiv.refl 𝕜 E : E →L[𝕜] E) = 0 := by
    ext x
    change x - x = 0
    exact sub_self x
  change (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (N : E →L[𝕜] E)) ≤
    (OperatorIdealFamily.schatten 𝕜 p hp).gauge
      (1 - (LinearIsometryEquiv.refl 𝕜 E : E →L[𝕜] E)) at h
  rw [hcost, hz, OperatorIdealFamily.gauge_zero] at h
  exact ENNReal.zero_ne_top (le_antisymm zero_le h)

/-- In a fiber admitting finite Schatten cost, a compact-displacement
operator-norm local minimum necessarily has finite cost. The reference
need not minimize. Both fields and every finite exponent at least one
are included. -/
theorem gauge_schatten_displacement_ne_top_of_isLocalMinOn_of_compact
    (p : ℝ) (hp : 1 ≤ p)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R U : E ≃ₗᵢ[𝕜] E) (hRmap : K.map R.toLinearMap = L)
    (hUmap : K.map U.toLinearMap = L)
    (hRfinite : (OperatorIdealFamily.schatten 𝕜 p hp).gauge
      (1 - (R : E →L[𝕜] E)) ≠ ∞)
    (hUcompact : IsCompactOperator ((1 - (U : E →L[𝕜] E)) : E →L[𝕜] E))
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[𝕜] E => (OperatorIdealFamily.schatten 𝕜 p hp).gauge
        (1 - (T : E →L[𝕜] E))) {T | K.map T.toLinearMap = L} U) :
    (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : E →L[𝕜] E)) ≠ ∞ := by
  let Φ := OperatorIdealFamily.schatten 𝕜 p hp
  have hRc := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    p hp (1 - (R : E →L[𝕜] E)) hRfinite
  have hUR : IsCompactOperator
      (((U : E →L[𝕜] E) - (R : E →L[𝕜] E)) : E →L[𝕜] E) := by
    have hfac : (U : E →L[𝕜] E) - (R : E →L[𝕜] E) =
        -(1 - (U : E →L[𝕜] E)) + (1 - (R : E →L[𝕜] E)) := by abel
    rw [hfac]
    exact hUcompact.neg.add hRc
  obtain ⟨V, _, hVP, hVfinite, _, hlim⟩ :=
    exists_schatten_transport_finite_update_sequence_of_compact p hp
      K.starProjection L.starProjection R U hRfinite hUR
      ((K.map_eq_iff_conjugate_starProjection L R).mp hRmap)
      ((K.map_eq_iff_conjugate_starProjection L U).mp hUmap)
  have hVmap (n) : K.map (V n).toLinearMap = L :=
    (K.map_eq_iff_conjugate_starProjection L (V n)).mpr (hVP n)
  have hwithin : Tendsto V atTop (𝓝[{T | K.map T.toLinearMap = L}] U) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hVmap⟩
  have hbound : ∀ᶠ n in atTop,
      Φ.gauge (1 - (U : E →L[𝕜] E)) ≤ Φ.gauge (1 - (V n : E →L[𝕜] E)) := hwithin hmin
  obtain ⟨n, hn⟩ := hbound.exists
  exact ne_top_of_le_ne_top (hVfinite n) hn

end TauCeti
