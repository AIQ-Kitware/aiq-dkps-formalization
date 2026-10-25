/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSchatten
public import ForTauCeti.Analysis.Normed.Lp.ProdLp
public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction
public import Mathlib.Topology.Order.LocalExtr

/-!
# Local transport minima restrict to orthogonal blocks

Varying one unitary summand and fixing its orthogonal complement is a
continuous feasible variation of the ambient transporter. Additivity of
finite Schatten powers therefore transfers local minimality to that
summand. The coordinate isometry and the remaining block are arbitrary.
-/

public section

noncomputable section

open scoped ENNReal Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

theorem star_withLpProdMap (A : E →L[𝕜] E) (B : F →L[𝕜] F) :
    star (A.withLpProdMap 2 B) = (star A).withLpProdMap 2 (star B) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [withLpProdMap_apply, WithLp.prod_inner_apply]
  change inner 𝕜 (star A x.fst) y.fst + inner 𝕜 (star B x.snd) y.snd =
    inner 𝕜 x.fst (A y.fst) + inner 𝕜 x.snd (B y.snd)
  rw [show star A = A.adjoint from rfl, show star B = B.adjoint from rfl,
    A.adjoint_inner_left, B.adjoint_inner_left]

omit [CompleteSpace E] [CompleteSpace F] in
theorem mul_withLpProdMap (A A' : E →L[𝕜] E) (B B' : F →L[𝕜] F) :
    A.withLpProdMap 2 B * A'.withLpProdMap 2 B' = (A * A').withLpProdMap 2 (B * B') := by
  ext x
  apply WithLp.ofLp_injective 2
  simp [withLpProdMap_apply]

/-- Orthogonal sums of unitary operators are unitary. No dimension
assumption is required. -/
theorem withLpProdMap_mem_unitary {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    (hA : A ∈ unitary (E →L[𝕜] E)) (hB : B ∈ unitary (F →L[𝕜] F)) :
    A.withLpProdMap 2 B ∈ unitary (WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) := by
  have hone : (1 : E →L[𝕜] E).withLpProdMap 2 (1 : F →L[𝕜] F) = 1 := by
    ext x
    apply WithLp.ofLp_injective 2
    simp [withLpProdMap_apply]
    simpa only [WithLp.ofLp_fst, WithLp.ofLp_snd] using Prod.eta x.ofLp
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [star_withLpProdMap, mul_withLpProdMap,
      Unitary.star_mul_self_of_mem hA, Unitary.star_mul_self_of_mem hB, hone]
  · rw [star_withLpProdMap, mul_withLpProdMap,
      Unitary.mul_star_self_of_mem hA, Unitary.mul_star_self_of_mem hB, hone]

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 E F H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H] [CompleteSpace H]

/-- Local minimality of the finite Schatten transport cost is preserved
under an isometric change of coordinates. The source operator is arbitrary. -/
theorem isLocalMinOn_transport_of_conj_linearIsometryEquiv
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (e : E ≃ₗᵢ[𝕜] F) (U P : E →L[𝕜] E) (hU : U ∈ unitary (E →L[𝕜] E))
    (hmin : IsLocalMinOn
      (fun T : F →L[𝕜] F => UnitarilyInvariantSeminorm.schatten 𝕜 F F p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (F →L[𝕜] F) ∧
        T * e.conjStarAlgEquiv P * star T =
          e.conjStarAlgEquiv U * e.conjStarAlgEquiv P * star (e.conjStarAlgEquiv U)}
      (e.conjStarAlgEquiv U)) :
    IsLocalMinOn
      (fun T : E →L[𝕜] E => UnitarilyInvariantSeminorm.schatten 𝕜 E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (E →L[𝕜] E) ∧ T * P * star T = U * P * star U} U := by
  have hfeasible (A : E →L[𝕜] E)
      (hA : A ∈ unitary (E →L[𝕜] E) ∧ A * P * star A = U * P * star U) :
      e.conjStarAlgEquiv A ∈ unitary (F →L[𝕜] F) ∧
        e.conjStarAlgEquiv A * e.conjStarAlgEquiv P * star (e.conjStarAlgEquiv A) =
          e.conjStarAlgEquiv U * e.conjStarAlgEquiv P * star (e.conjStarAlgEquiv U) := by
    refine ⟨Unitary.map_mem e.conjStarAlgEquiv hA.1, ?_⟩
    simpa only [map_mul, map_star] using congrArg e.conjStarAlgEquiv hA.2
  have hc : Continuous e.conjStarAlgEquiv :=
    e.conjStarAlgEquiv.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  have h := hmin.comp_continuousOn (g := e.conjStarAlgEquiv)
    (s := {T | T ∈ unitary (E →L[𝕜] E) ∧ T * P * star T = U * P * star U})
    (fun A hA => hfeasible A hA) hc.continuousOn ⟨hU, rfl⟩
  change ∀ᶠ A in 𝓝[{T | T ∈ unitary (E →L[𝕜] E) ∧
    T * P * star T = U * P * star U}] U, _ ≤ _ at h ⊢
  filter_upwards [h] with A hA
  simpa only [Function.comp_apply,
    schatten_displacement_conj_linearIsometryEquiv e _ p hp] using hA

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 H] in
/-- An ambient local transport minimum is a local minimum on each
orthogonal unitary block when the complementary block is fixed.
The block competitors range over all unitaries carrying its source
operator to the same target; no parametrized variation is assumed. -/
theorem isLocalMinOn_block_transport_of_cost_orthogonal_sum
    (cost : (H →L[𝕜] H) → ℝ) (blockCost : (E →L[𝕜] E) → ℝ) (k : ℝ)
    (e : WithLp 2 (E × F) ≃ₗᵢ[𝕜] H)
    (U : E →L[𝕜] E) (hU : U ∈ unitary (E →L[𝕜] E)) (V : unitary (F →L[𝕜] F))
    (P₀ : E →L[𝕜] E) (P₁ : F →L[𝕜] F)
    (hcost : ∀ A : E →L[𝕜] E,
      cost (e.conjStarAlgEquiv (A.withLpProdMap 2 (V : F →L[𝕜] F))) = blockCost A + k) :
    let W := e.conjStarAlgEquiv (U.withLpProdMap 2 (V : F →L[𝕜] F))
    let P := e.conjStarAlgEquiv (P₀.withLpProdMap 2 P₁)
    IsLocalMinOn
      cost
      {T | T ∈ unitary (H →L[𝕜] H) ∧ T * P * star T = W * P * star W} W →
    IsLocalMinOn
      blockCost
      {T | T ∈ unitary (E →L[𝕜] E) ∧ T * P₀ * star T = U * P₀ * star U} U := by
  dsimp only
  let lift := fun A : E →L[𝕜] E => e.conjStarAlgEquiv (A.withLpProdMap 2 (V : F →L[𝕜] F))
  have htrans (A : E →L[𝕜] E) :
      lift A * e.conjStarAlgEquiv (P₀.withLpProdMap 2 P₁) * star (lift A) =
        e.conjStarAlgEquiv ((A * P₀ * star A).withLpProdMap 2
          ((V : F →L[𝕜] F) * P₁ * star (V : F →L[𝕜] F))) := by
    dsimp only [lift]
    rw [← map_star, ← map_mul, ← map_mul, ContinuousLinearMap.star_withLpProdMap,
      ContinuousLinearMap.mul_withLpProdMap, ContinuousLinearMap.mul_withLpProdMap]
  have hfeasible (A : E →L[𝕜] E)
      (hA : A ∈ unitary (E →L[𝕜] E) ∧ A * P₀ * star A = U * P₀ * star U) :
      lift A ∈ unitary (H →L[𝕜] H) ∧
        lift A * e.conjStarAlgEquiv (P₀.withLpProdMap 2 P₁) * star (lift A) =
          lift U * e.conjStarAlgEquiv (P₀.withLpProdMap 2 P₁) * star (lift U) := by
    refine ⟨Unitary.map_mem e.conjStarAlgEquiv
      (ContinuousLinearMap.withLpProdMap_mem_unitary hA.1 V.property), ?_⟩
    rw [htrans, htrans, hA.2]
  have hlift : Continuous lift := by
    change Continuous (fun A : E →L[𝕜] E => (e : _ →L[𝕜] H) ∘L
      (A.withLpProdMap 2 (V : F →L[𝕜] F)) ∘L (e.symm : H →L[𝕜] _))
    have hblock : Continuous (fun A : E →L[𝕜] E => A.withLpProdMap 2 (V : F →L[𝕜] F)) :=
      continuous_id.withLpProdMap continuous_const
    exact (hblock.clm_comp_const
      (e.symm : H →L[𝕜] _)).const_clm_comp (e : _ →L[𝕜] H)
  have hcostLift (A : E →L[𝕜] E) : cost (lift A) = blockCost A + k := hcost A
  intro hmin
  have h := hmin.comp_continuousOn (g := lift)
    (s := {T | T ∈ unitary (E →L[𝕜] E) ∧ T * P₀ * star T = U * P₀ * star U})
    (fun A hA => hfeasible A hA) hlift.continuousOn
    (show U ∈ {T | T ∈ unitary (E →L[𝕜] E) ∧ T * P₀ * star T = U * P₀ * star U} from
      ⟨hU, rfl⟩)
  change ∀ᶠ A in 𝓝[{T | T ∈ unitary (E →L[𝕜] E) ∧
    T * P₀ * star T = U * P₀ * star U}] U, _ ≤ _ at h ⊢
  filter_upwards [h] with A hA
  simpa only [Function.comp_apply, hcostLift, add_le_add_iff_right] using hA

/-- An ambient local transport minimum is a local minimum on each
orthogonal unitary block when the complementary block is fixed.
The block competitors range over all unitaries carrying its source
operator to the same target; no parametrized variation is assumed. -/
theorem isLocalMinOn_block_transport_of_orthogonal_sum
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (e : WithLp 2 (E × F) ≃ₗᵢ[𝕜] H)
    (U : E →L[𝕜] E) (hU : U ∈ unitary (E →L[𝕜] E)) (V : unitary (F →L[𝕜] F))
    (P₀ : E →L[𝕜] E) (P₁ : F →L[𝕜] F) :
    let W := e.conjStarAlgEquiv (U.withLpProdMap 2 (V : F →L[𝕜] F))
    let P := e.conjStarAlgEquiv (P₀.withLpProdMap 2 P₁)
    IsLocalMinOn
      (fun T : H →L[𝕜] H => UnitarilyInvariantSeminorm.schatten 𝕜 H H p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (H →L[𝕜] H) ∧ T * P * star T = W * P * star W} W →
    IsLocalMinOn
      (fun T : E →L[𝕜] E => UnitarilyInvariantSeminorm.schatten 𝕜 E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (E →L[𝕜] E) ∧ T * P₀ * star T = U * P₀ * star U} U := by
  apply isLocalMinOn_block_transport_of_cost_orthogonal_sum
    (fun T : H →L[𝕜] H => UnitarilyInvariantSeminorm.schatten 𝕜 H H p
      (LinearMap.id - T.toLinearMap) ^ p.toReal)
    (fun T : E →L[𝕜] E => UnitarilyInvariantSeminorm.schatten 𝕜 E E p
      (LinearMap.id - T.toLinearMap) ^ p.toReal)
    (UnitarilyInvariantSeminorm.schatten 𝕜 F F p
      (LinearMap.id - (V : F →L[𝕜] F).toLinearMap) ^ p.toReal)
    e U hU V P₀ P₁
  intro A
  rw [schatten_displacement_conj_linearIsometryEquiv e _ p hp,
    schatten_displacement_rpow_withLpProdMap _ _ p hp]

/-- Local minimality descends to an actual common invariant subspace
of a unitary transporter and a self-adjoint source operator. Its unitary
restriction, complementary unitary and orthogonal coordinates are all
constructed from invariance. No block decomposition is supplied. -/
theorem exists_isLocalMinOn_restriction_of_invariant
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : E ≃ₗᵢ[𝕜] E) (P : E →L[𝕜] E) (hP : IsSelfAdjoint P)
    (N : Submodule 𝕜 E) (hTN : ∀ x ∈ N, T x ∈ N) (hPN : ∀ x ∈ N, P x ∈ N)
    (hmin : IsLocalMinOn
      (fun W : E →L[𝕜] E => UnitarilyInvariantSeminorm.schatten 𝕜 E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[𝕜] E) ∧
        W * P * star W = (T : E →L[𝕜] E) * P * star (T : E →L[𝕜] E)}
      (T : E →L[𝕜] E)) :
    let P₀ := (P.toLinearMap.restrict hPN).toContinuousLinearMap
    ∃ V : N ≃ₗᵢ[𝕜] N, (∀ x : N, (V x : E) = T x) ∧
      IsLocalMinOn
        (fun W : N →L[𝕜] N => UnitarilyInvariantSeminorm.schatten 𝕜 N N p
          (LinearMap.id - W.toLinearMap) ^ p.toReal)
        {W | W ∈ unitary (N →L[𝕜] N) ∧
          W * P₀ * star W = (V : N →L[𝕜] N) * P₀ * star (V : N →L[𝕜] N)}
        (V : N →L[𝕜] N) := by
  obtain ⟨V, hV, _, hred⟩ := T.exists_restriction_of_finite_invariant N hTN
  have hTorth : ∀ x ∈ Nᗮ, T x ∈ Nᗮ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem T.toLinearMap).mp
      hred.orthogonal_mem_invtSubmodule
  obtain ⟨V₁, hV₁, _, _⟩ := T.exists_restriction_of_finite_invariant Nᗮ hTorth
  have hPorth : ∀ x ∈ Nᗮ, P x ∈ Nᗮ := by
    intro x hx y hy
    exact (hP.isSymmetric y x).symm.trans (hx (P y) (hPN y hy))
  let P₀ : N →L[𝕜] N := (P.toLinearMap.restrict hPN).toContinuousLinearMap
  let P₁ : Nᗮ →L[𝕜] Nᗮ := (P.toLinearMap.restrict hPorth).toContinuousLinearMap
  let e := N.orthogonalDecomposition.symm
  have hTblock : e.conjStarAlgEquiv
      ((V : N →L[𝕜] N).withLpProdMap 2 (V₁ : Nᗮ →L[𝕜] Nᗮ)) =
        (T : E →L[𝕜] E) := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.symm_apply_apply,
      ContinuousLinearMap.withLpProdMap_apply]
    change (V y.fst : E) + (V₁ y.snd : E) = T ((y.fst : E) + (y.snd : E))
    rw [map_add, hV, hV₁]
  have hPblock : e.conjStarAlgEquiv (P₀.withLpProdMap 2 P₁) = P := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.symm_apply_apply,
      ContinuousLinearMap.withLpProdMap_apply]
    change P (y.fst : E) + P (y.snd : E) = P ((y.fst : E) + (y.snd : E))
    exact (map_add P _ _).symm
  refine ⟨V, hV, ?_⟩
  apply isLocalMinOn_block_transport_of_orthogonal_sum p hp e
    (V : N →L[𝕜] N) (Unitary.linearIsometryEquiv.symm V).property
    (Unitary.linearIsometryEquiv.symm V₁) P₀ P₁
  simpa only [Unitary.coe_symm_linearIsometryEquiv_apply, hTblock, hPblock] using hmin

end TauCeti
