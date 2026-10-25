/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSchatten
public import ForTauCeti.Analysis.Normed.Lp.ProdLp
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
  have hcost (A : E →L[𝕜] E) : UnitarilyInvariantSeminorm.schatten 𝕜 H H p
      (LinearMap.id - (lift A).toLinearMap) ^ p.toReal =
      UnitarilyInvariantSeminorm.schatten 𝕜 E E p (LinearMap.id - A.toLinearMap) ^ p.toReal +
        UnitarilyInvariantSeminorm.schatten 𝕜 F F p
          (LinearMap.id - (V : F →L[𝕜] F).toLinearMap) ^ p.toReal := by
    dsimp only [lift]
    rw [schatten_displacement_conj_linearIsometryEquiv e _ p hp,
      schatten_displacement_rpow_withLpProdMap _ _ p hp]
  intro hmin
  have h := hmin.comp_continuousOn (g := lift)
    (s := {T | T ∈ unitary (E →L[𝕜] E) ∧ T * P₀ * star T = U * P₀ * star U})
    (fun A hA => hfeasible A hA) hlift.continuousOn
    (show U ∈ {T | T ∈ unitary (E →L[𝕜] E) ∧ T * P₀ * star T = U * P₀ * star U} from
      ⟨hU, rfl⟩)
  change ∀ᶠ A in 𝓝[{T | T ∈ unitary (E →L[𝕜] E) ∧
    T * P₀ * star T = U * P₀ * star U}] U, _ ≤ _ at h ⊢
  filter_upwards [h] with A hA
  simpa only [Function.comp_apply, hcost, add_le_add_iff_right] using hA

end TauCeti
