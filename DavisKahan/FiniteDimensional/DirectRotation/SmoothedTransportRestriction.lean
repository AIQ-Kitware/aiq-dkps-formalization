/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedBlockCost

/-!
# Local Charbonnier minima restrict to actual reducing subspaces

Fixing the complementary unitary and varying a common invariant subspace
is a continuous feasible ambient variation. Literal cost additivity
transfers local minimality, without any supplied coordinate decomposition.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped Topology

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]

/-- Ambient local minimality descends to all feasible unitary competitors
on an orthogonal block, with the complementary block fixed. -/
theorem isLocalMinOn_block_transport_of_orthogonal_sum_complex
    (tau : ℝ) (e : WithLp 2 (E × F) ≃ₗᵢ[ℂ] H)
    (U : E →L[ℂ] E) (hU : U ∈ unitary (E →L[ℂ] E)) (V : unitary (F →L[ℂ] F))
    (P₀ : E →L[ℂ] E) (P₁ : F →L[ℂ] F) :
    let W := e.conjStarAlgEquiv (U.withLpProdMap 2 (V : F →L[ℂ] F))
    let P := e.conjStarAlgEquiv (P₀.withLpProdMap 2 P₁)
    IsLocalMinOn (fun T : H →L[ℂ] H => smoothedDisplacementCost tau T.toLinearMap)
      {T | T ∈ unitary (H →L[ℂ] H) ∧ T * P * star T = W * P * star W} W →
    IsLocalMinOn (fun T : E →L[ℂ] E => smoothedDisplacementCost tau T.toLinearMap)
      {T | T ∈ unitary (E →L[ℂ] E) ∧ T * P₀ * star T = U * P₀ * star U} U := by
  apply isLocalMinOn_block_transport_of_cost_orthogonal_sum
    (fun T : H →L[ℂ] H => smoothedDisplacementCost tau T.toLinearMap)
    (fun T : E →L[ℂ] E => smoothedDisplacementCost tau T.toLinearMap)
    (smoothedDisplacementCost tau (V : F →L[ℂ] F).toLinearMap) e U hU V P₀ P₁
  intro A
  rw [smoothedDisplacementCost_conj_linearIsometryEquiv_complex,
    smoothedDisplacementCost_withLpProdMap_complex]

/-- Local minimality descends to an actual common invariant subspace
of a unitary transporter and a self-adjoint source operator. Its unitary
restriction, complementary unitary and orthogonal coordinates are all
constructed from invariance. No block decomposition is supplied. -/
theorem exists_isLocalMinOn_restriction_of_invariant_complex
    (tau : ℝ)
    (T : E ≃ₗᵢ[ℂ] E) (P : E →L[ℂ] E) (hP : IsSelfAdjoint P)
    (N : Submodule ℂ E) (hTN : ∀ x ∈ N, T x ∈ N) (hPN : ∀ x ∈ N, P x ∈ N)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧
        W * P * star W = (T : E →L[ℂ] E) * P * star (T : E →L[ℂ] E)}
      (T : E →L[ℂ] E)) :
    let P₀ := (P.toLinearMap.restrict hPN).toContinuousLinearMap
    ∃ V : N ≃ₗᵢ[ℂ] N, (∀ x : N, (V x : E) = T x) ∧
      IsLocalMinOn
        (fun W : N →L[ℂ] N => smoothedDisplacementCost tau W.toLinearMap)
        {W | W ∈ unitary (N →L[ℂ] N) ∧
          W * P₀ * star W = (V : N →L[ℂ] N) * P₀ * star (V : N →L[ℂ] N)}
        (V : N →L[ℂ] N) := by
  obtain ⟨V, hV, _, hred⟩ := T.exists_restriction_of_finite_invariant N hTN
  have hTorth : ∀ x ∈ Nᗮ, T x ∈ Nᗮ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem T.toLinearMap).mp
      hred.orthogonal_mem_invtSubmodule
  obtain ⟨V₁, hV₁, _, _⟩ := T.exists_restriction_of_finite_invariant Nᗮ hTorth
  have hPorth : ∀ x ∈ Nᗮ, P x ∈ Nᗮ := by
    intro x hx y hy
    exact (hP.isSymmetric y x).symm.trans (hx (P y) (hPN y hy))
  let P₀ : N →L[ℂ] N := (P.toLinearMap.restrict hPN).toContinuousLinearMap
  let P₁ : Nᗮ →L[ℂ] Nᗮ := (P.toLinearMap.restrict hPorth).toContinuousLinearMap
  let e := N.orthogonalDecomposition.symm
  have hTblock : e.conjStarAlgEquiv
      ((V : N →L[ℂ] N).withLpProdMap 2 (V₁ : Nᗮ →L[ℂ] Nᗮ)) =
        (T : E →L[ℂ] E) := by
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
  apply isLocalMinOn_block_transport_of_orthogonal_sum_complex tau e
    (V : N →L[ℂ] N) (Unitary.linearIsometryEquiv.symm V).property
    (Unitary.linearIsometryEquiv.symm V₁) P₀ P₁
  simpa only [Unitary.coe_symm_linearIsometryEquiv_apply, hTblock, hPblock] using hmin

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
