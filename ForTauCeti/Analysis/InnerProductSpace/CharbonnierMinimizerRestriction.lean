/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReplaceFiniteTransport
public import ForTauCeti.Analysis.OperatorIdeal.ReducingTrace

/-!
# Actual finite restrictions of Hilbert-space Charbonnier minimizers

Every finite source-reducing sector invariant under a finite-cost global
minimizer carries a global minimizer of the actual restricted pair.
Exact cost additivity allows cancellation of the unchanged finite-cost
tail. The finiteness hypothesis is essential to this cancellation.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- A unique ambient Charbonnier minimizer has finite cost. If all
feasible costs were infinite, composing a transporter with negation
would give another minimizer, unless the entire space were zero. -/
theorem charbonnierCost_displacement_ne_top_of_unique_transport
    (tau : ℝ) (hτ : 0 ≤ tau) (K L : Submodule 𝕜 E)
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hmin : ∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≤
        (1 - (T : E →L[𝕜] E)).charbonnierCost tau)
    (huni : ∀ T : E ≃ₗᵢ[𝕜] E,
      (K.map T.toLinearMap = L ∧
        ∀ W : E ≃ₗᵢ[𝕜] E, K.map W.toLinearMap = L →
          (1 - (T : E →L[𝕜] E)).charbonnierCost tau ≤
            (1 - (W : E →L[𝕜] E)).charbonnierCost tau) → T = U) :
    (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≠ ∞ := by
  intro htop
  have hall (T : E ≃ₗᵢ[𝕜] E) (hT : K.map T.toLinearMap = L) :
      (1 - (T : E →L[𝕜] E)).charbonnierCost tau = ∞ := by
    apply top_unique
    simpa only [htop] using hmin T hT
  let N := U.trans (LinearIsometryEquiv.neg 𝕜)
  have hNmap : K.map N.toLinearMap = L := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      change -(U x) ∈ L
      apply L.neg_mem
      rw [← hmap]
      exact Submodule.mem_map_of_mem hx
    · intro y hy
      have hny : -y ∈ K.map U.toLinearMap := by
        rw [hmap]
        exact L.neg_mem hy
      obtain ⟨x, hx, hxy⟩ := hny
      refine ⟨x, hx, ?_⟩
      change -(U x) = y
      change U x = -y at hxy
      rw [hxy, neg_neg]
  have hNU : N = U := huni N ⟨hNmap, fun W hW => by rw [hall N hNmap, hall W hW]⟩
  have hzero (y : E) : y = 0 := by
    have hy : -y = y := by
      have h := congrArg (fun T : E ≃ₗᵢ[𝕜] E => T (U.symm y)) hNU
      change -(U (U.symm y)) = U (U.symm y) at h
      rwa [U.apply_symm_apply] at h
    have htwo : (2 : 𝕜) • y = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr hy.symm
    exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero
  have hdisp : 1 - (U : E →L[𝕜] E) = 0 := by
    ext x
    exact hzero _
  rw [hdisp, (ContinuousLinearMap.charbonnierCost_eq_zero_iff tau hτ _).mpr rfl] at htop
  exact ENNReal.zero_ne_top htop

/-- Finite-cost global optimality descends to every actual reducing
sector, including an infinite-dimensional one. Competitors on that
sector extend with exactly the original complementary action. -/
theorem exists_charbonnier_minimizing_reducing_restriction
    (tau : ℝ) (hτ : 0 < tau)
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] [CompleteSpace M]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≤
        (1 - (T : E →L[𝕜] E)).charbonnierCost tau)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hUM : M.IsReducing U.toLinearMap) :
    ∃ V : M ≃ₗᵢ[𝕜] M,
      (∀ x : M, (V x : E) = U x) ∧
      (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
      ∀ W : M ≃ₗᵢ[𝕜] M,
        (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
        (1 - (V : M →L[𝕜] M)).charbonnierCost tau ≤
          (1 - (W : M →L[𝕜] M)).charbonnierCost tau := by
  let := K.hasOrthogonalProjection_comap_subtype_of_complete M
  let := L.hasOrthogonalProjection_comap_subtype_of_complete M
  obtain ⟨V, hV, _⟩ := U.exists_restriction_of_reducing M hUM
  have hlocal := K.map_comap_subtype_of_isometry_restriction L M U V hmap hV
  have hsplit := ContinuousLinearMap.charbonnierCost_unitary_displacement_eq_block_add_tail
    tau hτ M U U V (fun x => (hV x).symm) (fun _ _ => rfl)
  have htail : (Mᗮ.orthogonalProjectionOnto ∘L
      (1 - (U : E →L[𝕜] E)) ∘L Mᗮ.subtypeL).charbonnierCost tau ≠ ∞ := by
    rw [hsplit] at hfinite
    exact (ENNReal.add_ne_top.mp hfinite).2
  refine ⟨V, hV, hlocal, ?_⟩
  intro W hW
  obtain ⟨T, hTmap, hTM, hTtail⟩ :=
    K.exists_transport_replacing_reducing_block L M hK U hmap hUM W hW
  have hsplitT := ContinuousLinearMap.charbonnierCost_unitary_displacement_eq_block_add_tail
    tau hτ M T U W hTM hTtail
  have hle := hmin T hTmap
  rw [hsplit, hsplitT] at hle
  exact (ENNReal.add_le_add_iff_right htail).mp hle

/-- Global finite-cost Charbonnier optimality descends to every actual
finite reducing sector. Neither ambient finite dimension nor a
prescribed block form of the competing ambient transports is assumed. -/
theorem exists_charbonnier_minimizing_finite_restriction
    (tau : ℝ) (hτ : 0 < tau)
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 M]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≤
        (1 - (T : E →L[𝕜] E)).charbonnierCost tau)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hUM : ∀ x ∈ M, U x ∈ M) :
    ∃ V : M ≃ₗᵢ[𝕜] M,
      (∀ x : M, (V x : E) = U x) ∧
      (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
      ∀ W : M ≃ₗᵢ[𝕜] M,
        (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
        (1 - (V : M →L[𝕜] M)).charbonnierCost tau ≤
          (1 - (W : M →L[𝕜] M)).charbonnierCost tau := by
  obtain ⟨_, _, _, hred⟩ := U.exists_restriction_of_finite_invariant M hUM
  exact exists_charbonnier_minimizing_reducing_restriction tau hτ K L M U hmap hfinite hmin hK hred


/-- With the same complementary action as a global minimizing
reference, global optimality is equivalent to optimality of the actual
finite restriction. The tail may have infinite rank. -/
theorem charbonnier_minimal_iff_restriction_of_minimizing_reference_tail
    (tau : ℝ) (hτ : 0 < tau)
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 M]
    (U R : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hRmap : K.map R.toLinearMap = L)
    (hfinite : (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≠ ∞)
    (hRmin : ∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (1 - (R : E →L[𝕜] E)).charbonnierCost tau ≤
        (1 - (T : E →L[𝕜] E)).charbonnierCost tau)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hRM : ∀ x ∈ M, R x ∈ M)
    (htail : ∀ x ∈ Mᗮ, U x = R x)
    (V : M ≃ₗᵢ[𝕜] M) (hV : ∀ x : M, (V x : E) = U x) :
    (∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≤
        (1 - (T : E →L[𝕜] E)).charbonnierCost tau) ↔
    (∀ W : M ≃ₗᵢ[𝕜] M,
      (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
      (1 - (V : M →L[𝕜] M)).charbonnierCost tau ≤
        (1 - (W : M →L[𝕜] M)).charbonnierCost tau) := by
  constructor
  · intro hmin
    obtain ⟨V', hV', _, hmin'⟩ := exists_charbonnier_minimizing_finite_restriction tau hτ K L M
      U hmap hfinite hmin hK (fun x hx => by rw [← hV ⟨x, hx⟩]; exact (V ⟨x, hx⟩).property)
    have heq : V' = V := by
      ext x
      exact (hV' x).trans (hV x).symm
    simpa only [heq] using hmin'
  · intro hmin T hT
    obtain ⟨W, hW, _, _⟩ := R.exists_restriction_of_finite_invariant M hRM
    have hWmap := K.map_comap_subtype_of_isometry_restriction L M R W hRmap hW
    have hUcost := ContinuousLinearMap.charbonnierCost_unitary_displacement_eq_block_add_tail
      tau hτ M U R V (fun x => (hV x).symm) htail
    have hRcost := ContinuousLinearMap.charbonnierCost_unitary_displacement_eq_block_add_tail
      tau hτ M R R W (fun x => (hW x).symm) (fun _ _ => rfl)
    have hle : (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≤
      (1 - (R : E →L[𝕜] E)).charbonnierCost tau := by
      rw [hUcost, hRcost]
      exact add_le_add (hmin W hWmap) le_rfl
    exact hle.trans (hRmin T hT)

/-- An angle-preserving finite-cost global Charbonnier optimizer fixes
all common source and common orthogonal directions. This works over
both fields at every positive smoothing scale, in arbitrary dimension. -/
theorem apply_eq_self_of_projections_eq_of_charbonnier_minimal_of_commute
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≤
        (1 - (T : E →L[𝕜] E)).charbonnierCost tau)
    (hUS : Commute (U : E →L[𝕜] E) (K.sinAngleOperator L))
    (x : E) (hx : K.starProjection x = L.starProjection x) : U x = x := by
  let S := K.sinAngleOperator L
  let Z := S.ker
  let := K.hasOrthogonalProjection_comap_subtype_of_complete Z
  let := L.hasOrthogonalProjection_comap_subtype_of_complete Z
  have hPQ (y : Z) : K.starProjection (y : E) = L.starProjection y := by
    have h := K.norm_sinAngleOperator_apply L (y : E)
    rw [show K.sinAngleOperator L (y : E) = 0 from y.property, norm_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)
  have hK : Z.IsReducing K.starProjection.toLinearMap := by
    apply (K.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule Z).mpr
    intro y hy
    change S (K.starProjection y) = 0
    have h := congrArg (fun A : E →L[𝕜] E => A y)
      (K.commute_starProjection_sinAngleOperator L).eq
    change K.starProjection (S y) = S (K.starProjection y) at h
    rw [← h, show S y = 0 from hy, map_zero]
  have hpair : K.comap Z.subtype = L.comap Z.subtype := by
    apply Submodule.ext
    intro y
    change (y : E) ∈ K ↔ (y : E) ∈ L
    rw [← K.starProjection_eq_self_iff, hPQ y, L.starProjection_eq_self_iff]
  obtain ⟨V, hV, _, hVmin⟩ := exists_charbonnier_minimizing_reducing_restriction tau hτ K L Z
    U hmap hfinite hmin hK
      (U.isReducing_ker_of_commute_selfAdjoint S
        (K.isPositive_sinAngleOperator L).isSelfAdjoint hUS)
  have hzero := hVmin (LinearIsometryEquiv.refl 𝕜 Z) (by
    change (K.comap Z.subtype).map (LinearMap.id : Z →ₗ[𝕜] Z) = L.comap Z.subtype
    rwa [Submodule.map_id])
  have hVzero : 1 - (V : Z →L[𝕜] Z) = 0 := by
    apply (ContinuousLinearMap.charbonnierCost_eq_zero_iff tau hτ.le _).mp
    apply le_antisymm _ zero_le
    change (1 - (V : Z →L[𝕜] Z)).charbonnierCost tau ≤
      (1 - (1 : Z →L[𝕜] Z)).charbonnierCost tau at hzero
    rw [sub_self, (ContinuousLinearMap.charbonnierCost_eq_zero_iff tau hτ.le
      (0 : Z →L[𝕜] Z)).mpr rfl] at hzero
    exact hzero
  have hxZ : x ∈ Z := by
    change S x = 0
    apply norm_eq_zero.mp
    rw [K.norm_sinAngleOperator_apply L, hx, sub_self, norm_zero]
  have hvx := congrArg (fun A : Z →L[𝕜] Z => A ⟨x, hxZ⟩) hVzero
  have hv : V ⟨x, hxZ⟩ = ⟨x, hxZ⟩ := (sub_eq_zero.mp hvx).symm
  exact (hV ⟨x, hxZ⟩).symm.trans (congrArg Subtype.val hv)

end TauCeti
