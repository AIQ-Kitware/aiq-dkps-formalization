/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierOptimizerAngles

/-!
# Fixed directions at finite-cost Hilbert Charbonnier local minima

The full zero-gradient kernel has compact reflecting displacement.
Its finite source-reducing support inherits finite global optimality.
Together with the positive gradient cutoffs, this proves that a local
minimum preserving a subspace is identity. Apply this to the zero-angle
sector to retain arbitrary common and common-orthogonal directions.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

private theorem eq_one_of_charbonnier_minimal_self_complex
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (tau : ℝ) (hτ : 0 < tau) (K : Submodule ℂ F) (U : F ≃ₗᵢ[ℂ] F)
    (hmin : ∀ T : F ≃ₗᵢ[ℂ] F, K.map T.toLinearMap = K →
      (1 - (U : F →L[ℂ] F)).charbonnierCost tau ≤
        (1 - (T : F →L[ℂ] F)).charbonnierCost tau) : (U : F →L[ℂ] F) = 1 := by
  have h := hmin (LinearIsometryEquiv.refl ℂ F) (by
    change K.map (LinearMap.id : F →ₗ[ℂ] F) = K
    simp only [Submodule.map_id])
  have hz : 1 - (LinearIsometryEquiv.refl ℂ F : F →L[ℂ] F) = 0 := by
    ext x
    change x - x = 0
    exact sub_self x
  rw [hz, (ContinuousLinearMap.charbonnierCost_eq_zero_iff tau hτ.le _).mpr rfl] at h
  exact (sub_eq_zero.mp ((ContinuousLinearMap.charbonnierCost_eq_zero_iff tau hτ.le _).mp
    (le_antisymm h zero_le))).symm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Identity is the only finite-cost operator-norm local minimum among
unitaries preserving a prescribed subspace, in arbitrary Hilbert dimension.
The full infinite zero-gradient sector is included. -/
theorem eq_one_of_charbonnier_isLocalMinOn_self_transport_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = K)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
      {T | K.map T.toLinearMap = K} U) : (U : E →L[ℂ] E) = 1 := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  let A := G.modulus
  have hSp := (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hfinite
  have hGc : IsCompactOperator G := isCompactOperator_smoothedUnitaryGradient tau hτ U (by
    rw [← neg_sub 1 (U : E →L[ℂ] E)]
    exact (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
      2 (by norm_num) (1 - (U : E →L[ℂ] E)) hSp).neg)
  have hAc : IsCompactOperator A := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hseq : A.singularValue = G.singularValue :=
      funext (fun n => ContinuousLinearMap.singularValue_modulus G n)
    rw [hseq]
    exact hGc.tendsto_singularValue
  apply eq_of_eq_on_ker_and_positive_eigenSpans hAc G.isSelfAdjoint_modulus
    G.isPositive_modulus.re_inner_nonneg_left
  · rw [show A.ker = G.ker from G.ker_modulus]
    let Z := G.ker
    let K₀ := K.comap Z.subtype
    let := K.hasOrthogonalProjection_comap_subtype_of_complete Z
    have hK : Z.IsReducing K.starProjection.toLinearMap :=
      K.isReducing_ker_of_reflection_conjugate_eq_neg G
        (isSelfAdjoint_smoothedUnitaryGradient _ _)
        (gradient_reflection_conjugate_eq_neg_of_charbonnier_isLocalMinOn_complex
          tau hτ K K U hmap hfinite hmin)
    obtain ⟨V, hV, _, hself⟩ :=
      exists_selfAdjoint_unitary_restriction_smoothed_gradient_kernel tau hτ U
    obtain ⟨V', hV', hlocal, hVfinite, hVmin⟩ :=
      exists_charbonnier_locally_minimizing_reducing_restriction tau hτ K K Z U hmap
        hfinite hmin hK (U.isReducing_of_restriction Z V hV)
    have heq : V' = V := by
      ext x
      exact (hV' x).trans (hV x).symm
    subst V'
    have hVc := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top 2 (by norm_num)
      (1 - (V : Z →L[ℂ] Z))
      ((ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hVfinite)
    obtain ⟨n, hn⟩ := V.exists_rank_displacement_le_of_isSelfAdjoint hself hVc
    obtain ⟨M, hM, _, hMK, hMV, _, hfix⟩ := exists_finite_transport_support K₀ ⊥ V n hn
    let : FiniteDimensional ℂ M := hM
    obtain ⟨W, hW, hWmap, _, hWlocal⟩ :=
      exists_charbonnier_locally_minimizing_finite_restriction tau hτ K₀ K₀ M V
        hlocal hVfinite hVmin hMK hMV.mem_invtSubmodule
    have hWmin := charbonnier_isMin_of_isLocalMinOn_finite_complex tau hτ
      (K₀.comap M.subtype) (K₀.comap M.subtype) W hWmap hWlocal
    have hWone := eq_one_of_charbonnier_minimal_self_complex tau hτ (K₀.comap M.subtype) W hWmin
    have hVhead (y : M) : V (y : Z) = (y : Z) := by
      have h := congrArg (fun B : M →L[ℂ] M => B y) hWone
      exact (hW y).symm.trans (congrArg Subtype.val h)
    have hVfix (y : Z) : V y = y := by
      calc
        V y = V (M.starProjection y + Mᗮ.starProjection y) :=
          congrArg V (M.starProjection_add_starProjection_orthogonal y).symm
        _ = M.starProjection y + Mᗮ.starProjection y := by
          rw [map_add]
          exact congrArg₂ (fun a b : Z => a + b)
            (hVhead ⟨_, M.starProjection_apply_mem y⟩) (hfix _ (Mᗮ.starProjection_apply_mem y))
        _ = y := M.starProjection_add_starProjection_orthogonal y
    intro x hx
    exact (hV ⟨x, hx⟩).symm.trans (congrArg Subtype.val (hVfix ⟨x, hx⟩))
  · intro ε hε x hx
    obtain ⟨hM, _, _, _, _, V, hV, _, hlocal, hVmin⟩ :=
      exists_charbonnier_minimizing_restriction_on_gradient_cutoff_of_isLocalMinOn_complex
        tau hτ K K U hmap hfinite hmin ε hε
    let M := eigenSpan A (Set.Ioi ε)
    let : FiniteDimensional ℂ M := hM
    have hcost (W : M ≃ₗᵢ[ℂ] M) : (1 - (W : M →L[ℂ] M)).charbonnierCost tau =
        ENNReal.ofReal (smoothedDisplacementCost tau W.toLinearMap) := by
      rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
      rfl
    have hnative (W : M ≃ₗᵢ[ℂ] M)
        (hW : (K.comap M.subtype).map W.toLinearMap = K.comap M.subtype) :
        (1 - (V : M →L[ℂ] M)).charbonnierCost tau ≤
          (1 - (W : M →L[ℂ] M)).charbonnierCost tau := by
      rw [hcost, hcost]
      exact ENNReal.ofReal_le_ofReal (hVmin W hW)
    have hVone := eq_one_of_charbonnier_minimal_self_complex tau hτ (K.comap M.subtype) V hnative
    exact (hV ⟨x, hx⟩).symm.trans (congrArg Subtype.val
      (congrArg (fun B : M →L[ℂ] M => B ⟨x, hx⟩) hVone))

/-- Every finite-cost operator-norm local optimizer fixes all directions
on which the two projections agree, including infinite common-source
and common-orthogonal subspaces. -/
theorem apply_eq_self_of_projections_eq_of_charbonnier_isLocalMinOn_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
      {T | K.map T.toLinearMap = L} U)
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
    have h := congrArg (fun B : E →L[ℂ] E => B y)
      (K.commute_starProjection_sinAngleOperator L).eq
    change K.starProjection (S y) = S (K.starProjection y) at h
    rw [← h, show S y = 0 from hy, map_zero]
  have hpair : K.comap Z.subtype = L.comap Z.subtype := by
    apply Submodule.ext
    intro y
    change (y : E) ∈ K ↔ (y : E) ∈ L
    rw [← K.starProjection_eq_self_iff, hPQ y, L.starProjection_eq_self_iff]
  obtain ⟨V, hV, hlocal, hVfinite, hVmin⟩ :=
    exists_charbonnier_locally_minimizing_reducing_restriction tau hτ K L Z U hmap
      hfinite hmin hK (U.isReducing_ker_of_commute_selfAdjoint S
        (K.isPositive_sinAngleOperator L).isSelfAdjoint
        (commute_sinAngleOperator_of_charbonnier_isLocalMinOn_complex tau hτ K L U hmap hfinite hmin))
  rw [← hpair] at hlocal hVmin
  have hVone := eq_one_of_charbonnier_isLocalMinOn_self_transport_complex tau hτ
    (K.comap Z.subtype) V hlocal hVfinite hVmin
  have hxZ : x ∈ Z := by
    change S x = 0
    apply norm_eq_zero.mp
    rw [K.norm_sinAngleOperator_apply L, hx, sub_self, norm_zero]
  exact (hV ⟨x, hxZ⟩).symm.trans (congrArg Subtype.val
    (congrArg (fun B : Z →L[ℂ] Z => B ⟨x, hxZ⟩) hVone))

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
