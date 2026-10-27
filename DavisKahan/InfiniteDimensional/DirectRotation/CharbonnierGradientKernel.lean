/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierGradientCutoff
public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierGradientKernelHilbert
public import ForTauCeti.Analysis.InnerProductSpace.CompactReflection

/-!
# The full zero-gradient sector of every Hilbert Charbonnier optimizer

The actual kernel restriction inherits unrestricted optimality and is a
self-adjoint unitary with finite-rank displacement. Its nonidentity
part lies in a finite source-reducing support, whose actual restriction
is a finite global optimizer. The remaining kernel is fixed pointwise.
Right-angle reflecting choices are retained throughout.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Every optimizer's full gradient kernel consists of a finite
optimizing reflection support and an exactly fixed complement. No
finite-dimensionality of the full kernel is assumed or concluded. -/
theorem exists_finite_reflecting_support_on_gradient_kernel_of_charbonnier_minimal
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau) :
    let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
    let Z := G.ker
    let K₀ := K.comap Z.subtype
    let L₀ := L.comap Z.subtype
    ∃ V : Z ≃ₗᵢ[ℂ] Z,
      (∀ x : Z, (V x : E) = U x) ∧ IsSelfAdjoint (V : Z →L[ℂ] Z) ∧
      K₀.map V.toLinearMap = L₀ ∧
      (∀ W : Z ≃ₗᵢ[ℂ] Z, K₀.map W.toLinearMap = L₀ →
        (1 - (V : Z →L[ℂ] Z)).charbonnierCost tau ≤
          (1 - (W : Z →L[ℂ] Z)).charbonnierCost tau) ∧
      ∃ M : Submodule ℂ Z, ∃ hM : FiniteDimensional ℂ M,
        let _ : FiniteDimensional ℂ M := hM
        let _ := K.hasOrthogonalProjection_comap_subtype_of_complete Z
        M.IsReducing K₀.starProjection.toLinearMap ∧ M.IsReducing V.toLinearMap ∧
        (∀ x ∈ Mᗮ, V x = x) ∧
        ∃ W : M ≃ₗᵢ[ℂ] M,
          (∀ x : M, (W x : Z) = V x) ∧
          (K₀.comap M.subtype).map W.toLinearMap = L₀.comap M.subtype ∧
          ∀ T : M ≃ₗᵢ[ℂ] M,
            (K₀.comap M.subtype).map T.toLinearMap = L₀.comap M.subtype →
            smoothedDisplacementCost (E := M) tau W.toLinearMap ≤
              smoothedDisplacementCost (E := M) tau T.toLinearMap := by
  dsimp only
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  let Z := G.ker
  let K₀ := K.comap Z.subtype
  let L₀ := L.comap Z.subtype
  let := K.hasOrthogonalProjection_comap_subtype_of_complete Z
  let := L.hasOrthogonalProjection_comap_subtype_of_complete Z
  have hK : Z.IsReducing K.starProjection.toLinearMap :=
    K.isReducing_ker_of_reflection_conjugate_eq_neg G
      (isSelfAdjoint_smoothedUnitaryGradient _ _)
      (gradient_reflection_conjugate_eq_neg_of_charbonnier_minimal tau hτ K L U hmap hfinite hmin)
  obtain ⟨V, hV, _, hself⟩ :=
    exists_selfAdjoint_unitary_restriction_smoothed_gradient_kernel tau hτ U
  have hUred : Z.IsReducing U.toLinearMap := U.isReducing_of_restriction Z V hV
  obtain ⟨V', hV', hlocal', hlocalmin'⟩ := exists_charbonnier_minimizing_reducing_restriction
    tau hτ K L Z U hmap hfinite hmin hK hUred
  have heq : V' = V := by
    ext x
    exact (hV' x).trans (hV x).symm
  subst V'
  have hdisp : (1 - (V : Z →L[ℂ] Z)) =
      Z.orthogonalProjectionOnto ∘L (1 - (U : E →L[ℂ] E)) ∘L Z.subtypeL := by
    apply ContinuousLinearMap.ext
    intro x
    change x - V x = Z.orthogonalProjectionOnto ((x : E) - U x)
    rw [← hV, map_sub, Z.orthogonalProjectionOnto_mem_subspace_eq_self,
      Z.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hSp := (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hfinite
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) (1 - (U : E →L[ℂ] E)) hSp
  have hVc : IsCompactOperator ((1 : Z →L[ℂ] Z) - (V : Z →L[ℂ] Z)) := by
    rw [hdisp]
    exact (hcompact.comp_clm Z.subtypeL).clm_comp Z.orthogonalProjectionOnto
  obtain ⟨n, hn⟩ := V.exists_rank_displacement_le_of_isSelfAdjoint hself hVc
  obtain ⟨M, hM, _, hMK, hMV, _, hfix⟩ :=
    TauCeti.exists_finite_transport_support K₀ ⊥ V n hn
  let : FiniteDimensional ℂ M := hM
  have hsplit := ContinuousLinearMap.charbonnierCost_unitary_displacement_eq_block_add_tail
    tau hτ Z U U V (fun x => (hV x).symm) (fun _ _ => rfl)
  have hVle : (1 - (V : Z →L[ℂ] Z)).charbonnierCost tau ≤
        (1 - (U : E →L[ℂ] E)).charbonnierCost tau := by
    rw [hsplit]
    exact le_self_add
  obtain ⟨W, hW, hWmap, hWmin⟩ := exists_charbonnier_minimizing_finite_restriction
    tau hτ K₀ L₀ M V hlocal' (ne_top_of_le_ne_top hfinite hVle)
      hlocalmin' hMK hMV.mem_invtSubmodule
  refine ⟨V, hV, hself, hlocal', hlocalmin', M, hM, hMK, hMV, hfix, W, hW, hWmap, ?_⟩
  intro T hT
  have hcost (X : M ≃ₗᵢ[ℂ] M) : (1 - (X : M →L[ℂ] M)).charbonnierCost tau =
      ENNReal.ofReal (smoothedDisplacementCost (E := M) tau X.toLinearMap) := by
    rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ.le]
    rfl
  have hnonneg : 0 ≤ smoothedDisplacementCost (E := M) tau T.toLinearMap := by
    unfold smoothedDisplacementCost
    apply Finset.sum_nonneg
    intro i _
    exact sub_nonneg.mpr (Real.le_sqrt_of_sq_le
      (by nlinarith [sq_nonneg ((LinearMap.id - T.toLinearMap).singularValues i)]))
  have h := hWmin T hT
  rw [hcost, hcost] at h
  exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp h

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
