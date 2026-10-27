/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierGradientKernel
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerAngles
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReflectionTransport

/-!
# Every Hilbert-space Charbonnier optimizer preserves principal sines

Classify the actual finite positive-gradient cutoffs and use reflection
commutation on the entire gradient kernel. Compact spectral completeness
then proves the ambient commutation identity. No prescribed spectral
block form or canonical-tail assumption is needed.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Every finite-cost local complex Charbonnier optimizer commutes with
the intrinsic sine-angle operator in arbitrary Hilbert dimension.
In particular unequal angle sectors cannot mix. -/
theorem commute_sinAngleOperator_of_charbonnier_isLocalMinOn_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
      {T | K.map T.toLinearMap = L} U) :
    Commute (U : E →L[ℂ] E) (K.sinAngleOperator L) := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  let A := G.modulus
  let S := K.sinAngleOperator L
  have hSp := (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hfinite
  have hGc : IsCompactOperator G := isCompactOperator_smoothedUnitaryGradient tau hτ U
    (by
      rw [← neg_sub 1 (U : E →L[ℂ] E)]
      exact (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
        2 (by norm_num) (1 - (U : E →L[ℂ] E)) hSp).neg)
  have hAc : IsCompactOperator A := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hseq : A.singularValue = G.singularValue :=
      funext (fun n => ContinuousLinearMap.singularValue_modulus G n)
    rw [hseq]
    exact hGc.tendsto_singularValue
  have hlocal_commutes (M : Submodule ℂ E) [M.HasOrthogonalProjection] [CompleteSpace M]
      [(K.comap M.subtype).HasOrthogonalProjection]
      [(L.comap M.subtype).HasOrthogonalProjection]
      (hK : M.IsReducing K.starProjection.toLinearMap)
      (hL : M.IsReducing L.starProjection.toLinearMap)
      (V : M ≃ₗᵢ[ℂ] M) (hV : ∀ x : M, (V x : E) = U x)
      (hVS : Commute (V : M →L[ℂ] M)
        ((K.comap M.subtype).sinAngleOperator (L.comap M.subtype))) :
      ∀ x ∈ M, U (S x) = S (U x) := by
    intro x hx
    let x₀ : M := ⟨x, hx⟩
    let S₀ := (K.comap M.subtype).sinAngleOperator (L.comap M.subtype)
    have hS₀ (y : M) : (S₀ y : E) = S (y : E) :=
      K.sinAngleOperator_comap_subtype_apply_of_invariant L M
        hK.mem_invtSubmodule hL.mem_invtSubmodule y
    calc
      _ = U (S₀ x₀ : E) := congrArg U (hS₀ x₀).symm
      _ = (V (S₀ x₀) : E) := (hV _).symm
      _ = (S₀ (V x₀) : E) :=
        congrArg Subtype.val (congrArg (fun B : M →L[ℂ] M => B x₀) hVS.eq)
      _ = S (V x₀ : E) := hS₀ _
      _ = _ := congrArg S (hV x₀)
  rw [commute_iff_eq]
  apply eq_of_eq_on_ker_and_positive_eigenSpans hAc G.isSelfAdjoint_modulus
    G.isPositive_modulus.re_inner_nonneg_left
  · rw [show A.ker = G.ker from G.ker_modulus]
    let Z := G.ker
    let := K.hasOrthogonalProjection_comap_subtype_of_complete Z
    let := L.hasOrthogonalProjection_comap_subtype_of_complete Z
    obtain ⟨V, hV, _, hself⟩ :=
      exists_selfAdjoint_unitary_restriction_smoothed_gradient_kernel tau hτ U
    have hK : Z.IsReducing K.starProjection.toLinearMap :=
      K.isReducing_ker_of_reflection_conjugate_eq_neg G
        (isSelfAdjoint_smoothedUnitaryGradient _ _)
        (gradient_reflection_conjugate_eq_neg_of_charbonnier_isLocalMinOn_complex tau hτ K L U hmap hfinite hmin)
    have hL : Z.IsReducing L.starProjection.toLinearMap := by
      apply (L.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule Z).mpr
      intro x hx
      change L.starProjection x ∈ Z
      have h := K.starProjection_map_mem_of_isometry_restriction Z U V hV
        hK.mem_invtSubmodule x hx
      simpa only [hmap] using h
    have hlocal := K.map_comap_subtype_of_isometry_restriction L Z U V hmap hV
    have hconj : (V : Z →L[ℂ] Z) * (K.comap Z.subtype).starProjection *
        star (V : Z →L[ℂ] Z) = (L.comap Z.subtype).starProjection := by
      rw [show star (V : Z →L[ℂ] Z) = (V.symm : Z →L[ℂ] Z) from V.adjoint_eq_symm]
      apply ContinuousLinearMap.ext
      intro x
      change V ((K.comap Z.subtype).starProjection (V.symm x)) =
        (L.comap Z.subtype).starProjection x
      have h := Submodule.starProjection_map_apply V (K.comap Z.subtype) x
      change ((K.comap Z.subtype).map V.toLinearMap).starProjection x = _ at h
      simpa only [hlocal] using h.symm
    have hVS := (K.comap Z.subtype).commute_sinAngleOperator_of_selfAdjoint_transport
      (L.comap Z.subtype) V hself hconj
    exact hlocal_commutes Z hK hL V hV hVS
  · intro ε hε
    obtain ⟨hM, hK, hL, _, _, V, hV, _, hlocal, hVmin⟩ :=
      exists_charbonnier_minimizing_restriction_on_gradient_cutoff_of_isLocalMinOn_complex tau hτ K L U hmap
        hfinite hmin ε hε
    let M := eigenSpan A (Set.Ioi ε)
    let : FiniteDimensional ℂ M := hM
    have hdim : Module.finrank ℂ (K.comap M.subtype) =
        Module.finrank ℂ (L.comap M.subtype) := by
      have h := V.toLinearEquiv.finrank_map_eq (K.comap M.subtype)
      rw [hlocal] at h
      exact h.symm
    have hVS := commute_sinAngleOperator_of_smoothed_minimal tau hτ
      (K.comap M.subtype) (L.comap M.subtype) hdim V hlocal hVmin
    exact hlocal_commutes M hK hL V hV hVS

/-- Global optimality implies angle preservation as a special case of
local rigidity. -/
theorem commute_sinAngleOperator_of_charbonnier_minimal
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau) :
    Commute (U : E →L[ℂ] E) (K.sinAngleOperator L) := by
  exact commute_sinAngleOperator_of_charbonnier_isLocalMinOn_complex tau hτ K L U hmap hfinite
    (show IsMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
      {T | K.map T.toLinearMap = L} U from fun T hT => hmin T hT).isLocalMinOn

/-- Every finite-cost global complex Charbonnier optimizer fixes each
common-source and common-orthogonal direction, in arbitrary dimension. -/
theorem apply_eq_self_of_projections_eq_of_charbonnier_minimal
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
    (x : E) (hx : K.starProjection x = L.starProjection x) : U x = x :=
  apply_eq_self_of_projections_eq_of_charbonnier_minimal_of_commute tau hτ K L U hmap
    hfinite hmin (commute_sinAngleOperator_of_charbonnier_minimal tau hτ K L U hmap hfinite hmin)
    x hx

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
