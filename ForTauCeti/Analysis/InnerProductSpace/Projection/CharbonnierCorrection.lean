/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryCorrection
public import ForTauCeti.Analysis.OperatorIdeal.Charbonnier
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry

/-!
# Native Charbonnier correction and transport

The relative-unitary correspondence preserves the literal extended
smoothed spectral cost and all ambient competitors. No ideal-norm
structure is imposed on this nonhomogeneous trace penalty.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Unitary changes of domain and codomain preserve the native smoothed
trace, including infinite values and arbitrary smoothing parameter. -/
theorem charbonnierCost_comp_linearIsometryEquiv
    {F E' F' : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']
    (tau : ℝ) (T : E →L[𝕜] F) (A : E' ≃ₗᵢ[𝕜] E) (B : F ≃ₗᵢ[𝕜] F') :
    ((B : F →L[𝕜] F') ∘L T ∘L (A : E' →L[𝕜] E)).charbonnierCost tau =
      T.charbonnierCost tau := by
  have hseq : ((B : F →L[𝕜] F') ∘L T ∘L (A : E' →L[𝕜] E)).singularValue =
      T.singularValue := by
    funext n
    exact singularValue_comp_linearIsometryEquiv T A B n
  simp only [charbonnierCost, hseq]

/-- Correction distance equals relative-unitary displacement as a native
extended smoothed trace. No finite-cost hypothesis is required. -/
theorem charbonnierCost_unitary_sub_eq_displacement (tau : ℝ) (A C : E ≃ₗᵢ[𝕜] E) :
    ((A : E →L[𝕜] E) - (C : E →L[𝕜] E)).charbonnierCost tau =
      (1 - (A.symm.trans C : E →L[𝕜] E)).charbonnierCost tau := by
  have hfactor : (A : E →L[𝕜] E) - (C : E →L[𝕜] E) =
      (1 : E →L[𝕜] E) ∘L (1 - (A.symm.trans C : E →L[𝕜] E)) ∘L
        (A : E →L[𝕜] E) := by
    ext x
    change A x - C x = A x - C (A.symm (A x))
    rw [A.symm_apply_apply]
  rw [hfactor]
  exact charbonnierCost_comp_linearIsometryEquiv tau _ A (LinearIsometryEquiv.refl 𝕜 E)

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Full native Charbonnier correction optimality is equivalent to
relative transport optimality, with unrestricted ambient competitors. -/
theorem charbonnier_correction_isMin_iff_transport_isMin
    (tau : ℝ) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[𝕜] E) :
    (∀ V : E ≃ₗᵢ[𝕜] E, Commute (V : E →L[𝕜] E) K.starProjection →
      ((A : E →L[𝕜] E) - (C : E →L[𝕜] E)).charbonnierCost tau ≤
        ((A : E →L[𝕜] E) - (V : E →L[𝕜] E)).charbonnierCost tau) ↔
    (∀ T : E ≃ₗᵢ[𝕜] E, (K.map A.toLinearMap).map T.toLinearMap = K →
      (1 - (A.symm.trans C : E →L[𝕜] E)).charbonnierCost tau ≤
        (1 - (T : E →L[𝕜] E)).charbonnierCost tau) := by
  constructor
  · intro hmin T hT
    let V := A.trans T
    have hrel : A.symm.trans V = T := by ext x; simp [V]
    have hV : Commute (V : E →L[𝕜] E) K.starProjection := by
      apply (K.map_eq_self_iff_commute_starProjection V).mp
      rw [← K.map_correction_transport A V, hrel]
      exact hT
    have h := hmin V hV
    rwa [ContinuousLinearMap.charbonnierCost_unitary_sub_eq_displacement tau A C,
      ContinuousLinearMap.charbonnierCost_unitary_sub_eq_displacement tau A V, hrel] at h
  · intro hmin V hV
    rw [ContinuousLinearMap.charbonnierCost_unitary_sub_eq_displacement tau A C,
      ContinuousLinearMap.charbonnierCost_unitary_sub_eq_displacement tau A V]
    apply hmin
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection V).mpr hV

/-- Uniqueness of nearest commuting correction is equivalent to uniqueness
of relative transport, including the extended infinite-cost regime. -/
theorem existsUnique_charbonnier_correction_iff_transport
    (tau : ℝ) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[𝕜] E) :
    (∃! C : E ≃ₗᵢ[𝕜] E, Commute (C : E →L[𝕜] E) K.starProjection ∧
      ∀ V : E ≃ₗᵢ[𝕜] E, Commute (V : E →L[𝕜] E) K.starProjection →
        ((A : E →L[𝕜] E) - (C : E →L[𝕜] E)).charbonnierCost tau ≤
          ((A : E →L[𝕜] E) - (V : E →L[𝕜] E)).charbonnierCost tau) ↔
    (∃! T : E ≃ₗᵢ[𝕜] E, (K.map A.toLinearMap).map T.toLinearMap = K ∧
      ∀ V : E ≃ₗᵢ[𝕜] E, (K.map A.toLinearMap).map V.toLinearMap = K →
        (1 - (T : E →L[𝕜] E)).charbonnierCost tau ≤
          (1 - (V : E →L[𝕜] E)).charbonnierCost tau) := by
  let e : (E ≃ₗᵢ[𝕜] E) ≃ (E ≃ₗᵢ[𝕜] E) :=
    { toFun := fun C => A.symm.trans C
      invFun := fun T => A.trans T
      left_inv := by
        intro C
        ext x
        change C (A.symm (A x)) = C x
        rw [A.symm_apply_apply]
      right_inv := by
        intro T
        ext x
        change T (A (A.symm x)) = T x
        rw [A.apply_symm_apply] }
  apply e.existsUnique_congr
  intro C
  change (Commute (C : E →L[𝕜] E) K.starProjection ∧ _) ↔
    ((K.map A.toLinearMap).map (A.symm.trans C).toLinearMap = K ∧ _)
  rw [charbonnier_correction_isMin_iff_transport_isMin tau K A C,
    K.map_correction_transport A C, K.map_eq_self_iff_commute_starProjection C]
  rfl

end TauCeti
