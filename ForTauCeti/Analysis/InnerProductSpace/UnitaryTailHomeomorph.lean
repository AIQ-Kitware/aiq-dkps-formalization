/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitaryTailAgreement
public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction
public import ForTauCeti.Analysis.OperatorIdeal.OrthogonalExtension
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Topology

/-!
# Operator-norm coordinates for unitaries with a fixed reducing tail

Restriction and extension identify all unitary actions on a reducing
subspace with all ambient unitaries having a prescribed complementary
action. The correspondence is a homeomorphism and preserves the operator
norm of differences exactly. Both sectors may be infinite-dimensional.
-/

public section

noncomputable section

open scoped TauCeti.LinearIsometryEquivOperatorNorm

namespace LinearIsometryEquiv

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- All ambient unitaries with a fixed reducing reference tail are
homeomorphic in operator norm to the unitaries on the retained sector.
The exact difference norm is preserved, without a dimension assumption. -/
theorem exists_reference_tail_homeomorph
    (M : Submodule 𝕜 E) [M.HasOrthogonalProjection]
    (R : E ≃ₗᵢ[𝕜] E) (hR : M.IsReducing R.toLinearMap) :
    ∃ e : (M ≃ₗᵢ[𝕜] M) ≃ₜ {U : E ≃ₗᵢ[𝕜] E | ∀ x ∈ Mᗮ, U x = R x},
      (∀ V (x : M), (e V).val x = (V x : E)) ∧
      ∀ V W, ‖((e V).val : E →L[𝕜] E) - ((e W).val : E →L[𝕜] E)‖ =
        ‖(V : M →L[𝕜] M) - (W : M →L[𝕜] M)‖ := by
  obtain ⟨RN, hRN, _⟩ := R.exists_restriction_of_reducing Mᗮ
    ((Submodule.isReducing_orthogonal_iff M _).mpr hR)
  have hex (V : M ≃ₗᵢ[𝕜] M) : ∃ U : E ≃ₗᵢ[𝕜] E,
      (∀ x : M, U x = (V x : E)) ∧ (∀ x ∈ Mᗮ, U x = R x) := by
    obtain ⟨U, hUM, hUN⟩ := M.exists_unitary_orthogonal_sum V RN
    exact ⟨U, hUM, fun x hx => (hUN ⟨x, hx⟩).trans (hRN ⟨x, hx⟩)⟩
  choose f hfM hfN using hex
  let X := {U : E ≃ₗᵢ[𝕜] E | ∀ x ∈ Mᗮ, U x = R x}
  have hrestr (U : X) : ∃ V : M ≃ₗᵢ[𝕜] M, ∀ x : M, (V x : E) = U.val x := by
    obtain ⟨V, hV, _⟩ := U.val.exists_restriction_of_reducing M
      (U.val.isReducing_of_eq_on_orthogonal R M hR U.property)
    exact ⟨V, hV⟩
  choose g hg using hrestr
  have hformula (V : M ≃ₗᵢ[𝕜] M) : (f V : E →L[𝕜] E) =
      M.subtypeL ∘L (V : M →L[𝕜] M) ∘L M.orthogonalProjectionOnto +
        (R : E →L[𝕜] E) ∘L Mᗮ.starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    change f V x = (V (M.orthogonalProjectionOnto x) : E) + R (Mᗮ.starProjection x)
    calc
      _ = f V (M.starProjection x + Mᗮ.starProjection x) := by
        rw [M.starProjection_add_starProjection_orthogonal]
      _ = _ := by
        rw [map_add, hfM V ⟨_, M.starProjection_apply_mem x⟩,
          hfN V _ (Mᗮ.starProjection_apply_mem x)]
        rfl
  let e : (M ≃ₗᵢ[𝕜] M) ≃ X :=
    { toFun := fun V => ⟨f V, hfN V⟩
      invFun := g
      left_inv := by
        intro V
        ext x
        exact (hg ⟨f V, hfN V⟩ x).trans (hfM V x)
      right_inv := by
        intro U
        apply Subtype.ext
        ext x
        change f (g U) x = U.val x
        rw [show f (g U) x =
          (g U (M.orthogonalProjectionOnto x) : E) + R (Mᗮ.starProjection x) from
            congrArg (fun A : E →L[𝕜] E => A x) (hformula (g U))]
        rw [hg U, ← U.property _ (Mᗮ.starProjection_apply_mem x), ← map_add]
        change U.val (M.starProjection x + Mᗮ.starProjection x) = U.val x
        rw [M.starProjection_add_starProjection_orthogonal] }
  have hec : Continuous e := by
    apply Continuous.subtype_mk
    apply continuous_operatorNorm_iff.mpr
    have hc : Continuous (fun V : M ≃ₗᵢ[𝕜] M =>
        M.subtypeL ∘L (V : M →L[𝕜] M) ∘L M.orthogonalProjectionOnto +
          (R : E →L[𝕜] E) ∘L Mᗮ.starProjection) :=
      (continuous_const.clm_comp
        (isEmbedding_toContinuousLinearMap.continuous.clm_comp continuous_const)).add
          continuous_const
    exact hc.congr (fun V => (hformula V).symm)
  have heic : Continuous e.symm := by
    apply continuous_operatorNorm_iff.mpr
    have hc : Continuous (fun U : X => M.orthogonalProjectionOnto ∘L
        (U.val : E →L[𝕜] E) ∘L M.subtypeL) :=
      continuous_const.clm_comp
        ((isEmbedding_toContinuousLinearMap.continuous.comp continuous_subtype_val).clm_comp
          continuous_const)
    apply hc.congr
    intro U
    apply ContinuousLinearMap.ext
    intro x
    change M.orthogonalProjectionOnto (U.val x) = g U x
    rw [← hg U, M.orthogonalProjectionOnto_mem_subspace_eq_self]
  refine ⟨⟨e, hec, heic⟩, hfM, ?_⟩
  intro V W
  have hdiff : (f V : E →L[𝕜] E) - (f W : E →L[𝕜] E) =
      M.subtypeL ∘L ((V : M →L[𝕜] M) - (W : M →L[𝕜] M)) ∘L
        M.orthogonalProjectionOnto := by
    apply (ContinuousLinearMap.eq_orthogonal_extension_iff M M _ _).mpr
    constructor
    · intro x
      change f V x - f W x = (V x : E) - (W x : E)
      rw [hfM, hfM]
    · intro x hx
      change f V x - f W x = 0
      rw [hfN V x hx, hfN W x hx, sub_self]
  change ‖(f V : E →L[𝕜] E) - (f W : E →L[𝕜] E)‖ = _
  rw [hdiff, ContinuousLinearMap.norm_orthogonal_extension]

end LinearIsometryEquiv
