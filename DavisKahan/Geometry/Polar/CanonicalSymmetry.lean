/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.Geometry.Polar.NonacuteCompression
public import DavisKahan.Geometry.Angle.CosineKernel

/-!
# A self-adjoint transporter with any prescribed crossed-defect pairing

Canonical rotation followed on the source by its reflection is a
self-adjoint unitary transporter. On crossed defects it acts by the chosen
identification and its adjoint, with no minus sign. This supplies arbitrary
reflecting kernel data for optimal transport assembly. No optimality claim
is made for its positive-angle action.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Every isometric identification of the actual crossed defects extends
to a self-adjoint unitary transporter preserving the principal cosine.
The reverse action is exactly its inverse identification. -/
theorem exists_selfAdjoint_transport_prescribing_defects
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    ∃ V : E ≃ₗᵢ[𝕜] E, K.map V.toLinearMap = L ∧
      IsSelfAdjoint (V : E →L[𝕜] E) ∧
      Commute (V : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L) ∧
      (∀ x : halmosSourceDefect K L, V x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, V y = (D.symm y : E)) := by
  let Rop := nonacuteDirectRotation K L D
  let R := Unitary.linearIsometryEquiv
    (⟨Rop, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[𝕜] E))
  let V := K.reflection.trans R
  have hVop : (V : E →L[𝕜] E) = Rop * (K.reflection : E →L[𝕜] E) := rfl
  have hJ : star (K.reflection : E →L[𝕜] E) = (K.reflection : E →L[𝕜] E) := by
    change ContinuousLinearMap.adjoint (K.reflection : E →L[𝕜] E) = _
    rw [K.reflection.adjoint_eq_symm, Submodule.reflection_symm]
  have hself : IsSelfAdjoint (V : E →L[𝕜] E) := by
    change star (V : E →L[𝕜] E) = (V : E →L[𝕜] E)
    rw [hVop, star_mul, hJ]
    ext x
    exact (nonacuteDirectRotation_reflection_eq_reflection_star K L D x).symm
  have hmap : K.map V.toLinearMap = L := by
    apply (K.map_eq_iff_intertwines_reflection L V).mpr
    intro x
    change Rop (K.reflection (K.reflection x)) = L.reflection (Rop (K.reflection x))
    exact nonacuteDirectRotation_reflection_intertwines K L D (K.reflection x)
  have hJC : Commute (K.reflection : E →L[𝕜] E)
      (Proposition35.section3CosAngleOperator K L) := by
    ext x
    change K.reflection (Proposition35.section3CosAngleOperator K L x) =
      Proposition35.section3CosAngleOperator K L (K.reflection x)
    rw [Submodule.reflection_apply, Submodule.reflection_apply, map_sub, map_nsmul]
    have h := DFunLike.congr_fun
      (Proposition35.section3CosAngleOperator_comm_projection K L).eq x
    change Proposition35.section3CosAngleOperator K L (K.starProjection x) =
      K.starProjection (Proposition35.section3CosAngleOperator K L x) at h
    rw [h]
  have hVC : Commute (V : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L) := by
    rw [hVop]
    exact (Proposition35.nonacuteDirectRotation_comm_cosine K L D).mul_left hJC
  have hsource (x : halmosSourceDefect K L) : Rop (x : E) = (D x : E) := by
    change (spectraCanonicalPolarFactor K L + crossedDefectQuarterTurn K L D) (x : E) = _
    rw [add_apply, canonicalPolarFactor_apply_crossedDefect_eq_zero K L
      (show (x : E) ∈ crossedDefectSum K L from Submodule.mem_sup_left x.property),
      crossedDefectQuarterTurn_apply_source, zero_add]
  have htarget (y : halmosTargetDefect K L) : Rop (y : E) = -(D.symm y : E) := by
    change (spectraCanonicalPolarFactor K L + crossedDefectQuarterTurn K L D) (y : E) = _
    rw [add_apply, canonicalPolarFactor_apply_crossedDefect_eq_zero K L
      (show (y : E) ∈ crossedDefectSum K L from Submodule.mem_sup_right y.property),
      crossedDefectQuarterTurn_apply_target, zero_add]
  refine ⟨V, hmap, hself, hVC, ?_, ?_⟩
  · intro x
    change Rop (K.reflection (x : E)) = (D x : E)
    rw [Submodule.reflection_mem_subspace_eq_self (mem_halmosSourceDefect.mp x.property).1]
    exact hsource x
  · intro y
    change Rop (K.reflection (y : E)) = (D.symm y : E)
    rw [Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
      (mem_halmosTargetDefect.mp y.property).1, map_neg, htarget, neg_neg]

end TauCeti.DavisKahan
