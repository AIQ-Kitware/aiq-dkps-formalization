/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport
public import ForTauCeti.Analysis.OperatorIdeal.Family.UnitaryTransport

/-!
# Unitary correction fibers and exact ideal costs

Correcting a unitary to preserve a subspace is exactly a transport
problem from its image back to that subspace. The correspondence
preserves every accepted ideal gauge. The projection-image difference
has the same ideal gauge as the actual commutator.
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A unitary preserves a closed subspace exactly when it commutes
with its orthogonal projection, in arbitrary Hilbert dimension. -/
theorem map_eq_self_iff_commute_starProjection
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (V : E ≃ₗᵢ[𝕜] E) :
    K.map V.toLinearMap = K ↔ Commute (V : E →L[𝕜] E) K.starProjection := by
  constructor
  · intro hmap
    ext x
    change V (K.starProjection x) = K.starProjection (V x)
    have h := starProjection_map_apply V K (V x)
    simpa only [hmap, V.symm_apply_apply] using h.symm
  · intro hcomm
    apply (K.map_eq_iff_conjugate_starProjection K V).mpr
    rw [show star (V : E →L[𝕜] E) = (V.symm : E →L[𝕜] E) from V.adjoint_eq_symm]
    ext x
    have h := congrArg (fun B : E →L[𝕜] E => B (V.symm x)) hcomm.eq
    change V (K.starProjection (V.symm x)) = K.starProjection (V (V.symm x)) at h
    change V (K.starProjection (V.symm x)) = K.starProjection x
    simpa only [V.apply_symm_apply] using h

omit [CompleteSpace E] in
/-- The correction-to-transport correspondence on actual subspace maps. -/
theorem map_correction_transport (K : Submodule 𝕜 E) (A V : E ≃ₗᵢ[𝕜] E) :
    (K.map A.toLinearMap).map (A.symm.trans V).toLinearMap = K.map V.toLinearMap := by
  rw [← map_comp]
  congr 1
  ext x
  exact congrArg V (A.symm_apply_apply x)

omit [CompleteSpace E] in
/-- The projection-image difference factors the actual commutator
through the given unitary. -/
theorem projection_image_sub_comp_unitary_eq_commutator
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[𝕜] E) :
    ((K.map A.toLinearMap).starProjection - K.starProjection) ∘L (A : E →L[𝕜] E) =
      (A : E →L[𝕜] E) * K.starProjection - K.starProjection * (A : E →L[𝕜] E) := by
  ext x
  change (K.map A.toLinearMap).starProjection (A x) - K.starProjection (A x) =
    A (K.starProjection x) - K.starProjection (A x)
  rw [starProjection_map_apply, A.symm_apply_apply]

omit [CompleteSpace E] in
/-- The commutator norm is exactly the image projection gap. -/
theorem norm_projection_image_sub_eq_commutator
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[𝕜] E) :
    ‖(K.map A.toLinearMap).starProjection - K.starProjection‖ =
      ‖(A : E →L[𝕜] E) * K.starProjection - K.starProjection * (A : E →L[𝕜] E)‖ := by
  rw [← K.projection_image_sub_comp_unitary_eq_commutator A,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

end Submodule

namespace TauCeti.OperatorIdealFamily

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Literal correction distance equals relative-unitary displacement
in every accepted ideal gauge, including infinite values. -/
theorem gauge_unitary_sub_eq_displacement (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (A V : E ≃ₗᵢ[𝕜] E) :
    Φ.gauge ((A : E →L[𝕜] E) - (V : E →L[𝕜] E)) =
      Φ.gauge (1 - (A.symm.trans V : E →L[𝕜] E)) := by
  have hfactor : (A : E →L[𝕜] E) - (V : E →L[𝕜] E) =
      (1 - (A.symm.trans V : E →L[𝕜] E)) ∘L (A : E →L[𝕜] E) := by
    ext x
    change A x - V x = A x - V (A.symm (A x))
    rw [A.symm_apply_apply]
  rw [hfactor, Φ.gauge_comp_linearIsometryEquiv_right]


/-- Correction minimality and relative-transport minimality are exactly
equivalent in every operator-ideal gauge, including infinite costs.
The candidate need not be assumed feasible for this comparison identity. -/
theorem gauge_correction_isMin_iff_transport_isMin
    (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[𝕜] E) :
    (∀ V : E ≃ₗᵢ[𝕜] E, Commute (V : E →L[𝕜] E) K.starProjection →
      Φ.gauge ((A : E →L[𝕜] E) - (C : E →L[𝕜] E)) ≤
        Φ.gauge ((A : E →L[𝕜] E) - (V : E →L[𝕜] E))) ↔
    (∀ T : E ≃ₗᵢ[𝕜] E, (K.map A.toLinearMap).map T.toLinearMap = K →
      Φ.gauge (1 - (A.symm.trans C : E →L[𝕜] E)) ≤
        Φ.gauge (1 - (T : E →L[𝕜] E))) := by
  constructor
  · intro hmin T hT
    let V := A.trans T
    have hrel : A.symm.trans V = T := by ext x; simp [V]
    have hV : Commute (V : E →L[𝕜] E) K.starProjection := by
      apply (K.map_eq_self_iff_commute_starProjection V).mp
      rw [← K.map_correction_transport A V, hrel]
      exact hT
    have h := hmin V hV
    rwa [Φ.gauge_unitary_sub_eq_displacement A C,
      Φ.gauge_unitary_sub_eq_displacement A V, hrel] at h
  · intro hmin V hV
    rw [Φ.gauge_unitary_sub_eq_displacement A C,
      Φ.gauge_unitary_sub_eq_displacement A V]
    apply hmin
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection V).mpr hV

/-- The actual unitary commutator and the image projection difference
have exactly the same ideal gauge. This is an equality, not a bound. -/
theorem gauge_projection_image_sub_eq_commutator (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[𝕜] E) :
    Φ.gauge ((K.map A.toLinearMap).starProjection - K.starProjection) =
      Φ.gauge ((A : E →L[𝕜] E) * K.starProjection -
        K.starProjection * (A : E →L[𝕜] E)) := by
  rw [← K.projection_image_sub_comp_unitary_eq_commutator A,
    Φ.gauge_comp_linearIsometryEquiv_right]

/-- The commutator gives a certified lower bound for the distance to
every unitary commuting with the prescribed projection. -/
theorem gauge_commutator_le_unitary_correction (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[𝕜] E)
    (hC : Commute (C : E →L[𝕜] E) K.starProjection) :
    Φ.gauge ((A : E →L[𝕜] E) * K.starProjection -
      K.starProjection * (A : E →L[𝕜] E)) ≤
        Φ.gauge ((A : E →L[𝕜] E) - (C : E →L[𝕜] E)) := by
  rw [← Φ.gauge_projection_image_sub_eq_commutator K A,
    Φ.gauge_unitary_sub_eq_displacement A C]
  apply Φ.gauge_projection_sub_le_unitary_displacement
  rw [K.map_correction_transport]
  exact (K.map_eq_self_iff_commute_starProjection C).mpr hC

end TauCeti.OperatorIdealFamily
