/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport
public import ForTauCeti.Analysis.OperatorIdeal.Family.UnitaryTransport
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Topology
public import Mathlib.Topology.Order.LocalExtr

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

open Filter
open scoped ENNReal Topology TauCeti.LinearIsometryEquivOperatorNorm

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

/-- Local correction and relative-transport optimality are equivalent
in operator norm. The actual feasible candidate and all ambient nearby
competitors are retained; the ideal gauge may be infinite. -/
theorem gauge_correction_isLocalMinOn_iff_transport_isLocalMinOn
    (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (A C : E ≃ₗᵢ[𝕜] E) (hC : Commute (C : E →L[𝕜] E) K.starProjection) :
    IsLocalMinOn
      (fun V : E ≃ₗᵢ[𝕜] E =>
        Φ.gauge ((A : E →L[𝕜] E) - (V : E →L[𝕜] E)))
      {V | Commute (V : E →L[𝕜] E) K.starProjection} C ↔
    IsLocalMinOn
      (fun T : E ≃ₗᵢ[𝕜] E => Φ.gauge (1 - (T : E →L[𝕜] E)))
      {T | (K.map A.toLinearMap).map T.toLinearMap = K} (A.symm.trans C) := by
  let f (T : E ≃ₗᵢ[𝕜] E) := A.trans T
  let g (V : E ≃ₗᵢ[𝕜] E) := A.symm.trans V
  have hfg (V : E ≃ₗᵢ[𝕜] E) : f (g V) = V := by
    ext x
    change V (A.symm (A x)) = V x
    rw [A.symm_apply_apply]
  have hgf (T : E ≃ₗᵢ[𝕜] E) : g (f T) = T := by
    ext x
    change T (A (A.symm x)) = T x
    rw [A.apply_symm_apply]
  have hf : Continuous f := by
    apply LinearIsometryEquiv.continuous_operatorNorm_iff.mpr
    change Continuous (fun T : E ≃ₗᵢ[𝕜] E => (T : E →L[𝕜] E) ∘L (A : E →L[𝕜] E))
    exact LinearIsometryEquiv.isEmbedding_toContinuousLinearMap.continuous.clm_comp continuous_const
  have hg : Continuous g := by
    apply LinearIsometryEquiv.continuous_operatorNorm_iff.mpr
    change Continuous (fun V : E ≃ₗᵢ[𝕜] E =>
      (V : E →L[𝕜] E) ∘L (A.symm : E →L[𝕜] E))
    exact LinearIsometryEquiv.isEmbedding_toContinuousLinearMap.continuous.clm_comp continuous_const
  have hgmap (V : E ≃ₗᵢ[𝕜] E) (hV : Commute (V : E →L[𝕜] E) K.starProjection) :
      (K.map A.toLinearMap).map (g V).toLinearMap = K := by
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection V).mpr hV
  have hfmap (T : E ≃ₗᵢ[𝕜] E)
      (hT : (K.map A.toLinearMap).map T.toLinearMap = K) :
      Commute (f T : E →L[𝕜] E) K.starProjection := by
    apply (K.map_eq_self_iff_commute_starProjection (f T)).mp
    rw [← K.map_correction_transport A (f T)]
    change (K.map A.toLinearMap).map (g (f T)).toLinearMap = K
    rwa [hgf]
  have hcostf (T : E ≃ₗᵢ[𝕜] E) :
      Φ.gauge ((A : E →L[𝕜] E) - (f T : E →L[𝕜] E)) =
        Φ.gauge (1 - (T : E →L[𝕜] E)) := by
    rw [Φ.gauge_unitary_sub_eq_displacement]
    change Φ.gauge (1 - (g (f T) : E →L[𝕜] E)) = _
    rw [hgf]
  constructor
  · intro hmin
    have hloc : IsLocalMinOn
        (fun V : E ≃ₗᵢ[𝕜] E =>
          Φ.gauge ((A : E →L[𝕜] E) - (V : E →L[𝕜] E)))
        {V | Commute (V : E →L[𝕜] E) K.starProjection} (f (g C)) := by rwa [hfg]
    have hcomp := hloc.comp_continuousOn
      (s := {T : E ≃ₗᵢ[𝕜] E | (K.map A.toLinearMap).map T.toLinearMap = K})
      (fun T hT => hfmap T hT) hf.continuousOn (hgmap C hC)
    filter_upwards [hcomp] with T hT
    change Φ.gauge ((A : E →L[𝕜] E) - (f (g C) : E →L[𝕜] E)) ≤
      Φ.gauge ((A : E →L[𝕜] E) - (f T : E →L[𝕜] E)) at hT
    rw [hcostf, hcostf] at hT
    exact hT
  · intro hmin
    have hcomp := hmin.comp_continuousOn
      (s := {V : E ≃ₗᵢ[𝕜] E | Commute (V : E →L[𝕜] E) K.starProjection})
      (fun V hV => hgmap V hV) hg.continuousOn hC
    filter_upwards [hcomp] with V hV
    change Φ.gauge (1 - (g C : E →L[𝕜] E)) ≤
      Φ.gauge (1 - (g V : E →L[𝕜] E)) at hV
    rw [← Φ.gauge_unitary_sub_eq_displacement A C,
      ← Φ.gauge_unitary_sub_eq_displacement A V] at hV
    exact hV

/-- Uniqueness of nearest commuting correction is equivalent to
uniqueness of relative transport in every operator-ideal gauge. This
also compares competitors at infinite distance. -/
theorem existsUnique_correction_iff_transport
    (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[𝕜] E) :
    (∃! C : E ≃ₗᵢ[𝕜] E, Commute (C : E →L[𝕜] E) K.starProjection ∧
      ∀ V : E ≃ₗᵢ[𝕜] E, Commute (V : E →L[𝕜] E) K.starProjection →
        Φ.gauge ((A : E →L[𝕜] E) - (C : E →L[𝕜] E)) ≤
          Φ.gauge ((A : E →L[𝕜] E) - (V : E →L[𝕜] E))) ↔
    (∃! T : E ≃ₗᵢ[𝕜] E, (K.map A.toLinearMap).map T.toLinearMap = K ∧
      ∀ V : E ≃ₗᵢ[𝕜] E, (K.map A.toLinearMap).map V.toLinearMap = K →
        Φ.gauge (1 - (T : E →L[𝕜] E)) ≤ Φ.gauge (1 - (V : E →L[𝕜] E))) := by
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
    ((K.map A.toLinearMap).map (A.symm.trans C).toLinearMap = K ∧
      ∀ V : E ≃ₗᵢ[𝕜] E, (K.map A.toLinearMap).map V.toLinearMap = K →
        Φ.gauge (1 - (A.symm.trans C : E →L[𝕜] E)) ≤ Φ.gauge (1 - (V : E →L[𝕜] E)))
  rw [Φ.gauge_correction_isMin_iff_transport_isMin K A C,
    K.map_correction_transport A C, K.map_eq_self_iff_commute_starProjection C]

/-- A unique nearest commuting correction has finite ideal distance.
If its distance were infinite, identity and negative identity would both
minimize; their equality forces the space to be zero, where the cost is zero.
This argument applies to every accepted ideal gauge in either field. -/
theorem gauge_unitary_sub_ne_top_of_unique_correction
    (Φ : OperatorIdealFamily.{u, v, v} 𝕜)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[𝕜] E)
    (hC : Commute (C : E →L[𝕜] E) K.starProjection ∧
      ∀ V : E ≃ₗᵢ[𝕜] E, Commute (V : E →L[𝕜] E) K.starProjection →
        Φ.gauge ((A : E →L[𝕜] E) - (C : E →L[𝕜] E)) ≤
          Φ.gauge ((A : E →L[𝕜] E) - (V : E →L[𝕜] E)))
    (huni : ∀ V : E ≃ₗᵢ[𝕜] E,
      (Commute (V : E →L[𝕜] E) K.starProjection ∧
        ∀ W : E ≃ₗᵢ[𝕜] E, Commute (W : E →L[𝕜] E) K.starProjection →
          Φ.gauge ((A : E →L[𝕜] E) - (V : E →L[𝕜] E)) ≤
            Φ.gauge ((A : E →L[𝕜] E) - (W : E →L[𝕜] E))) → V = C) :
    Φ.gauge ((A : E →L[𝕜] E) - (C : E →L[𝕜] E)) ≠ ∞ := by
  intro htop
  have hall (W : E ≃ₗᵢ[𝕜] E) (hW : Commute (W : E →L[𝕜] E) K.starProjection) :
      Φ.gauge ((A : E →L[𝕜] E) - (W : E →L[𝕜] E)) = ∞ := by
    apply top_unique
    simpa only [htop] using hC.2 W hW
  let I := LinearIsometryEquiv.refl 𝕜 E
  let N : E ≃ₗᵢ[𝕜] E := LinearIsometryEquiv.neg 𝕜
  have hI : Commute (I : E →L[𝕜] E) K.starProjection := by
    change Commute 1 K.starProjection
    exact Commute.one_left _
  have hN : Commute (N : E →L[𝕜] E) K.starProjection := by
    ext x
    change -(K.starProjection x) = K.starProjection (-x)
    rw [map_neg]
  have hmin (W : E ≃ₗᵢ[𝕜] E) (hW : Commute (W : E →L[𝕜] E) K.starProjection) :
      ∀ V : E ≃ₗᵢ[𝕜] E, Commute (V : E →L[𝕜] E) K.starProjection →
        Φ.gauge ((A : E →L[𝕜] E) - (W : E →L[𝕜] E)) ≤
          Φ.gauge ((A : E →L[𝕜] E) - (V : E →L[𝕜] E)) := by
    intro V hV
    rw [hall W hW, hall V hV]
  have heq : I = N := (huni I ⟨hI, hmin I hI⟩).trans (huni N ⟨hN, hmin N hN⟩).symm
  have hzero (x : E) : x = 0 := by
    have hx : x = -x := congrArg (fun U : E ≃ₗᵢ[𝕜] E => U x) heq
    have htwo : (2 : 𝕜) • x = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr hx
    exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero
  have hdiff : (A : E →L[𝕜] E) - (C : E →L[𝕜] E) = 0 := by
    ext x
    exact hzero _
  rw [hdiff, Φ.gauge_zero] at htop
  exact ENNReal.zero_ne_top htop

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
