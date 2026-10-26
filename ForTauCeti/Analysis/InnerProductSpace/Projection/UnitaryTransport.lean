/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import ForTauCeti.Analysis.InnerProductSpace.Projection.KernelSupport

/-!
# Subspace transport as reflection intertwining

An ambient isometric equivalence carries one subspace onto another exactly
when it intertwines their reflections.
-/

public section

namespace Submodule

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

/-- Subspace transport is equivalent to conjugacy of the actual
orthogonal projections, in arbitrary Hilbert dimension. -/
theorem map_eq_iff_conjugate_starProjection [CompleteSpace E]
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) :
    K.map U.toLinearMap = L ↔
      (U : E →L[𝕜] E) * K.starProjection * star (U : E →L[𝕜] E) = L.starProjection := by
  have hs : star (U : E →L[𝕜] E) = (U.symm : E →L[𝕜] E) := U.adjoint_eq_symm
  have hp : (K.map U.toLinearMap).starProjection =
      (U : E →L[𝕜] E) * K.starProjection * star (U : E →L[𝕜] E) := by
    ext x
    rw [starProjection_map_apply, hs]
    rfl
  constructor
  · intro h
    simpa only [h] using hp.symm
  · intro h
    have heq := hp.trans h
    rw [← range_starProjection (K.map U.toLinearMap), ← range_starProjection L, heq]

/-- An isometric equivalence transports subspaces exactly when it
intertwines their orthogonal reflections. -/
theorem map_eq_iff_intertwines_reflection
    (U : Submodule 𝕜 E) (V : Submodule 𝕜 F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] F) :
    U.map W.toLinearMap = V ↔ ∀ x, W (U.reflection x) = V.reflection (W x) := by
  constructor
  · intro h x
    have href := reflection_map_apply W U (W x)
    change (U.map W.toLinearMap).reflection (W x) = _ at href
    simpa only [h, W.symm_apply_apply] using href.symm
  · intro h
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply (reflection_eq_self_iff _).mp
      change V.reflection (W x) = W x
      rw [← h, reflection_mem_subspace_eq_self hx]
    · intro hy
      refine ⟨W.symm y, ?_, W.apply_symm_apply y⟩
      apply (reflection_eq_self_iff _).mp
      apply W.injective
      rw [h, W.apply_symm_apply, reflection_mem_subspace_eq_self hy]

/-- The relative unitary of two transports of the same subspaces commutes
with the source reflection. No dimension or completeness assumption is needed. -/
theorem relative_transport_commutes_reflection
    (U : Submodule 𝕜 E) (V : Submodule 𝕜 F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (R T : E ≃ₗᵢ[𝕜] F) (hR : U.map R.toLinearMap = V) (hT : U.map T.toLinearMap = V)
    (x : E) :
    (R.trans T.symm) (U.reflection x) = U.reflection ((R.trans T.symm) x) := by
  have hRref := (U.map_eq_iff_intertwines_reflection V R).mp hR
  have hTref := (U.map_eq_iff_intertwines_reflection V T).mp hT
  apply T.injective
  change T (T.symm (R (U.reflection x))) = T (U.reflection (T.symm (R x)))
  rw [T.apply_symm_apply, hTref, T.apply_symm_apply, hRref]

/-- Affine phase parameters of relative unitaries cannot change faster
than the ambient unitaries. This estimate is valid over either field,
without finite dimension or completeness. -/
theorem relative_phase_projection_separation
    (N : Submodule 𝕜 E) (R T₁ T₂ : E ≃ₗᵢ[𝕜] E)
    (Q₁ Q₂ : N →L[𝕜] N) (alpha kappa : 𝕜)
    (h₁ : ∀ x : N, (R.trans T₁.symm) x = alpha • (x : E) + kappa • (Q₁ x : E))
    (h₂ : ∀ x : N, (R.trans T₂.symm) x = alpha • (x : E) + kappa • (Q₂ x : E)) :
    ‖kappa‖ * ‖Q₁ - Q₂‖ ≤ ‖(T₁ : E →L[𝕜] E) - (T₂ : E →L[𝕜] E)‖ := by
  have hbound : ‖kappa • (Q₁ - Q₂)‖ ≤ ‖(T₁ : E →L[𝕜] E) - (T₂ : E →L[𝕜] E)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    let Z₁ := R.trans T₁.symm
    let Z₂ := R.trans T₂.symm
    have hvec : ((kappa • (Q₁ - Q₂)) x : E) = Z₁ x - Z₂ x := by
      change kappa • ((Q₁ x : E) - (Q₂ x : E)) = _
      rw [show Z₁ x = _ from h₁ x, show Z₂ x = _ from h₂ x]
      simp only [smul_sub]
      rw [add_sub_add_left_eq_sub]
    calc
      ‖(kappa • (Q₁ - Q₂)) x‖ = ‖Z₁ x - Z₂ x‖ := by rw [← hvec]; rfl
      _ = ‖T₁ (Z₁ x - Z₂ x)‖ := (T₁.norm_map _).symm
      _ = ‖((T₂ : E →L[𝕜] E) - (T₁ : E →L[𝕜] E)) (Z₂ x)‖ := by
        congr 1
        change T₁ (T₁.symm (R x) - T₂.symm (R x)) =
          T₂ (T₂.symm (R x)) - T₁ (T₂.symm (R x))
        rw [map_sub, T₁.apply_symm_apply, T₂.apply_symm_apply]
      _ ≤ ‖(T₂ : E →L[𝕜] E) - (T₁ : E →L[𝕜] E)‖ * ‖Z₂ x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖(T₁ : E →L[𝕜] E) - (T₂ : E →L[𝕜] E)‖ * ‖x‖ := by
        rw [Z₂.norm_map, norm_sub_rev]
        rfl
  simpa only [norm_smul] using hbound

end Submodule

namespace LinearIsometryEquiv

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A relative unitary determines the original isometric equivalence. -/
theorem eq_of_relative_eq (R : E ≃ₗᵢ[𝕜] E) {T S : E ≃ₗᵢ[𝕜] E}
    (h : (R.trans T.symm : E →L[𝕜] E) = (R.trans S.symm : E →L[𝕜] E)) : T = S := by
  have hsymm : T.symm = S.symm := by
    ext x
    have hx := DFunLike.congr_fun h (R.symm x)
    change T.symm (R (R.symm x)) = S.symm (R (R.symm x)) at hx
    simpa only [R.apply_symm_apply] using hx
  simpa only [LinearIsometryEquiv.symm_symm] using
    congrArg (fun V : E ≃ₗᵢ[𝕜] E => V.symm) hsymm

/-- Equality of two relative unitaries after left multiplication determines
the original unitaries on the orthogonal complement of the multiplier's
kernel. No positivity, normality, completeness, or finite dimension is needed. -/
theorem eq_on_orthogonal_ker_of_relative_left_mul_eq
    (C : E →L[𝕜] E) (R T S : E ≃ₗᵢ[𝕜] E)
    (h : C * (R.trans T.symm : E →L[𝕜] E) =
      C * (R.trans S.symm : E →L[𝕜] E)) :
    ∀ x ∈ C.kerᗮ, T x = S x := by
  have hker (y : E) : T.symm y - S.symm y ∈ C.ker := by
    have hy := DFunLike.congr_fun h (R.symm y)
    change C (T.symm (R (R.symm y))) = C (S.symm (R (R.symm y))) at hy
    rw [R.apply_symm_apply] at hy
    change C (T.symm y - S.symm y) = 0
    rw [C.map_sub, hy, sub_self]
  have hinner (U : E ≃ₗᵢ[𝕜] E) (x y : E) :
      inner 𝕜 (U.symm y) x = inner 𝕜 y (U x) := by
    have hu := U.inner_map_map (U.symm y) x
    rw [U.apply_symm_apply] at hu
    exact hu.symm
  intro x hx
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
  have hz := hx (T.symm (T x - S x) - S.symm (T x - S x)) (hker (T x - S x))
  rw [inner_sub_left, hinner, hinner, ← inner_sub_right] at hz
  exact hz

/-- Taking relative inverses against a fixed isometry preserves operator
distance. No completeness or finite-dimensional assumption is required. -/
theorem norm_sub_relative (R T S : E ≃ₗᵢ[𝕜] E) :
    ‖(R.trans T.symm : E →L[𝕜] E) - (R.trans S.symm : E →L[𝕜] E)‖ =
      ‖(T : E →L[𝕜] E) - (S : E →L[𝕜] E)‖ := by
  have hfac : (R.trans T.symm : E →L[𝕜] E) - (R.trans S.symm : E →L[𝕜] E) =
      (T.symm : E →L[𝕜] E).comp
        (((S : E →L[𝕜] E) - (T : E →L[𝕜] E)).comp (R.trans S.symm : E →L[𝕜] E)) := by
    ext x
    change T.symm (R x) - S.symm (R x) =
      T.symm (S (S.symm (R x)) - T (S.symm (R x)))
    rw [map_sub, S.apply_symm_apply, T.symm_apply_apply]
  rw [hfac, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, norm_sub_rev]

/-- A common affine parameterization of the whole relative unitary has
an exact operator-distance formula, stronger than a restriction estimate. -/
theorem norm_sub_eq_of_relative_affine
    (R T S : E ≃ₗᵢ[𝕜] E) (P Q A : E →L[𝕜] E) (kappa : 𝕜)
    (hT : (R.trans T.symm : E →L[𝕜] E) = A + kappa • P)
    (hS : (R.trans S.symm : E →L[𝕜] E) = A + kappa • Q) :
    ‖(T : E →L[𝕜] E) - (S : E →L[𝕜] E)‖ = ‖kappa‖ * ‖P - Q‖ := by
  rw [← norm_sub_relative R T S, hT, hS, add_sub_add_left_eq_sub, ← smul_sub, norm_smul]

/-- Passing to right relative unitaries preserves operator distance. -/
theorem norm_sub_right_relative (R T S : E ≃ₗᵢ[𝕜] E) :
    ‖(T.trans R.symm : E →L[𝕜] E) - (S.trans R.symm : E →L[𝕜] E)‖ =
      ‖(T : E →L[𝕜] E) - (S : E →L[𝕜] E)‖ := by
  have hfac : (T.trans R.symm : E →L[𝕜] E) - (S.trans R.symm : E →L[𝕜] E) =
      (R.symm : E →L[𝕜] E).comp ((T : E →L[𝕜] E) - (S : E →L[𝕜] E)) := by
    ext x
    exact (R.symm.map_sub (T x) (S x)).symm
  rw [hfac, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp]

/-- A split formula for right relative phases gives an exact operator
distance formula. The two coefficient maps need not be scalar, and the
parameter maps need not be projections. No completeness or finite
dimension is required. -/
theorem norm_sub_eq_of_right_relative_split
    (R T S : E ≃ₗᵢ[𝕜] E) (F G P Q : E →L[𝕜] E)
    (hT : (T.trans R.symm : E →L[𝕜] E) = F * P + G * (1 - P))
    (hS : (S.trans R.symm : E →L[𝕜] E) = F * Q + G * (1 - Q)) :
    ‖(T : E →L[𝕜] E) - (S : E →L[𝕜] E)‖ = ‖(F - G) * (P - Q)‖ := by
  rw [← norm_sub_right_relative R T S, hT, hS]
  congr 1
  simp only [mul_sub, sub_mul, mul_one]
  abel

/-- Normalized split parameters admit uniform operator-norm recovery from
the unitaries whenever the effective phase-weight space is finite
dimensional. The coefficients and reference unitary are fixed; the bound
is uniform over all parameters and unitary pairs satisfying the formulas. -/
theorem exists_pos_normalized_split_parameter_recovery
    (R : E ≃ₗᵢ[𝕜] E) (C F G : E →L[𝕜] E)
    [FiniteDimensional 𝕜 (C * (F - G)).kerᗮ] :
    ∃ k : ℝ, 0 < k ∧ ∀ (T S : E ≃ₗᵢ[𝕜] E) (P Q : E →L[𝕜] E),
      (∀ x, P x ∈ (C * (F - G)).kerᗮ) →
      (∀ x, Q x ∈ (C * (F - G)).kerᗮ) →
      C * (T.trans R.symm : E →L[𝕜] E) = C * (F * P + G * (1 - P)) →
      C * (S.trans R.symm : E →L[𝕜] E) = C * (F * Q + G * (1 - Q)) →
      ‖P - Q‖ ≤ (k * ‖C‖) * ‖(T : E →L[𝕜] E) - (S : E →L[𝕜] E)‖ := by
  obtain ⟨k, hk, hbound⟩ :=
    ContinuousLinearMap.exists_pos_norm_le_mul_norm_mul_on_orthogonal_ker (C * (F - G))
  refine ⟨k, hk, fun T S P Q hP hQ hT hS => ?_⟩
  have hdiff : C * (F - G) * (P - Q) =
      C * ((T.trans R.symm : E →L[𝕜] E) - (S.trans R.symm : E →L[𝕜] E)) := by
    rw [mul_sub C (T.trans R.symm : E →L[𝕜] E) (S.trans R.symm : E →L[𝕜] E), hT, hS]
    noncomm_ring
  calc
    ‖P - Q‖ ≤ k * ‖C * (F - G) * (P - Q)‖ :=
      hbound (P - Q) (fun x => (C * (F - G)).kerᗮ.sub_mem (hP x) (hQ x))
    _ = k * ‖C * ((T.trans R.symm : E →L[𝕜] E) -
        (S.trans R.symm : E →L[𝕜] E))‖ := by rw [hdiff]
    _ ≤ k * (‖C‖ * ‖(T.trans R.symm : E →L[𝕜] E) -
        (S.trans R.symm : E →L[𝕜] E)‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) hk.le
    _ = (k * ‖C‖) * ‖(T : E →L[𝕜] E) - (S : E →L[𝕜] E)‖ := by
      rw [norm_sub_right_relative, mul_assoc]

/-- Normalized split parameters admit uniform operator-norm recovery from
the unitaries whenever the effective phase-weight space is finite
dimensional. This is the left relative-phase convention. The coefficients
and reference unitary are fixed; the bound is uniform over all parameters
and unitary pairs satisfying the formulas. -/
theorem exists_pos_normalized_left_split_parameter_recovery
    (R : E ≃ₗᵢ[𝕜] E) (C F G : E →L[𝕜] E)
    [FiniteDimensional 𝕜 (C * (F - G)).kerᗮ] :
    ∃ k : ℝ, 0 < k ∧ ∀ (T S : E ≃ₗᵢ[𝕜] E) (P Q : E →L[𝕜] E),
      (∀ x, P x ∈ (C * (F - G)).kerᗮ) →
      (∀ x, Q x ∈ (C * (F - G)).kerᗮ) →
      C * (R.trans T.symm : E →L[𝕜] E) = C * (F * P + G * (1 - P)) →
      C * (R.trans S.symm : E →L[𝕜] E) = C * (F * Q + G * (1 - Q)) →
      ‖P - Q‖ ≤ (k * ‖C‖) * ‖(T : E →L[𝕜] E) - (S : E →L[𝕜] E)‖ := by
  obtain ⟨k, hk, hbound⟩ :=
    ContinuousLinearMap.exists_pos_norm_le_mul_norm_mul_on_orthogonal_ker (C * (F - G))
  refine ⟨k, hk, fun T S P Q hP hQ hT hS => ?_⟩
  have hdiff : C * (F - G) * (P - Q) =
      C * ((R.trans T.symm : E →L[𝕜] E) - (R.trans S.symm : E →L[𝕜] E)) := by
    rw [mul_sub C (R.trans T.symm : E →L[𝕜] E) (R.trans S.symm : E →L[𝕜] E), hT, hS]
    noncomm_ring
  calc
    ‖P - Q‖ ≤ k * ‖C * (F - G) * (P - Q)‖ :=
      hbound (P - Q) (fun x => (C * (F - G)).kerᗮ.sub_mem (hP x) (hQ x))
    _ = k * ‖C * ((R.trans T.symm : E →L[𝕜] E) -
        (R.trans S.symm : E →L[𝕜] E))‖ := by rw [hdiff]
    _ ≤ k * (‖C‖ * ‖(R.trans T.symm : E →L[𝕜] E) -
        (R.trans S.symm : E →L[𝕜] E)‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) hk.le
    _ = (k * ‖C‖) * ‖(T : E →L[𝕜] E) - (S : E →L[𝕜] E)‖ := by
      rw [norm_sub_relative, mul_assoc]

end LinearIsometryEquiv
