/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import ForTauCeti.Analysis.InnerProductSpace.PrincipalAngles
public import TauCeti.Analysis.InnerProductSpace.Projection.Acute.PrincipalAngle
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
import TauCeti.Analysis.InnerProductSpace.Projection.FrobeniusSine

/-!
# Directed principal-angle geometry

TauCeti supplies the submodule angle maps, the sine embedding, and their
singular values. The basis formulas here use the native cosine spectrum
and directed Frobenius sine. The projection-gap results relate finite
acuteness and its infinite-dimensional obstruction.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Core/AngleGeometry.lean`
before the dependency-closed base of the sin-Θ core moved into the staging
layer.  Statements, proofs, signatures and namespaces are
unchanged; the declarations already lived in `TauCeti.DavisKahan*`, so the move
was a path change and an import repoint and nothing else.

The move became possible only once Y3(b2) took the `ForMathlib`
inner-product-space component into `ForTauCeti`: before that this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
/-- In finite ambient dimension, native acuteness forces a uniform projection gap. -/
theorem projectionGap_lt_one_of_isAcute {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U.IsAcute V) : U.projectionGap V < 1 := by
  obtain ⟨hUV, hVU⟩ := Submodule.isAcute_iff_disjoint.mp h
  rw [Submodule.projectionGap_eq_max, max_lt_iff]
  exact ⟨(Submodule.directedProjectionGap_lt_one_iff U V).mpr hUV,
    (Submodule.directedProjectionGap_lt_one_iff V U).mpr hVU⟩

omit [FiniteDimensional 𝕜 E] in
/-- **What has to fail in infinite dimension: unit vectors of `U` almost
annihilated by `P_V` force the gap up to one.**

This complements native `Submodule.directedProjectionGap_lt_one_iff`.
In finite dimension, compactness makes `inf { ‖P_V x‖ : x ∈ U, ‖x‖ = 1 }` a *minimum* and
transversality makes it positive.  Here the infimum is zero without being
attained — the configuration of principal angles accumulating at `π/2` with none
equal to it — and then `‖(P_U - P_V) x‖ ≥ ‖x‖ - ‖P_V x‖ > 1 - ε` for every `ε`.

Such a pair can still satisfy `Submodule.IsAcute`, since no unit vector of `U` is
annihilated exactly; that is precisely why `projectionGap_lt_one_of_isAcute`
cannot drop `FiniteDimensional`.  No dimension hypothesis is used here. -/
theorem one_le_projectionGap_of_forall_exists_unit_lt {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : ∀ ε : ℝ, 0 < ε → ∃ x ∈ U, ‖x‖ = 1 ∧ ‖V.starProjection x‖ < ε) :
    1 ≤ U.projectionGap V := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  obtain ⟨x, hxU, hxnorm, hxlt⟩ := h (1 - c) (by linarith)
  have hval : (U.starProjection - V.starProjection : E →L[𝕜] E) x
      = x - V.starProjection x := by
    simp [Submodule.starProjection_eq_self_iff.mpr hxU]
  have hle : ‖x‖ - ‖V.starProjection x‖ ≤ ‖U.starProjection - V.starProjection‖ := by
    calc ‖x‖ - ‖V.starProjection x‖
        ≤ ‖x - V.starProjection x‖ := norm_sub_norm_le _ _
      _ = ‖(U.starProjection - V.starProjection : E →L[𝕜] E) x‖ := by rw [hval]
      _ ≤ ‖U.starProjection - V.starProjection‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖U.starProjection - V.starProjection‖ := by rw [hxnorm, mul_one]
  have : c ≤ U.projectionGap V := by
    have hgap : U.projectionGap V = ‖U.starProjection - V.starProjection‖ :=
      Submodule.projectionGap_def U V
    rw [hgap]
    rw [hxnorm] at hle
    linarith
  exact this

/-- **In finite dimension the printed acute case and the uniform (gap) acute
case are the same condition.**

The two predicates this development calls acute — the paper's vanishing crossed
intersections and `‖P_U - P_V‖ < 1` — coincide exactly when the ambient space is
finite dimensional.  Every finite-dimensional theorem stated on one of them may
therefore be read on the other; in infinite dimension they must be kept
apart. -/
theorem isAcute_iff_projectionGap_lt_one {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Submodule.IsAcute U V ↔ U.projectionGap V < 1 :=
  ⟨projectionGap_lt_one_of_isAcute, Submodule.IsAcute.of_projectionGap_lt_one U V⟩

/-! ### Principal-angle energy on a basis of the source subspace -/

/-- **The squared principal cosines summed over an orthonormal basis of `U`.**

`∑ₖ cos²θₖ = ∑ᵢ ‖P_V bᵢ‖²` for every orthonormal basis `b` of `U`.  The right
side is manifestly the Frobenius energy of the cross projection read on `U`;
the left side is the principal-angle sequence, so this is the basis-free
identification of that energy. -/
theorem sum_sq_principalCosines_eq_sum_sq_norm_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U) :
    ∑ i : Fin (finrank 𝕜 U), Submodule.principalCosines U V (i : ℕ) ^ 2 =
      ∑ i, ‖V.starProjection.toLinearMap ((b i : U) : E)‖ ^ 2 := by
  let A : U →L[𝕜] E := V.starProjection ∘L U.subtypeL
  have hσ : U.principalCosines V = A.toLinearMap.singularValues := by
    simpa only [Submodule.toLinearMap_subtypeL, Submodule.range_subtype] using
      (V.principalCosines_range_eq_singularValues (X := U.subtypeL) U.subtypeₗᵢ.isometry)
  rw [hσ]
  calc
    ∑ i : Fin (finrank 𝕜 U), A.toLinearMap.singularValues i ^ 2 =
        A.toLinearMap.singularValues.sum (fun _ s => s ^ 2) :=
      A.toLinearMap.sum_fin_singularValues (· ^ 2) (by simp)
    _ = ∑ i, ‖A.toLinearMap (b i)‖ ^ 2 :=
      RCLike.ofReal_injective
        (A.toLinearMap.trace_adjoint_comp_self_eq_sum_sq_singularValues.symm.trans
          (A.toLinearMap.trace_adjoint_comp_self_eq_sum_norm_apply_sq b))

/-- **`∑ₖ sin²θₖ = ∑ᵢ (1 - ‖P_V bᵢ‖²)` over an orthonormal basis of `U`.**

This is the Davis--Kahan square-sum right-hand side: the deficit of the
`V`-projection energy of a basis of `U`. The directed Frobenius sine identifies
the energy in the orthogonal complement, and Pythagoras gives the deficit. -/
theorem sum_sq_principalSines_eq_sum_one_sub_sq_norm_projection
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U) :
    ∑ i : Fin (finrank 𝕜 U), Submodule.principalSines U V (i : ℕ) ^ 2 =
      ∑ i, (1 - ‖V.starProjection.toLinearMap ((b i : U) : E)‖ ^ 2) := by
  have hsum : ∑ i : Fin (finrank 𝕜 U), U.principalSines V (i : ℕ) ^ 2 =
      (U.sinThetaFrobenius V) ^ 2 := by
    rw [U.sq_sinThetaFrobenius V, ← U.singularValues_sinThetaEmbedding V]
    exact (U.sinThetaEmbedding V).toLinearMap.sum_fin_singularValues (· ^ 2) (by simp)
  rw [hsum, U.sq_sinThetaFrobenius_eq_sum_projection_of_orthonormal V
    (b.orthonormal.comp_linearIsometry U.subtypeₗᵢ)
    ((U.span_range_subtype_eq_top_iff fun i => (b i).property).mp b.toBasis.span_eq)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hunit : ‖((b i : U) : E)‖ = 1 := by
    -- the ambient norm of a subspace vector is its norm in the subspace
    change ‖(b i : U)‖ = 1
    exact b.orthonormal.1 i
  have hpy := V.norm_sq_eq_add_norm_sq_starProjection ((b i : U) : E)
  rw [hunit] at hpy
  -- states both projections in the `starProjection` spelling `hpy` uses
  change ‖Vᗮ.starProjection ((b i : U) : E)‖ ^ 2 =
    1 - ‖V.starProjection ((b i : U) : E)‖ ^ 2
  rw [one_pow] at hpy
  linarith

end TauCeti
