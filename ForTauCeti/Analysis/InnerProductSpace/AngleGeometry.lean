/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import ForTauCeti.Analysis.InnerProductSpace.PrincipalAngles
public import TauCeti.Analysis.InnerProductSpace.Projection.Acute
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap

/-!
# Directed principal-angle geometry

Native submodule principal cosines, sines, angles, tangents and quarter-turn
conditions are consumed directly from TauCeti. This donor retains linear
projection/angle operators, transversality and the remaining projector
consequences. Duplicate sequence definitions and symmetry proofs are retired.

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
/-- The cosine cross-projection `P_V P_U`. -/
@[expose]
noncomputable def cosThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  projection V ∘ₗ projection U

/-- The sine cross-projection `P_{Vᗮ} P_U`. -/
@[expose]
noncomputable def sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  complementaryProjection V ∘ₗ projection U

/-- `cos Θ` on the full ambient space, `|P_V P_U|`.  Its singular values are the
principal-angle cosines by `LinearMap.singularValues_operatorAbs`. -/
noncomputable def cosAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  LinearMap.operatorAbs (cosThetaMap U V)

/-- `sin Θ` on the full ambient space, the modulus `|P_U - P_V|` of the projector
difference.  This is the symmetric full-space sine operator; its singular values
are those of `P_U - P_V` (`singularValues_projection_sub_projection`). -/
@[expose]
noncomputable def sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  LinearMap.operatorAbs (projection U - projection V)

/-- Public characterization of the sine-angle operator as the modulus of the projector
difference.  Keep downstream proofs on this theorem rather than unfolding the definition
directly. -/
theorem sinAngleOperator_eq_operatorAbs (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinAngleOperator U V = LinearMap.operatorAbs (projection U - projection V) :=
  rfl

/-- The one-sided finite-dimensional `sin (2 Θ)` map supported on `U`.

This normalization matches the classic Davis--Kahan UI-norm theorem:
`2 P_{Uᗮ} P_V P_U`.  A separate full positive angle operator would duplicate
nonzero singular values and should not be conflated with this map. -/
@[expose]
noncomputable def sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  (2 : 𝕜) • (complementaryProjection U ∘ₗ projection V ∘ₗ projection U)

omit [FiniteDimensional 𝕜 E] in
/-- `sin Θ` of a subspace with itself is zero: the complementary projector kills
the range of the projector. -/
theorem sinThetaMap_self (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    sinThetaMap U U = 0 := by
  ext x
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change Uᗮ.starProjection (U.starProjection x) = 0
  exact Submodule.starProjection_orthogonal_apply_eq_zero (U.starProjection_apply_mem x)

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

/-- The singular values of `P_U-P_V` are the full-space `sin Θ` values: with
`sinAngleOperator = |P_U - P_V|` and `σ(|T|) = σ(T)` (`LinearMap.singularValues_operatorAbs`). -/
theorem singularValues_projection_sub_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (projection U - projection V).singularValues =
      (sinAngleOperator U V).singularValues := by
  rw [sinAngleOperator, LinearMap.singularValues_operatorAbs]

/-- **The full projector-difference UI-norm bridge.**  Every unitarily invariant
norm of `P_U - P_V` equals that of the full `sin Θ` operator `|P_U - P_V|`, since
they share the singular-value sequence.  This is the only projection-geometry
rewrite the final UI-norm projector theorem needs. -/
theorem uiNorm_projection_sub_eq_sinAngleOperator (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    N (projection U - projection V) = N (sinAngleOperator U V) :=
  N.map_eq_of_singularValues_eq (singularValues_projection_sub_projection U V)

omit [FiniteDimensional 𝕜 E] in
/-- The one-sided double-angle map is exactly twice the cross block.

Signature audit: Valid after defining `sinTwoAngleOperator` as the one-sided
classic Davis--Kahan map rather than a full-space positive operator.
-/
theorem sinTwoAngleOperator_eq_two_smul_cross (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinTwoAngleOperator U V =
      (2 : 𝕜) • (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) := by
  rfl

/-! ### Reading the principal-angle sequence on a basis of the source subspace

`cosThetaMap U V = P_V P_U` and `sinThetaMap U V = P_{Vᗮ} P_U` both vanish on
`Uᗮ`, so restricting their domain to `U` loses nothing: the singular-value
sequence is unchanged.  Combined with the Frobenius identity
`∑ᵢ σᵢ(A)² = ∑ₖ ‖A bₖ‖²` (`sum_sq_singularValues`), this reads the squared
principal cosines and sines as ordinary sums over an orthonormal basis of `U`,
with **no** basis of the ambient space and no trace machinery. -/

section SourceBasis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- **Restricting the domain to a subspace only removes zero padding.**
`A ∘ₗ U.subtype` and `A ∘ₗ P_U` have the same singular values.

The adjoint of the isometric inclusion `U → E` is the orthogonal projection
onto `U`, so the second map is the first precomposed with the adjoint of an
isometric embedding, which is `LinearMap.singularValues_comp_adjoint_linearIsometry`. -/
theorem singularValues_comp_subtype (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →ₗ[𝕜] F) :
    (A ∘ₗ U.subtype).singularValues = (A ∘ₗ projection U).singularValues := by
  have hsub : U.subtypeₗᵢ.toLinearMap = U.subtype := by
    ext x
    rfl
  have hadj : LinearMap.adjoint U.subtypeₗᵢ.toLinearMap =
      U.orthogonalProjectionOnto.toLinearMap := by
    rw [hsub, eq_comm]
    refine (LinearMap.eq_adjoint_iff U.orthogonalProjectionOnto.toLinearMap
      U.subtype).2 fun x y => ?_
    -- states the goal in the ambient space, where the projection's defining
    -- property applies; there is no `_apply` lemma to rewrite with here.
    change ⟪U.starProjection x, (y : E)⟫_𝕜 = ⟪x, (y : E)⟫_𝕜
    rw [U.inner_starProjection_left_eq_right,
      U.starProjection_eq_self_iff.mpr y.2]
  have hcomp : (A ∘ₗ U.subtype) ∘ₗ LinearMap.adjoint U.subtypeₗᵢ.toLinearMap =
      A ∘ₗ projection U := by
    rw [hadj]
    ext x
    rfl
  rw [← hcomp, LinearMap.singularValues_comp_adjoint_linearIsometry]

omit [FiniteDimensional 𝕜 E] in
/-- The cosine cross projection is unchanged by precomposition with `P_U`. -/
theorem cosThetaMap_comp_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    cosThetaMap U V ∘ₗ projection U = cosThetaMap U V := by
  ext x
  -- exposes the two nested projections, which no `simp` lemma reassociates.
  change V.starProjection (U.starProjection (U.starProjection x)) =
    V.starProjection (U.starProjection x)
  rw [U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)]

omit [FiniteDimensional 𝕜 E] in
/-- The sine cross projection is unchanged by precomposition with `P_U`. -/
theorem sinThetaMap_comp_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinThetaMap U V ∘ₗ projection U = sinThetaMap U V := by
  ext x
  -- exposes the two nested projections, which no `simp` lemma reassociates.
  change Vᗮ.starProjection (U.starProjection (U.starProjection x)) =
    Vᗮ.starProjection (U.starProjection x)
  rw [U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)]

/-- The principal cosines are the singular values of `P_V P_U` restricted to
`U`, with no zero padding removed. -/
theorem singularValues_cosThetaMap_comp_subtype (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (cosThetaMap U V ∘ₗ U.subtype).singularValues = Submodule.principalCosines U V := by
  rw [singularValues_comp_subtype, cosThetaMap_comp_projection,
    Submodule.principalCosines_def, Submodule.cosThetaMap_def]
  rfl

/-- The principal sines are the singular values of `P_{Vᗮ} P_U` restricted to
`U`. -/
theorem singularValues_sinThetaMap_comp_subtype (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (sinThetaMap U V ∘ₗ U.subtype).singularValues = Submodule.principalSines U V := by
  rw [singularValues_comp_subtype, sinThetaMap_comp_projection,
    Submodule.principalSines_def, Submodule.sinThetaMap_def]
  rfl

/-- **The squared principal cosines summed over an orthonormal basis of `U`.**

`∑ₖ cos²θₖ = ∑ᵢ ‖P_V bᵢ‖²` for every orthonormal basis `b` of `U`.  The right
side is manifestly the Frobenius energy of the cross projection read on `U`;
the left side is the principal-angle sequence, so this is the basis-free
identification of that energy. -/
theorem sum_sq_principalCosines_eq_sum_sq_norm_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U) :
    ∑ i : Fin (finrank 𝕜 U), Submodule.principalCosines U V (i : ℕ) ^ 2 =
      ∑ i, ‖projection V ((b i : U) : E)‖ ^ 2 := by
  have happ : ∀ i, (cosThetaMap U V ∘ₗ U.subtype) (b i) =
      projection V ((b i : U) : E) := by
    intro i
    -- exposes the inner projection, which is the identity on a vector of `U`.
    change V.starProjection (U.starProjection ((b i : U) : E)) =
      V.starProjection ((b i : U) : E)
    rw [U.starProjection_eq_self_iff.mpr (b i).2]
  rw [← singularValues_cosThetaMap_comp_subtype U V,
    sum_sq_singularValues (cosThetaMap U V ∘ₗ U.subtype) rfl b]
  simp only [happ]

/-- **The squared principal sines summed over an orthonormal basis of `U`.**

`∑ₖ sin²θₖ = ∑ᵢ ‖P_{Vᗮ} bᵢ‖²` for every orthonormal basis `b` of `U`. -/
theorem sum_sq_principalSines_eq_sum_sq_norm_complementaryProjection
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U) :
    ∑ i : Fin (finrank 𝕜 U), Submodule.principalSines U V (i : ℕ) ^ 2 =
      ∑ i, ‖complementaryProjection V ((b i : U) : E)‖ ^ 2 := by
  have happ : ∀ i, (sinThetaMap U V ∘ₗ U.subtype) (b i) =
      complementaryProjection V ((b i : U) : E) := by
    intro i
    -- exposes the inner projection, which is the identity on a vector of `U`.
    change Vᗮ.starProjection (U.starProjection ((b i : U) : E)) =
      Vᗮ.starProjection ((b i : U) : E)
    rw [U.starProjection_eq_self_iff.mpr (b i).2]
  rw [← singularValues_sinThetaMap_comp_subtype U V,
    sum_sq_singularValues (sinThetaMap U V ∘ₗ U.subtype) rfl b]
  simp only [happ]

/-- **`∑ₖ sin²θₖ = ∑ᵢ (1 - ‖P_V bᵢ‖²)` over an orthonormal basis of `U`.**

This is the Davis--Kahan square-sum right-hand side: the deficit of the
`V`-projection energy of a basis of `U`, term by term the Pythagorean
complement of `sum_sq_principalCosines_eq_sum_sq_norm_projection`.  It is the
identity that turns a statement about the basis into the printed statement
about the principal angles. -/
theorem sum_sq_principalSines_eq_sum_one_sub_sq_norm_projection
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (b : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U) :
    ∑ i : Fin (finrank 𝕜 U), Submodule.principalSines U V (i : ℕ) ^ 2 =
      ∑ i, (1 - ‖projection V ((b i : U) : E)‖ ^ 2) := by
  rw [sum_sq_principalSines_eq_sum_sq_norm_complementaryProjection U V b]
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

end SourceBasis

end TauCeti
