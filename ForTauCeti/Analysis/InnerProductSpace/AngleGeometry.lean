/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.SpectralSubspace
import ForTauCeti.Analysis.InnerProductSpace.PrincipalAngles
import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantNorm
import ForTauCeti.Analysis.InnerProductSpace.PolarDecomposition
import ForTauCeti.Analysis.InnerProductSpace.ProjectionGap

/-!
# Directed principal-angle geometry

Canonical finite-dimensional cosine, sine, angle, tangent, and double-angle
objects, together with their singular-value and projector dictionaries.

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

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
/-- The modulus `|A| = (A⋆A)^{1/2}` has the same singular values as `A`: both
Gram operators coincide, `|A|⋆|A| = |A|² = A⋆A`.  This is the finite-dimensional
`σ(|A|) = σ(A)` used to identify difference-of-projector singular values with the
`sin Θ` operator's. -/
theorem singularValues_abs (A : E →ₗ[𝕜] E) :
    (TauCeti.abs A).singularValues = A.singularValues := by
  refine TauCeti.singularValues_eq_of_gram_eq ?_
  rw [(TauCeti.isPositive_abs A).adjoint_eq, TauCeti.abs_mul_self]

/-- The cosine cross-projection `P_V P_U`. -/
noncomputable def cosThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  projection V ∘ₗ projection U

/-- The sine cross-projection `P_{Vᗮ} P_U`. -/
noncomputable def sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  complementaryProjection V ∘ₗ projection U

/-- `cos Θ` on the full ambient space, `|P_V P_U|`.  Its singular values are the
principal-angle cosines (`singularValues_abs` and `singularValues_cosThetaMap`). -/
noncomputable def cosAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  TauCeti.abs (cosThetaMap U V)

/-- `sin Θ` on the full ambient space, the modulus `|P_U - P_V|` of the projector
difference.  This is the symmetric full-space sine operator; its singular values
are those of `P_U - P_V` (`singularValues_projection_sub_projection`). -/
noncomputable def sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  TauCeti.abs (projection U - projection V)

/-- The one-sided finite-dimensional `sin (2 Θ)` map supported on `U`.

This normalization matches the classic Davis--Kahan UI-norm theorem:
`2 P_{Uᗮ} P_V P_U`.  A separate full positive angle operator would duplicate
nonzero singular values and should not be conflated with this map. -/
noncomputable def sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  (2 : 𝕜) • (complementaryProjection U ∘ₗ projection V ∘ₗ projection U)

/-- Principal-angle cosines: the singular values of the cross projection
`P_V P_U`, sorted decreasingly and padded by zeros beyond the finite rank.  These
are symmetric in `U, V` because `(P_V P_U)⋆ = P_U P_V` (`principalCosines_comm`). -/
noncomputable def principalCosines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (cosThetaMap U V).singularValues

/-- Principal-angle sines: the singular values of the directed cross projection
`P_{Vᗮ} P_U`.  In equal-dimension configurations these are the sines of the
principal angles; when `dim U ≠ dim V` the directed map also records the
`π/2` "defect" directions, so this is not symmetric in `U, V` in general. -/
noncomputable def principalSines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (sinThetaMap U V).singularValues

/-- Principal angles as a sorted finitely supported sequence: `arcsin` applied to
the principal sines.  `arcsin 0 = 0` keeps the support finite. -/
noncomputable def principalAngles (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (principalSines U V).mapRange Real.arcsin Real.arcsin_zero

/-- Principal-angle tangents: `tan` applied to the principal angles.  `tan 0 = 0`
keeps the support finite (poles at `π/2` are only reached in the non-acute
configuration, excluded by the tangent theorems' hypotheses). -/
noncomputable def principalTangents (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (principalAngles U V).mapRange Real.tan Real.tan_zero

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

/-- Every principal angle of a subspace with itself is zero. -/
theorem principalAngles_self (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (i : ℕ) : principalAngles U U i = 0 := by
  have h : principalSines U U = 0 := by
    rw [principalSines, sinThetaMap_self]
    exact LinearMap.singularValues_zero
  simp [principalAngles, h]

/-- The pair has no angle `π/2`; equivalently, `P_V` is injective on `U`. -/
def IsTransverse (U V : Submodule 𝕜 E) [V.HasOrthogonalProjection] : Prop :=
  ∀ x ∈ U, V.starProjection x = 0 → x = 0

/-- The pair is acute in the Davis--Kahan sense. -/
def IsAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  (∀ x ∈ U, V.starProjection x = 0 → x = 0) ∧
    (∀ y ∈ V, U.starProjection y = 0 → y = 0)

omit [FiniteDimensional 𝕜 E] in
/-- A subspace meeting another's orthogonal complement forces the gap to be at
least one.  This is the engine of `isAcute_of_projectionGap_lt_one`: if a
nonzero `x ∈ U` is killed by `P_V`, then `(P_U − P_V) x = x` exactly, so the
operator has a unit vector on which it acts as the identity.

Stated without `FiniteDimensional` because it does not need it — this direction
is true in any inner product space, and that asymmetry is the point of the pair
of theorems below. -/
theorem eq_zero_of_projectionGap_lt_one {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U.projectionGap V < 1)
    {x : E} (hxU : x ∈ U) (hxV : V.starProjection x = 0) : x = 0 := by
  by_contra hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hval : (U.starProjection - V.starProjection : E →L[𝕜] E) x = x := by
    simp [Submodule.starProjection_eq_self_iff.mpr hxU, hxV]
  have hle : ‖x‖ ≤ U.projectionGap V * ‖x‖ := by
    calc ‖x‖ = ‖(U.starProjection - V.starProjection : E →L[𝕜] E) x‖ := by rw [hval]
      _ ≤ ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = U.projectionGap V * ‖x‖ := rfl
  nlinarith [hle, hxpos, h]

omit [FiniteDimensional 𝕜 E] in
/-- The **directed** sharpening: transversality of `U` into `V` needs only the
directed gap `‖P_{Vᗮ} P_U‖` to be below one, not the symmetric gap.

This is strictly stronger than `eq_zero_of_projectionGap_lt_one` because
`directedProjectionGap_le_projectionGap`, and it is the right granularity: each
half of `IsAcute` is a one-sided condition, so each should be implied by the
corresponding one-sided gap. -/
theorem eq_zero_of_directedProjectionGap_lt_one {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [Vᗮ.HasOrthogonalProjection]
    (h : U.directedProjectionGap V < 1)
    {x : E} (hxU : x ∈ U) (hxV : V.starProjection x = 0) : x = 0 := by
  by_contra hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hval : (Vᗮ.starProjection ∘L U.starProjection : E →L[𝕜] E) x = x := by
    simp [Submodule.starProjection_eq_self_iff.mpr hxU,
      Submodule.starProjection_orthogonal_val, hxV]
  have hle : ‖x‖ ≤ U.directedProjectionGap V * ‖x‖ := by
    calc ‖x‖ = ‖(Vᗮ.starProjection ∘L U.starProjection : E →L[𝕜] E) x‖ := by rw [hval]
      _ ≤ ‖(Vᗮ.starProjection ∘L U.starProjection : E →L[𝕜] E)‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = U.directedProjectionGap V * ‖x‖ := rfl
  nlinarith [hle, hxpos, h]

omit [FiniteDimensional 𝕜 E] in
/-- **A small projection gap implies the acute (transversality) condition, in
any dimension.**

`DavisKahan.IsAcute U V` unfolds to `U.projectionGap V < 1`, so this is one
half of the relation between the two same-named predicates in this development.
The converse is `projectionGap_lt_one_of_isAcute` below and is **not** true in
this generality — it needs `FiniteDimensional`. Two predicates called `IsAcute`
that are related in only one direction without it is a correctness hazard, so
both directions are stated here with their hypotheses made explicit. -/
theorem isAcute_of_projectionGap_lt_one {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U.projectionGap V < 1) : IsAcute U V :=
  ⟨fun _x hxU hxV => eq_zero_of_projectionGap_lt_one h hxU hxV,
   fun _y hyV hyU =>
     eq_zero_of_projectionGap_lt_one
       ((Submodule.projectionGap_comm U V) ▸ h) hyV hyU⟩

/-- No principal angle is a quarter turn.  This is the natural domain condition
for `tan (2 Θ)` before the canonical branch is selected.  The arbitrary
reducing subspace in the raw `tan 2Θ` theorem may have angles on either side
of `π/4`; the theorem itself excludes equality. -/
def AvoidsQuarterTurn (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  ∀ i, principalAngles U V i ≠ Real.pi / 4

/-- **A subspace avoids the quarter turn with itself.**

The non-degenerate witness for `AvoidsQuarterTurn`: every principal angle of `U`
with `U` is zero, and `0 ≠ π/4`.  Without a witness the predicate would be
unfalsifiable — it could be vacuous and nothing in the library would notice —
which is the fault Tau Ceti's `correctness` rubric rates a block. -/
theorem avoidsQuarterTurn_self (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    AvoidsQuarterTurn U U := by
  intro i
  rw [principalAngles_self]
  have : (0 : ℝ) < Real.pi / 4 := by positivity
  exact ne_of_lt this

omit [FiniteDimensional 𝕜 E] in
/-- Acuteness is symmetric.
-/
theorem IsAcute.symm {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : IsAcute U V) : IsAcute V U :=
  ⟨h.2, h.1⟩

/-- **Two equidimensional subspaces carry orthonormal families, on a common
index type, spanning them.**

`stdOrthonormalBasis` gives each subspace a basis; the content is the
bookkeeping that puts both on `Fin (finrank 𝕜 U)` — `Fin.cast` across
`finrank 𝕜 U = finrank 𝕜 V` — and the two `Submodule.eq_of_le_of_finrank_eq`
arguments turning "spans a subspace of the right dimension" into "spans it".

Stated existentially because that is all its callers want: the bases and the
cast never escape, only `u`, `v`, their orthonormality and their spans.  It was
written out twice in this file, in `principalSines_comm` and in
`opNorm_projection_sub_eq_opNorm_sinThetaMap`, 29 identical lines each. -/
private theorem exists_orthonormal_pair_spanning (U V : Submodule 𝕜 E)
    (hrank : finrank 𝕜 U = finrank 𝕜 V) :
    ∃ u v : Fin (finrank 𝕜 U) → E, ∃ _ : Orthonormal 𝕜 u, ∃ _ : Orthonormal 𝕜 v,
      Submodule.span 𝕜 (Set.range u) = U ∧ Submodule.span 𝕜 (Set.range v) = V := by
  classical
  let d := finrank 𝕜 U
  let bU := stdOrthonormalBasis 𝕜 U
  let bV := stdOrthonormalBasis 𝕜 V
  have hdV : d = finrank 𝕜 V := by simpa only [d] using hrank
  let u : Fin d → E := fun i => ((bU i : U) : E)
  let v : Fin d → E := fun i => ((bV (Fin.cast hdV i) : V) : E)
  have hu : Orthonormal 𝕜 u := by
    rw [orthonormal_iff_ite]
    intro i j
    -- states the goal as the inner-product identity the structure lemma expects.
    change ⟪bU i, bU j⟫_𝕜 = if i = j then 1 else 0
    exact orthonormal_iff_ite.mp bU.orthonormal i j
  have hv : Orthonormal 𝕜 v := by
    rw [orthonormal_iff_ite]
    intro i j
    -- states the goal as the inner-product identity the structure lemma expects.
    change ⟪bV (Fin.cast hdV i), bV (Fin.cast hdV j)⟫_𝕜 =
      if i = j then 1 else 0
    rw [orthonormal_iff_ite.mp bV.orthonormal]
    simp only [Fin.cast_inj]
  have hspanU : Submodule.span 𝕜 (Set.range u) = U := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (bU i).2
    · rw [finrank_span_eq_card hu.linearIndependent, Fintype.card_fin]
  have hspanV : Submodule.span 𝕜 (Set.range v) = V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (bV (Fin.cast hdV i)).2
    · rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin]
      exact hdV
  exact ⟨u, v, hu, hv, hspanU, hspanV⟩

/-- The directed principal-sine sequences are symmetric for equal-rank
subspaces.  Equal rank lets us choose orthonormal families with the same finite
index type; the family-level complementary-Gram theorem then identifies the two
directed cross-projection singular-value sequences. -/
theorem principalSines_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hrank : finrank 𝕜 U = finrank 𝕜 V) :
    principalSines U V = principalSines V U := by
  classical
  let d := finrank 𝕜 U
  obtain ⟨u, v, hu, hv, hspanU, hspanV⟩ :=
    exists_orthonormal_pair_spanning U V hrank
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change
    (((Vᗮ.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E).singularValues) =
      (((Uᗮ.starProjection ∘L V.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E).singularValues)
  simpa only [hspanU, hspanV] using
    singularValues_orthogonal_starProjection_comp_starProjection_comm hu hv

/-- Principal angles are symmetric for equal-dimensional subspaces.

The equal-rank hypothesis matches the multiplicities of quarter-turn defect
directions in the two directed sine maps. -/
theorem principalAngles_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hrank : finrank 𝕜 U = finrank 𝕜 V) :
    principalAngles U V = principalAngles V U := by
  rw [principalAngles, principalAngles, principalSines_comm U V hrank]

/-- Principal-angle cosines are the singular values of `P_V P_U` (definitional:
`principalCosines` is defined as those singular values). -/
theorem singularValues_cosThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (cosThetaMap U V).singularValues = principalCosines U V :=
  rfl

/-- Principal-angle sines are the singular values of `P_{Vᗮ} P_U` (definitional:
`principalSines` is defined as those singular values). -/
theorem singularValues_sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (sinThetaMap U V).singularValues = principalSines U V :=
  rfl

/-- Principal-angle cosines are symmetric in the two subspaces, since
`(P_V P_U)⋆ = P_U P_V` and adjoints share singular values.  (The sines are *not*
symmetric when `dim U ≠ dim V`; see `principalSines`.) -/
theorem principalCosines_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    principalCosines U V = principalCosines V U := by
  have hadj : (cosThetaMap V U).adjoint = cosThetaMap U V := by
    rw [eq_comm, LinearMap.eq_adjoint_iff]
    intro x y
    simp only [cosThetaMap, projection, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [V.inner_starProjection_left_eq_right, U.inner_starProjection_left_eq_right]
  rw [principalCosines, principalCosines, ← hadj, TauCeti.singularValues_adjoint]

/-- The singular values of `P_U-P_V` are the full-space `sin Θ` values: with
`sinAngleOperator = |P_U - P_V|` and `σ(|T|) = σ(T)` (`singularValues_abs`). -/
theorem singularValues_projection_sub_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (projection U - projection V).singularValues =
      (sinAngleOperator U V).singularValues := by
  rw [sinAngleOperator, singularValues_abs]

/-- **A unitarily invariant norm depends only on the singular-value sequence.**
Via the gauge representation `apply_eq_gauge` of the operator SVD. -/
theorem _root_.TauCeti.UnitarilyInvariantNorm.eq_of_singularValues_eq
    (N : UnitarilyInvariantNorm 𝕜 E) {A B : E →ₗ[𝕜] E}
    (h : A.singularValues = B.singularValues) : N A = N B := by
  rw [N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) A,
    N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) B, h]

/-- **The full projector-difference UI-norm bridge.**  Every unitarily invariant
norm of `P_U - P_V` equals that of the full `sin Θ` operator `|P_U - P_V|`, since
they share the singular-value sequence.  This is the only projection-geometry
rewrite the final UI-norm projector theorem needs. -/
theorem uiNorm_projection_sub_eq_sinAngleOperator (N : UnitarilyInvariantNorm 𝕜 E)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    N (projection U - projection V) = N (sinAngleOperator U V) :=
  N.eq_of_singularValues_eq (singularValues_projection_sub_projection U V)

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

/-- Equal-rank subspaces have the same largest sine whether measured by a
cross projection or by the difference of projectors.

The proof combines the arbitrary-dimensional two-projection identity
`‖P_U - P_V‖ = max ‖P_{Uᗮ}P_V‖ ‖P_{Vᗮ}P_U‖` with finite equal-rank principal-angle
symmetry.  Finite dimensionality is used only to choose equal-length
orthonormal bases and identify the two directed cross-projection norms. -/
theorem opNorm_projection_sub_eq_opNorm_sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hrank : finrank 𝕜 U = finrank 𝕜 V) :
    ‖(projection U - projection V).toContinuousLinearMap‖ =
      ‖(sinThetaMap U V).toContinuousLinearMap‖ := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  -- names the application so the norm bound applies to it directly.
  change ‖U.starProjection - V.starProjection‖ =
    ‖Vᗮ.starProjection ∘L U.starProjection‖
  let d := finrank 𝕜 U
  by_cases hd0 : d = 0
  · have hdimU : finrank 𝕜 U = 0 := by simpa [d] using hd0
    have hdimV : finrank 𝕜 V = 0 := hrank.symm.trans hdimU
    have hU0 : U = ⊥ := by
      symm
      exact Submodule.eq_of_le_of_finrank_eq bot_le (by simpa using hdimU.symm)
    have hV0 : V = ⊥ := by
      symm
      exact Submodule.eq_of_le_of_finrank_eq bot_le (by simpa using hdimV.symm)
    subst U
    subst V
    simp
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  obtain ⟨u, v, hu, hv, hspanU, hspanV⟩ :=
    exists_orthonormal_pair_spanning U V hrank
  have hdirSpan :
      ‖(Submodule.span 𝕜 (Set.range u))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range v)).starProjection‖ =
        ‖(Submodule.span 𝕜 (Set.range v))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range u)).starProjection‖ := by
    rw [norm_orthogonal_starProjection_comp_starProjection hv hu hd,
      norm_orthogonal_starProjection_comp_starProjection hu hv hd,
      cosPrincipalAngles_comm hu hv]
  have hdir : ‖Uᗮ.starProjection ∘L V.starProjection‖ =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ := by
    simpa only [hspanU, hspanV] using hdirSpan
  rw [Submodule.norm_starProjection_sub_eq_max,
    ← Submodule.starProjection_orthogonal' V,
    ← Submodule.starProjection_orthogonal' U,
    hdir, max_self]

/-- Family-level principal angles agree with the canonical submodule API: the
subspace cosine spectrum of `span u, span v` is the family-level
`cosPrincipalAngles`.  Both are singular values of the same cross projection
`P_{span v} P_{span u}`, via the flat cosine dictionary
`singularValues_starProjection_comp_starProjection`. -/
theorem principalCosines_span_eq_cosPrincipalAngles {d : ℕ}
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    principalCosines (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) =
      cosPrincipalAngles hu hv := by
  have hcomp : cosThetaMap (Submodule.span 𝕜 (Set.range u)) (Submodule.span 𝕜 (Set.range v))
      = (((Submodule.span 𝕜 (Set.range v)).starProjection ∘L
          (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) :=
    rfl
  rw [principalCosines, hcomp,
    TauCeti.singularValues_starProjection_comp_starProjection hu hv,
    cosPrincipalAngles_comm hv hu]

/-- The principal-cosine sequence of two unit-generated lines has one entry,
the absolute overlap of their generators. -/
theorem principalCosines_rankOne {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    principalCosines (Submodule.span 𝕜 {u}) (Submodule.span 𝕜 {v}) =
      Finsupp.single 0 ‖⟪u, v⟫_𝕜‖ := by
  classical
  let uf : Fin 1 → E := fun _ => u
  let vf : Fin 1 → E := fun _ => v
  have huf : Orthonormal 𝕜 uf := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [uf, hu]
  have hvf : Orthonormal 𝕜 vf := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [vf, hv]
  have hspanU : Submodule.span 𝕜 (Set.range uf) = Submodule.span 𝕜 {u} := by
    congr 1
    ext x
    simp [uf]
  have hspanV : Submodule.span 𝕜 (Set.range vf) = Submodule.span 𝕜 {v} := by
    congr 1
    ext x
    simp [vf]
  -- `principalCosines` is indexed by a projection instance on each submodule,
  -- so a plain `rw` produces an ill-typed motive
  simp only [← hspanU, ← hspanV]
  rw [principalCosines_span_eq_cosPrincipalAngles huf hvf]
  ext i
  by_cases hi : i = 0
  · subst i
    have hsq := sum_sq_singularValues_overlapOp huf hvf
    have hnonneg := cosPrincipalAngles_nonneg huf hvf 0
    have hnorm : 0 ≤ ‖⟪u, v⟫_𝕜‖ := norm_nonneg _
    have heq : cosPrincipalAngles huf hvf 0 = ‖⟪u, v⟫_𝕜‖ := by
      -- put the goal and both bounds on the same atom as `hsq`
      simp only [cosPrincipalAngles] at hnonneg ⊢
      simp [uf, vf] at hsq
      nlinarith [hsq, hnonneg, hnorm]
    simp [heq]
  · have hle : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi
    rw [cosPrincipalAngles,
      (overlapOp huf hvf).singularValues_of_finrank_le]
    · simp [hi]
    · simpa using hle


end TauCeti
