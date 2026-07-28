/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
import ForTauCeti.Analysis.InnerProductSpace.PartialIsometry
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The polar decomposition of a bounded operator

Every bounded operator `M : E →L[ℂ] F` between complex Hilbert spaces factors as

```
M = M.polarPartial ∘L |M|
```

with `|M| = M.modulus` positive and `M.polarPartial` a **partial isometry**: isometric on
the closure of the range of `|M|` and zero on its orthogonal complement.  Unlike
`ContinuousLinearMap.polarIsometry`, which inverts `|M|` and therefore needs `|M|` to be
invertible, this holds for *every* `M` with no side condition.

## The construction

The whole decomposition rests on one identity, `ContinuousLinearMap.norm_modulus_apply`:

```
‖ |M| x ‖ = ‖ M x ‖.
```

Read from left to right it says the assignment `|M| x ↦ M x` is well defined — if
`|M| x = |M| y` then `‖M (x - y)‖ = ‖ |M| (x - y) ‖ = 0` — and read as an equation it says
that assignment is an isometry.  So there is an isometry from `range |M|` into `F`, and
`range |M|` is dense in the closed subspace `polarInitial M`.  Extending it by continuity
(`LinearMap.extendOfNorm`) and precomposing with the orthogonal projection onto that
subspace gives `polarPartial`.

## Main definitions and results

* `ContinuousLinearMap.polarInitial`: the **initial space**, the closure of `range |M|`;
* `ContinuousLinearMap.polarPartial`: the partial isometry;
* `ContinuousLinearMap.polarPartial_comp_modulus`: the polar identity
  `M.polarPartial ∘L |M| = M`, **unconditional**;
* `ContinuousLinearMap.polarPartial_comp_adjoint_comp_polarPartial`: the algebraic
  partial-isometry identity `W W⋆ W = W`, also unconditional;
* `ContinuousLinearMap.norm_polarPartial_apply_of_mem` and
  `ContinuousLinearMap.inner_polarPartial_apply_of_mem`: `W` preserves norms, and in fact
  inner products, on the initial space;
* `ContinuousLinearMap.polarPartial_eq_zero_of_mem_orthogonal` and
  `ContinuousLinearMap.ker_polarPartial`: `W` vanishes off the initial space, and nowhere
  else;
* `ContinuousLinearMap.adjoint_comp_polarPartial`: `W⋆ W` is the orthogonal projection onto
  the initial space;
* `ContinuousLinearMap.polarInitial_orthogonal_eq_ker`: the orthogonal complement of the
  initial space is exactly `ker M`, so the initial space is `(ker M)ᗮ`;
* `ContinuousLinearMap.range_polarPartial` and
  `ContinuousLinearMap.isClosed_range_polarPartial`: the range of `W` is closed and is the
  closure of `range M` — the **final** space;
* `ContinuousLinearMap.isSelfAdjoint_polarPartial_comp_adjoint` and
  `ContinuousLinearMap.isIdempotentElem_polarPartial_comp_adjoint`: `W W⋆` is the
  orthogonal projection onto it.

## Relation to the rest of the library

`ForTauCeti/Analysis/InnerProductSpace/PolarDecomposition.lean` has the partial-isometry
factor for `LinearMap` endomorphisms in **finite dimensions**;
`ForTauCeti/Analysis/InnerProductSpace/PolarIsometry.lean` has the *invertible* case in
general, with its own `TODO` asking for exactly this module.  This is the general bounded
statement that subsumes both directions of that gap.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** in the proof.  The *motivation* is that
  `DavisKahan/Geometry/Polar/{PolarIsometryFinal,Section3Nonacute}.lean` currently obtain
  the general bounded polar decomposition from `Spectra.QuantumMechanics.Channels`, and
  AGENTS.md records that the final migration target removes Spectra from the normal build.
  No definition or proof here was read off Spectra's.
-/

@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The **initial space** of the polar decomposition of `M`: the closure of the range of
the modulus.  `M.polarPartial` is isometric on it and zero on its orthogonal complement,
and it is exactly `(ker M)ᗮ` (`polarInitial_orthogonal_eq_ker`). -/
noncomputable def polarInitial (M : E →L[ℂ] F) : Submodule ℂ E :=
  (LinearMap.range M.modulus.toLinearMap).topologicalClosure

theorem modulus_apply_mem_polarInitial (M : E →L[ℂ] F) (x : E) :
    M.modulus x ∈ M.polarInitial :=
  Submodule.le_topologicalClosure _ ⟨x, rfl⟩

instance (M : E →L[ℂ] F) : CompleteSpace M.polarInitial :=
  Submodule.topologicalClosure.completeSpace _

/-- The modulus, corestricted to the initial space, where it has dense range. -/
noncomputable def modulusCorestrict (M : E →L[ℂ] F) : E →ₗ[ℂ] M.polarInitial :=
  LinearMap.codRestrict M.polarInitial M.modulus.toLinearMap M.modulus_apply_mem_polarInitial

@[simp]
theorem coe_modulusCorestrict_apply (M : E →L[ℂ] F) (x : E) :
    (M.modulusCorestrict x : E) = M.modulus x := rfl

theorem denseRange_modulusCorestrict (M : E →L[ℂ] F) :
    DenseRange M.modulusCorestrict := by
  rw [DenseRange, Subtype.dense_iff]
  have hsub : (LinearMap.range M.modulus.toLinearMap : Set E)
      ⊆ (Subtype.val '' Set.range M.modulusCorestrict) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨M.modulusCorestrict x, ⟨x, rfl⟩, rfl⟩
  calc (M.polarInitial : Set E)
      = closure (LinearMap.range M.modulus.toLinearMap : Set E) :=
        Submodule.topologicalClosure_coe _
    _ ⊆ closure (Subtype.val '' Set.range M.modulusCorestrict) := closure_mono hsub

/-- The isometry bound that makes the extension possible: `‖M x‖ ≤ 1 * ‖ |M| x ‖`, which is
an equality, by `ContinuousLinearMap.norm_modulus_apply`. -/
theorem norm_apply_le_norm_modulusCorestrict (M : E →L[ℂ] F) (x : E) :
    ‖M.toLinearMap x‖ ≤ 1 * ‖M.modulusCorestrict x‖ := by
  rw [one_mul]
  exact le_of_eq (M.norm_modulus_apply x).symm

/-- The isometry `|M| x ↦ M x`, extended from the dense range of the modulus to the whole
initial space. -/
noncomputable def polarPartialAux (M : E →L[ℂ] F) : M.polarInitial →L[ℂ] F :=
  M.toLinearMap.extendOfNorm M.modulusCorestrict

@[simp]
theorem polarPartialAux_modulusCorestrict (M : E →L[ℂ] F) (x : E) :
    M.polarPartialAux (M.modulusCorestrict x) = M x :=
  LinearMap.extendOfNorm_eq M.denseRange_modulusCorestrict
    ⟨1, M.norm_apply_le_norm_modulusCorestrict⟩ x

/-- The **polar partial isometry** of a bounded operator.

Isometric on `M.polarInitial` and zero on its orthogonal complement, with
`M.polarPartial ∘L |M| = M` unconditionally. -/
noncomputable def polarPartial (M : E →L[ℂ] F) : E →L[ℂ] F :=
  M.polarPartialAux ∘L M.polarInitial.orthogonalProjectionOnto

theorem polarPartial_apply (M : E →L[ℂ] F) (x : E) :
    M.polarPartial x = M.polarPartialAux (M.polarInitial.orthogonalProjectionOnto x) := rfl

/-- **The polar identity.**  `M = W |M|` with `W` the polar partial isometry, for every
bounded `M` and with no invertibility hypothesis. -/
@[simp]
theorem polarPartial_apply_modulus (M : E →L[ℂ] F) (x : E) :
    M.polarPartial (M.modulus x) = M x := by
  rw [polarPartial_apply]
  have hmem : M.modulus x ∈ M.polarInitial := M.modulus_apply_mem_polarInitial x
  have hproj : M.polarInitial.orthogonalProjectionOnto (M.modulus x)
      = M.modulusCorestrict x := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hmem
  rw [hproj, polarPartialAux_modulusCorestrict]

theorem polarPartial_comp_modulus (M : E →L[ℂ] F) :
    M.polarPartial ∘L M.modulus = M := by
  ext x
  simp


/-- The modulus is self-adjoint, so it moves across the inner product. -/
theorem inner_modulus_left (M : E →L[ℂ] F) (x z : E) :
    ⟪M.modulus x, z⟫_ℂ = ⟪x, M.modulus z⟫_ℂ :=
  calc ⟪M.modulus x, z⟫_ℂ = ⟪M.modulus.adjoint x, z⟫_ℂ := by rw [M.adjoint_modulus]
    _ = ⟪x, M.modulus z⟫_ℂ := ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The extension is an isometry on the whole initial space: it is one on the dense range
of the modulus, and both sides are continuous. -/
theorem norm_polarPartialAux_apply (M : E →L[ℂ] F) (y : M.polarInitial) :
    ‖M.polarPartialAux y‖ = ‖y‖ := by
  have heq : Set.EqOn (fun z : M.polarInitial => ‖M.polarPartialAux z‖)
      (fun z : M.polarInitial => ‖z‖) (Set.range M.modulusCorestrict) := by
    rintro _ ⟨x, rfl⟩
    simp only [polarPartialAux_modulusCorestrict]
    exact (M.norm_modulus_apply x).symm
  exact congrFun (Continuous.ext_on M.denseRange_modulusCorestrict
    (by fun_prop) (by fun_prop) heq) y

/-- The polar partial isometry is an isometry on the initial space. -/
theorem norm_polarPartial_apply_of_mem (M : E →L[ℂ] F) {y : E} (hy : y ∈ M.polarInitial) :
    ‖M.polarPartial y‖ = ‖y‖ := by
  rw [polarPartial_apply]
  have hproj : M.polarInitial.orthogonalProjectionOnto y = ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.mpr hy
  rw [hproj, M.norm_polarPartialAux_apply ⟨y, hy⟩]
  rfl

/-- The polar partial isometry vanishes off the initial space. -/
theorem polarPartial_eq_zero_of_mem_orthogonal (M : E →L[ℂ] F) {y : E}
    (hy : y ∈ M.polarInitialᗮ) : M.polarPartial y = 0 := by
  rw [polarPartial_apply, Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hy, map_zero]

/-- **The initial space is the orthogonal complement of the kernel.**  Equivalently
`M.polarInitial = (ker M)ᗮ`: the partial isometry is supported exactly where `M` is. -/
theorem polarInitial_orthogonal_eq_ker (M : E →L[ℂ] F) :
    M.polarInitialᗮ = LinearMap.ker M.toLinearMap := by
  ext y
  constructor
  · intro hy
    have hall : ∀ x : E, ⟪x, M.modulus y⟫_ℂ = 0 := by
      intro x
      have h := hy (M.modulus x) (M.modulus_apply_mem_polarInitial x)
      rwa [M.inner_modulus_left] at h
    have hzero : M.modulus y = 0 := inner_self_eq_zero.mp (hall _)
    exact (M.modulus_apply_eq_zero_iff y).mp hzero
  · intro hy
    have hMy : M y = 0 := hy
    have hmod : M.modulus y = 0 := (M.modulus_apply_eq_zero_iff y).mpr hMy
    have hle : M.polarInitial ≤ (ℂ ∙ y)ᗮ := by
      refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
      rintro _ ⟨x, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      simp only [ContinuousLinearMap.coe_coe]
      rw [← M.inner_modulus_left, hmod, inner_zero_left]
    intro u hu
    have := hle hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at this
    exact this

/-- The kernel of the polar partial isometry is exactly the orthogonal complement of the
initial space — it kills nothing else. -/
theorem ker_polarPartial (M : E →L[ℂ] F) :
    LinearMap.ker M.polarPartial.toLinearMap = M.polarInitialᗮ := by
  apply le_antisymm
  · intro y hy
    have hWy : M.polarPartial y = 0 := hy
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) y
    have hWq : M.polarPartial q = 0 := M.polarPartial_eq_zero_of_mem_orthogonal hq
    have hWp : M.polarPartial p = 0 := by
      have := hWy
      rw [map_add, hWq, add_zero] at this
      exact this
    have hp0 : p = 0 := by
      have := M.norm_polarPartial_apply_of_mem hp
      rw [hWp, norm_zero] at this
      exact norm_eq_zero.mp this.symm
    rw [hp0, zero_add]
    exact hq
  · intro y hy
    exact M.polarPartial_eq_zero_of_mem_orthogonal hy

/-- The initial space is the orthogonal complement of the kernel of the partial isometry,
which is the shape the abstract partial-isometry API expects. -/
theorem orthogonal_ker_polarPartial (M : E →L[ℂ] F) :
    (LinearMap.ker M.polarPartial.toLinearMap)ᗮ = M.polarInitial := by
  rw [M.ker_polarPartial, Submodule.orthogonal_orthogonal]

/-- On the initial space the partial isometry preserves inner products, not just norms. -/
theorem inner_polarPartial_apply_of_mem (M : E →L[ℂ] F) {p q : E}
    (hp : p ∈ M.polarInitial) (hq : q ∈ M.polarInitial) :
    ⟪M.polarPartial p, M.polarPartial q⟫_ℂ = ⟪p, q⟫_ℂ := by
  have hnorm : ∀ w : M.polarInitial,
      ‖(M.polarPartial.toLinearMap ∘ₗ M.polarInitial.subtype) w‖ = ‖w‖ := by
    intro w
    simpa using M.norm_polarPartial_apply_of_mem w.2
  have hmap := (LinearMap.norm_map_iff_inner_map_map
    (M.polarPartial.toLinearMap ∘ₗ M.polarInitial.subtype)).mp hnorm
  simpa using hmap ⟨p, hp⟩ ⟨q, hq⟩

/-- `W⋆ W` fixes the initial space pointwise. -/
theorem adjoint_polarPartial_polarPartial_apply_of_mem (M : E →L[ℂ] F) {p : E}
    (hp : p ∈ M.polarInitial) :
    M.polarPartial.adjoint (M.polarPartial p) = p := by
  have hall : ∀ z : E, ⟪M.polarPartial.adjoint (M.polarPartial p) - p, z⟫_ℂ = 0 := by
    intro z
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ :=
      Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) z
    have h₁ : ⟪M.polarPartial.adjoint (M.polarPartial p) - p, z₁⟫_ℂ = 0 := by
      rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
        M.inner_polarPartial_apply_of_mem hp hz₁, sub_self]
    have h₂ : ⟪M.polarPartial.adjoint (M.polarPartial p) - p, z₂⟫_ℂ = 0 := by
      rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
        M.polarPartial_eq_zero_of_mem_orthogonal hz₂, inner_zero_right,
        (Submodule.mem_orthogonal _ _).mp hz₂ p hp, sub_zero]
    rw [inner_add_right, h₁, h₂, add_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (hall _))

/-- `W⋆ W` is the orthogonal projection onto the initial space. -/
theorem adjoint_comp_polarPartial (M : E →L[ℂ] F) :
    M.polarPartial.adjoint ∘L M.polarPartial = M.polarInitial.starProjection := by
  ext x
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) x
  have hqz : M.polarInitial.starProjection q = 0 := by
    have hmem : q ∈ (M.polarInitial.starProjection).ker := by
      rw [Submodule.ker_starProjection]; exact hq
    exact hmem
  simp only [ContinuousLinearMap.comp_apply, map_add,
    M.polarPartial_eq_zero_of_mem_orthogonal hq, map_zero, add_zero,
    M.adjoint_polarPartial_polarPartial_apply_of_mem hp, hqz,
    Submodule.starProjection_eq_self_iff.mpr hp]

/-- The partial isometry is unchanged by first projecting onto its initial space. -/
theorem polarPartial_comp_starProjection (M : E →L[ℂ] F) :
    M.polarPartial ∘L M.polarInitial.starProjection = M.polarPartial := by
  ext x
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := M.polarInitial) x
  have hqz : M.polarInitial.starProjection q = 0 := by
    have hmem : q ∈ (M.polarInitial.starProjection).ker := by
      rw [Submodule.ker_starProjection]; exact hq
    exact hmem
  simp only [ContinuousLinearMap.comp_apply, map_add, hqz, add_zero,
    Submodule.starProjection_eq_self_iff.mpr hp,
    M.polarPartial_eq_zero_of_mem_orthogonal hq, map_zero]

/-- **The partial-isometry identity `W W⋆ W = W`**, for every bounded operator and with no
invertibility or finite-dimensionality hypothesis.  This is the algebraic form of
"`W` is a partial isometry"; the analytic form is
`norm_polarPartial_apply_of_mem` together with
`polarPartial_eq_zero_of_mem_orthogonal`. -/
theorem polarPartial_comp_adjoint_comp_polarPartial (M : E →L[ℂ] F) :
    M.polarPartial ∘L M.polarPartial.adjoint ∘L M.polarPartial = M.polarPartial := by
  rw [M.adjoint_comp_polarPartial, M.polarPartial_comp_starProjection]

/-- The adjoint form of the partial-isometry identity, `W⋆ W W⋆ = W⋆`. -/
theorem adjoint_comp_polarPartial_comp_adjoint (M : E →L[ℂ] F) :
    M.polarPartial.adjoint ∘L M.polarPartial ∘L M.polarPartial.adjoint =
      M.polarPartial.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint M.polarPartial_comp_adjoint_comp_polarPartial
  simpa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc] using h

/-- `W W⋆` is an orthogonal projection: idempotent and self-adjoint.  It is the projection
onto the *final* space of the polar decomposition. -/
theorem isSelfAdjoint_polarPartial_comp_adjoint (M : E →L[ℂ] F) :
    IsSelfAdjoint (M.polarPartial ∘L M.polarPartial.adjoint) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem isIdempotentElem_polarPartial_comp_adjoint (M : E →L[ℂ] F) :
    IsIdempotentElem (M.polarPartial ∘L M.polarPartial.adjoint) := by
  have h := M.adjoint_comp_polarPartial_comp_adjoint
  change (M.polarPartial ∘L M.polarPartial.adjoint) ∘L
    (M.polarPartial ∘L M.polarPartial.adjoint) = _
  calc (M.polarPartial ∘L M.polarPartial.adjoint) ∘L
        (M.polarPartial ∘L M.polarPartial.adjoint)
      = M.polarPartial ∘L (M.polarPartial.adjoint ∘L M.polarPartial ∘L
          M.polarPartial.adjoint) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = M.polarPartial ∘L M.polarPartial.adjoint := by rw [h]

/-- The partial isometry, bundled as a `LinearIsometry` on the initial space. -/
noncomputable def polarLinearIsometryAux (M : E →L[ℂ] F) : M.polarInitial →ₗᵢ[ℂ] F where
  toLinearMap := M.polarPartialAux.toLinearMap
  norm_map' := M.norm_polarPartialAux_apply

/-- Every vector in the range of the partial isometry already comes from the initial
space, because the projection is the identity there. -/
theorem range_polarPartial_eq_range_aux (M : E →L[ℂ] F) :
    Set.range M.polarPartial = Set.range M.polarPartialAux := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨M.polarInitial.orthogonalProjectionOnto x, rfl⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨(y : E), ?_⟩
    rw [polarPartial_apply]
    congr 1
    apply Subtype.ext
    simp

/-- **The range of the partial isometry is closed.**  It is the isometric image of the
initial space, and that space is complete. -/
theorem isClosed_range_polarPartial (M : E →L[ℂ] F) :
    IsClosed (Set.range M.polarPartial) := by
  rw [M.range_polarPartial_eq_range_aux]
  have hrange : Set.range M.polarPartialAux = Set.range M.polarLinearIsometryAux := rfl
  rw [hrange, ← Set.image_univ]
  exact ((LinearIsometry.isComplete_image_iff M.polarLinearIsometryAux).mpr
    complete_univ).isClosed

/-- **The range of the partial isometry is the closure of the range of `M`** — the *final*
space of the polar decomposition. -/
theorem range_polarPartial (M : E →L[ℂ] F) :
    LinearMap.range M.polarPartial.toLinearMap =
      (LinearMap.range M.toLinearMap).topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    have hclosed : IsClosed
        {w : M.polarInitial |
          M.polarPartialAux w ∈ (LinearMap.range M.toLinearMap).topologicalClosure} :=
      (Submodule.isClosed_topologicalClosure _).preimage M.polarPartialAux.continuous
    have hgen : ∀ x : E, M.polarPartialAux (M.modulusCorestrict x)
        ∈ (LinearMap.range M.toLinearMap).topologicalClosure := by
      intro x
      rw [polarPartialAux_modulusCorestrict]
      exact Submodule.le_topologicalClosure _ ⟨x, rfl⟩
    change M.polarPartial y ∈ _
    rw [polarPartial_apply]
    exact M.denseRange_modulusCorestrict.induction_on
      (p := fun w => M.polarPartialAux w ∈
        (LinearMap.range M.toLinearMap).topologicalClosure)
      (M.polarInitial.orthogonalProjectionOnto y) hclosed hgen
  · refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨M.modulus x, M.polarPartial_apply_modulus x⟩
    · rw [LinearMap.coe_range]
      exact M.isClosed_range_polarPartial

end ContinuousLinearMap
