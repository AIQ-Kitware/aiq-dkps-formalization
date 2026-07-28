/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
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
* `ContinuousLinearMap.norm_polarPartial_apply_of_mem`: isometry on the initial space;
* `ContinuousLinearMap.polarPartial_eq_zero_of_mem_orthogonal`: vanishing off it;
* `ContinuousLinearMap.polarInitial_orthogonal_eq_ker`: the orthogonal complement of the
  initial space is exactly `ker M`, so the initial space is `(ker M)ᗮ`.

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

end ContinuousLinearMap
