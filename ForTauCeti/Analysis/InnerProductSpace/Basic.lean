/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T01.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
addition to `Mathlib/Analysis/InnerProductSpace/Basic.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).  Placement history: originally
in the Gram-matrix staging file, then moved to `Orthonormal.lean` to sit by the
`Finsupp`/inner-product machinery; following @wwylele's review (PR #40567) it
moved here to `Basic.lean` — the lemma involves no `Orthonormal`, and `Basic`
already hosts `Finsupp.sum_inner` / `Finsupp.inner_sum` (its dependencies) and
`open`s `Finsupp` + `ComplexConjugate`, so no new import is needed.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint


/-! # Inner products of linear combinations

A general identity expanding the inner product of two finite linear combinations of a
vector family over the family's pairwise inner products `⟪v i, v j⟫`.  It involves no
orthonormality, no Gram matrix, and no rigidity hypothesis; it is the reusable algebraic
core behind the Gram-rigidity development in
`Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`, and belongs next to
`Finsupp.sum_inner` / `Finsupp.inner_sum`.

## Main results

* `TauCeti.inner_linearCombination_linearCombination`: expands
  `⟪Σ aᵢ • v i, Σ bⱼ • v j⟫` as `Σᵢ Σⱼ conj aᵢ * bⱼ * ⟪v i, v j⟫`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.Basic`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `6d8c37c`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/--
The inner product of two finite linear combinations `Σ aᵢ • v i` and `Σ bⱼ • v j`
of a vector family `v`, expanded over the family's Gram data
`⟪v i, v j⟫`:
`⟪Σ aᵢ • vᵢ, Σ bⱼ • vⱼ⟫ = Σᵢ Σⱼ conj aᵢ * bⱼ * ⟪vᵢ, vⱼ⟫`.
-/
theorem inner_linearCombination_linearCombination (v : ι → E) (a b : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 v a, Finsupp.linearCombination 𝕜 v b⟫_𝕜
      = a.sum fun i s => b.sum fun j t => starRingEnd 𝕜 s * t * ⟪v i, v j⟫_𝕜 := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]

section CoordinateFamily

variable {d : ℕ}

/-- The linear map `EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E` sending the `j`-th standard
basis vector to `v j` (extended linearly): `x ↦ ∑ j, x j • v j`. -/
noncomputable def familyMap (v : Fin d → E) : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E :=
  (Fintype.linearCombination 𝕜 v).comp (WithLp.linearEquiv 2 𝕜 (Fin d → 𝕜)).toLinearMap

/-- The family map, unfolded to its expansion in the family. -/
@[simp] theorem familyMap_apply (v : Fin d → E) (x : EuclideanSpace 𝕜 (Fin d)) :
    familyMap v x = ∑ i, x i • v i := by
  rw [familyMap, LinearMap.comp_apply, Fintype.linearCombination_apply]
  rfl

/-- The coordinate map of an orthonormal family preserves inner products. -/
theorem familyMap_inner_map_map {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (x y : EuclideanSpace 𝕜 (Fin d)) :
    ⟪familyMap v x, familyMap v y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  rw [familyMap_apply, familyMap_apply, sum_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hv i i, if_pos rfl, mul_one,
      RCLike.inner_apply]
    ring
  · intro j _ hji
    rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hv i j, if_neg (Ne.symm hji),
      mul_zero, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The bundled coordinate isometry `EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E` of an
orthonormal family `v`, sending `eⱼ ↦ vⱼ`. -/
noncomputable def familyIsometry {v : Fin d → E} (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E :=
  (familyMap v).isometryOfInner (familyMap_inner_map_map hv)

/-- The bundled isometry acts as the family map. -/
@[simp] theorem familyIsometry_apply {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (x : EuclideanSpace 𝕜 (Fin d)) : familyIsometry hv x = ∑ i, x i • v i := by
  rw [familyIsometry, LinearMap.coe_isometryOfInner, familyMap_apply]

/-- It sends the `k`-th standard basis vector to `v k`. -/
@[simp] theorem familyIsometry_single {v : Fin d → E} (hv : Orthonormal 𝕜 v) (k : Fin d) :
    familyIsometry hv (EuclideanSpace.single k 1) = v k := by
  rw [familyIsometry_apply]
  rw [Finset.sum_eq_single k]
  · rw [PiLp.single_apply, if_pos rfl, one_smul]
  · intro i _ hik; rw [PiLp.single_apply, if_neg hik, zero_smul]
  · intro hk; exact absurd (Finset.mem_univ k) hk

end CoordinateFamily

end TauCeti

section RootNamespace

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

/-- A subspace admitting an orthogonal projection is complete when the ambient
space is complete. -/
theorem isComplete_coe_of_hasOrthogonalProjection [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsComplete (U : Set E) := by
  have hclosed : IsClosed ((Uᗮ)ᗮ : Set E) := Uᗮ.isClosed_orthogonal
  simpa using hclosed.isComplete

end Submodule

namespace ContinuousLinearMap

/-- Restricting a symmetric operator to an invariant subspace preserves
symmetry. -/
theorem IsSymmetric.restrict_of_invariant {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U) :
    (A.restrict hU).IsSymmetric := by
  intro x y
  -- states the goal as the inner-product identity the structure lemma expects.
  change ⟪A (x : E), (y : E)⟫_𝕜 = ⟪(x : E), A (y : E)⟫_𝕜
  exact hA x y

end ContinuousLinearMap

end RootNamespace
