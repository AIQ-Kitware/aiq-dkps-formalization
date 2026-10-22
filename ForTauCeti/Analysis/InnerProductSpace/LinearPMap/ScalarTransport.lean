/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import ForTauCeti.Analysis.RCLike.ScalarTransport

/-!
# Reducing subspaces and bounded perturbations survive a change of scalar field

`TauCeti.ScalarTransport e E` rewrites a Hilbert space over `𝕜` as one over an
isomorphic `RCLike` field `𝕂`, changing neither the vectors nor the norm.  This
module carries the two structural notions a Davis--Kahan statement is built from
across that rewriting: a subspace reduces the transported operator exactly when
it reduces the original, and the transport commutes with adding a bounded
operator.

Together with `TauCeti.ScalarTransport.approximationNumber_clm` these are what
let a theorem proved at `ℝ` and at `ℂ` be read at an arbitrary `RCLike` field.

## Main results

* `TauCeti.ScalarTransport.isReducing_pmap_iff` transports Tau Ceti's canonical
  reducing-subspace predicate.
* `TauCeti.ScalarTransport.reducesSubspace_pmap_iff`.
* `TauCeti.ScalarTransport.pmap_addBounded`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none**.
-/

public section

namespace TauCeti
namespace ScalarTransport

universe u w v

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Membership in the transported domain is membership in the domain. -/
theorem mem_pmap_domain_iff {A : E →ₗ.[𝕜] E} (x : ScalarTransport e E) :
    x ∈ (pmap (e := e) A).domain ↔ out (e := e) x ∈ A.domain := by
  rw [pmap_domain, mem_submodule]

/-- The complementary projection of a transported subspace, pointwise. -/
theorem starProjection_orthogonal_of (S : Submodule 𝕜 E) [S.HasOrthogonalProjection]
    (x : E) :
    (submodule (e := e) S)ᗮ.starProjection (of (e := e) x) =
      of (e := e) (Sᗮ.starProjection x) := by
  rw [Submodule.starProjection_orthogonal_apply,
    Submodule.starProjection_orthogonal_apply, starProjection_of]
  rfl

/-- A subspace of the transported space is invariant under the transported
operator exactly when it was invariant. -/
theorem invariantSubspace_pmap_iff {A : E →ₗ.[𝕜] E} (S : Submodule 𝕜 E) :
    (pmap (e := e) A).IsInvariant (submodule (e := e) S) ↔ A.IsInvariant S := by
  rw [_root_.LinearPMap.isInvariant_iff, _root_.LinearPMap.isInvariant_iff]
  constructor
  · intro h x hx
    have hd : (of (e := e) (x : E)) ∈ (pmap (e := e) A).domain :=
      (mem_pmap_domain_iff (e := e) (A := A) _).mpr x.2
    exact (mem_submodule (e := e)).mp
      (h ⟨of (e := e) (x : E), hd⟩ ((mem_submodule (e := e)).mpr hx))
  · intro h x hx
    have hd : out (e := e) (x : ScalarTransport e E) ∈ A.domain :=
      (mem_pmap_domain_iff (e := e) (A := A) _).mp x.2
    exact (mem_submodule (e := e)).mpr
      (h ⟨out (e := e) (x : ScalarTransport e E), hd⟩ ((mem_submodule (e := e)).mp hx))

/-- **A subspace reduces the transported operator exactly when it reduces the
original.**  The canonical domain-preservation and invariance conditions are
unchanged by scalar transport. -/
theorem isReducing_pmap_iff {A : E →ₗ.[𝕜] E} (S : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] :
    _root_.LinearPMap.IsReducing (pmap (e := e) A) (submodule (e := e) S) ↔
      _root_.LinearPMap.IsReducing A S := by
  have hinvS := invariantSubspace_pmap_iff (e := e) (A := A) S
  have hinvSc := invariantSubspace_pmap_iff (e := e) (A := A) Sᗮ
  have hortho : (pmap (e := e) A).IsInvariant
        (submodule (e := e) Sᗮ) ↔
      (pmap (e := e) A).IsInvariant (submodule (e := e) S)ᗮ := by
    rw [submodule_orthogonal]
  constructor
  · intro h
    refine ⟨?_, (hinvS.mp h.isInvariant),
      (hinvSc.mp (hortho.mpr h.isInvariant_orthogonal))⟩
    intro x hx
    have hd : (of (e := e) x) ∈ (pmap (e := e) A).domain :=
      (mem_pmap_domain_iff (e := e) (A := A) _).mpr hx
    have hx := h.starProjection_mem_domain hd
    rw [starProjection_of] at hx
    exact (mem_pmap_domain_iff (e := e) (A := A) _).mp hx
  · intro h
    refine ⟨?_, (hinvS.mpr h.isInvariant),
      (hortho.mp (hinvSc.mpr h.isInvariant_orthogonal))⟩
    intro x hx
    have hd : out (e := e) (x : ScalarTransport e E) ∈ A.domain :=
      (mem_pmap_domain_iff (e := e) (A := A) _).mp hx
    have hx := h.starProjection_mem_domain hd
    refine (mem_pmap_domain_iff (e := e) (A := A) _).mpr ?_
    rw [show (submodule (e := e) S).starProjection (x : ScalarTransport e E)
        = of (e := e) (S.starProjection (out (e := e) (x : ScalarTransport e E)))
      from starProjection_of (e := e) S _]
    exact hx

/-- Compatibility theorem for consumers that still use the donor reduction predicate. -/
theorem reducesSubspace_pmap_iff {A : E →ₗ.[𝕜] E} (S : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] :
    TauCeti.LinearPMap.ReducesSubspace (pmap (e := e) A) (submodule (e := e) S) ↔
      TauCeti.LinearPMap.ReducesSubspace A S := by
  rw [TauCeti.LinearPMap.reducesSubspace_iff_isReducing,
    TauCeti.LinearPMap.reducesSubspace_iff_isReducing]
  exact isReducing_pmap_iff (e := e) S


/-- The transport commutes with adding a bounded operator. -/
theorem pmap_addBounded (A : E →ₗ.[𝕜] E) (T : E →L[𝕜] E) :
    pmap (e := e) (LinearPMap.addBounded A T) =
      LinearPMap.addBounded (pmap (e := e) A) (clm (e := e) T) := by
  refine LinearPMap.ext rfl ?_
  intro x hf hg
  simp only [pmap_apply, LinearPMap.addBounded_apply]
  rfl

end ScalarTransport
end TauCeti
