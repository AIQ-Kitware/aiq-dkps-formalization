/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Partial-map unitary conjugation during consumer migration

The declarations in this module have accepted counterparts in Tau Ceti's
`LinearPMap.Constructions`. They remain temporarily while downstream consumers
switch to Tau Ceti's root `LinearPMap` API; this module is not a distinct
mathematical foundation to maintain.

## Provenance

* **Original repository:** Davis--Kahan/DKPS formalization (Kitware, Inc.).
* **Original implementation:** the unitary-conjugation definitions and laws
  were introduced in this repository. Tau Ceti later accepted equivalent
  declarations in `TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions`.
* **Current extraction class:** duplicate awaiting consumer migration; remove
  this module when its remaining imports have moved to the accepted upstream
  module.
-/

public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

section UnitaryConj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']

/-- **Conjugation of a partial map by a unitary**, `A ↦ U A U⁻¹`, with domain
`U '' dom A` and action `y ↦ U (A (U⁻¹ y))`. -/
-- `@[expose]` here is deliberate and minimal: the `_apply` lemma below cannot be
-- *stated* without `.domain` reducing, since it indexes its argument by this map's
-- domain and applies the underlying map to it. That is the `api-design` rubric's own
-- carve-out — a consumer that must unfold — not the blanket exposure it rejects.
@[expose]
noncomputable def unitaryConj (U : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) : H' →ₗ.[𝕜] H' where
  domain := A.domain.comap (U.symm.toLinearEquiv : H' →ₗ[𝕜] H)
  toFun :=
    { toFun := fun x => U (A ⟨U.symm (x : H'), x.2⟩)
      map_add' := fun x y => by
        have hsub : (⟨U.symm ((x : H') + (y : H')), (x + y).2⟩ : A.domain)
            = ⟨U.symm (x : H'), x.2⟩ + ⟨U.symm (y : H'), y.2⟩ :=
          Subtype.ext (by simp)
        simp only [Submodule.coe_add]
        rw [hsub, A.map_add, map_add]
      map_smul' := fun c x => by
        have hsub : (⟨U.symm (c • (x : H')), (c • x).2⟩ : A.domain)
            = c • ⟨U.symm (x : H'), x.2⟩ :=
          Subtype.ext (by
            -- states the goal with the definition unfolded, in the shape the next step needs;
            -- there is no `_apply` lemma to rewrite with here.
            change U.symm (c • (x : H')) = c • U.symm (x : H')
            exact map_smul U.symm c (x : H'))
        simp only [Submodule.coe_smul]
        rw [hsub, A.map_smul, map_smul]
        rfl }

/-- The domain of the conjugated operator is the image of the original domain:
`x` lies in it exactly when `U.symm x` lies in `A.domain`.  Stated as an `Iff`
on the preimage because that is the form the definition produces and the one
`rw` can use in either direction. -/
theorem mem_unitaryConj_domain_iff {U : H ≃ₗᵢ[𝕜] H'} {A : H →ₗ.[𝕜] H} {x : H'} :
    x ∈ (unitaryConj U A).domain ↔ U.symm x ∈ A.domain := Iff.rfl

/-- `U A U⁻¹` acting on a vector of the conjugated domain: pull back by `U.symm`,
apply `A`, push forward by `U`. -/
@[simp]
theorem unitaryConj_apply (U : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H)
    (x : (unitaryConj U A).domain) :
    unitaryConj U A x = U (A ⟨U.symm (x : H'), x.2⟩) := (rfl)
/-- `U` carries `A.domain` into the conjugated domain.  This is the membership
witness needed to state `unitaryConj_apply_map`, which is the form of the
conjugation law that is usable from the *original* domain. -/
theorem map_mem_unitaryConj_domain (U : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) (y : A.domain) :
    U (y : H) ∈ (unitaryConj U A).domain := by
  rw [mem_unitaryConj_domain_iff, U.symm_apply_apply]
  exact y.2

/-- **The intertwining law**, in the form consumers want: conjugation composed
with `U` is `U` composed with `A`, indexed by the *original* domain rather than
the conjugated one. -/
theorem unitaryConj_apply_map (U : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) (y : A.domain) :
    unitaryConj U A ⟨U (y : H), map_mem_unitaryConj_domain U A y⟩ = U (A y) := by
  rw [unitaryConj_apply]
  congr 1
  exact congrArg A (Subtype.ext (U.symm_apply_apply (y : H)))

section UnitaryConjSelfAdjoint

variable [CompleteSpace H] [CompleteSpace H']

/-- **Self-adjointness transfers through unitary conjugation.**

Spectra proves this through von Neumann's deficiency criterion — symmetry,
density and both `(· ± i)` surjectivities transported across `U`.  It is cheaper
than that: `U` is an isometric equivalence, so `⟪U a, U b⟫ = ⟪a, b⟫` turns the
adjoint-domain condition for `U A U⁻¹` at `y` into the one for `A` at `U⁻¹ y`,
and symmetry closes it. -/
theorem isSelfAdjoint_unitaryConj {U : H ≃ₗᵢ[𝕜] H'} {A : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (unitaryConj U A) := by
  set B := unitaryConj U A with hB
  have hdenseA : Dense (A.domain : Set H) := hA.dense_domain
  have hsymA : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hdenseA
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  -- `U` is a surjective isometry, so it carries a dense set to a dense set
  have hdenseB : Dense (B.domain : Set H') := by
    have himg : (U : H ≃ₗᵢ[𝕜] H') '' (A.domain : Set H) ⊆ (B.domain : Set H') := by
      rintro _ ⟨w, hw, rfl⟩
      exact map_mem_unitaryConj_domain U A ⟨w, hw⟩
    exact Dense.mono himg ((U.toHomeomorph.isDenseEmbedding).dense_image.mpr hdenseA)
  -- symmetry of `B`
  have hsymB : B.IsFormalAdjoint B := by
    intro x y
    have hx : U.symm (x : H') ∈ A.domain := x.2
    have hy : U.symm (y : H') ∈ A.domain := y.2
    calc ⟪B x, (y : H')⟫_𝕜
        = ⟪U (A ⟨U.symm (x : H'), hx⟩), U (U.symm (y : H'))⟫_𝕜 := by
          rw [U.apply_symm_apply]; rfl
      _ = ⟪A ⟨U.symm (x : H'), hx⟩, U.symm (y : H')⟫_𝕜 := U.inner_map_map _ _
      _ = ⟪U.symm (x : H'), A ⟨U.symm (y : H'), hy⟩⟫_𝕜 :=
          hsymA ⟨U.symm (x : H'), hx⟩ ⟨U.symm (y : H'), hy⟩
      _ = ⟪U (U.symm (x : H')), U (A ⟨U.symm (y : H'), hy⟩)⟫_𝕜 :=
          (U.inner_map_map _ _).symm
      _ = ⟪(x : H'), B y⟫_𝕜 := by rw [U.apply_symm_apply]; rfl
  -- the adjoint domain of `B` sits inside `B`'s domain
  have hsub : ∀ y : H', y ∈ (_root_.LinearPMap.adjoint B).domain → y ∈ B.domain := by
    intro y hy
    have hform := _root_.LinearPMap.adjoint_isFormalAdjoint (T := B) hdenseB ⟨y, hy⟩
    rw [mem_unitaryConj_domain_iff]
    have hwit : ∀ u : A.domain,
        ⟪U.symm ((_root_.LinearPMap.adjoint B) ⟨y, hy⟩), (u : H)⟫_𝕜 = ⟪U.symm y, A u⟫_𝕜 := by
      intro u
      have h := hform ⟨U (u : H), map_mem_unitaryConj_domain U A u⟩
      rw [unitaryConj_apply_map] at h
      calc ⟪U.symm ((_root_.LinearPMap.adjoint B) ⟨y, hy⟩), (u : H)⟫_𝕜
          = ⟪(_root_.LinearPMap.adjoint B) ⟨y, hy⟩, U (u : H)⟫_𝕜 := by
            rw [← U.inner_map_map (U.symm _) (u : H), U.apply_symm_apply]
        _ = ⟪y, U (A u)⟫_𝕜 := h
        _ = ⟪U.symm y, A u⟫_𝕜 := by
            rw [← U.inner_map_map (U.symm y) (A u), U.apply_symm_apply]
    have hmem : U.symm y ∈ (_root_.LinearPMap.adjoint A).domain :=
      _root_.LinearPMap.mem_adjoint_domain_of_exists _
        ⟨U.symm ((_root_.LinearPMap.adjoint B) ⟨y, hy⟩), hwit⟩
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at hmem
  have hle : B ≤ _root_.LinearPMap.adjoint B :=
    _root_.LinearPMap.IsFormalAdjoint.le_adjoint (T := B) (S := B) hdenseB hsymB
  have hdomeq : B.domain = (_root_.LinearPMap.adjoint B).domain :=
    le_antisymm hle.1 hsub
  rw [_root_.LinearPMap.isSelfAdjoint_def]
  exact (_root_.LinearPMap.eq_of_le_of_domain_eq hle hdomeq).symm

end UnitaryConjSelfAdjoint

end UnitaryConj

end LinearPMap
end TauCeti
