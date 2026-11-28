/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Sylvester
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks

/-!
# Unitary transport of the domain-aware spectral vocabulary

`(A.conj U.toLinearEquiv) = U A U⁻¹` already exists for partial linear maps, together with
its domain description, its intertwining law and the transfer of
self-adjointness.  What was missing is that the rest of the unbounded spectral
vocabulary travels with it.

This module proves that a unitary equivalence transports

* the resolvent set and the real spectrum as equalities of sets;
* the two operator-form semibounds, in both directions;
* the reducing-subspace property, onto the image subspace;
* and the reducing restriction itself, as an *equality* of partial maps
  `A|U` conjugated by the restricted unitary and `(U A U⁻¹)|(U '' U)`.

The last one is the reason the module exists.  A reducing restriction is built
from a domain, a linear map and an invariance proof, so two restrictions of
visibly different operators are not interchangeable by `congr`; the equality has
to be proved once, and then every spectral hypothesis about the restriction can
be moved across the unitary by rewriting.

Everything is stated over an arbitrary `RCLike` scalar field and for a unitary
between two *different* Hilbert spaces, because that is what a restricted
unitary `U ≃ₗᵢ U.map W` is.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new reusable mathematics**.  Written for the ambient
  double-angle sine theorem, where the perturbed operator is the reflection
  conjugate of the unperturbed one and every spectral hypothesis has to cross
  that reflection.
* Spectra influence: none.
-/

public section

open _root_.LinearPMap (
  resolvent)

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H H' : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']

/-! ### Resolvent set and real spectrum -/

/-- The bounded inverse of the shift conjugates with the operator. -/
private theorem mem_resolventSet_conj_of_mem
    (W : H ≃ₗᵢ[𝕜] H') {A : H →ₗ.[𝕜] H} {z : 𝕜}
    (hz : z ∈ A.resolventSet) : z ∈ (A.conj W.toLinearEquiv).resolventSet := by
  obtain ⟨R, hR⟩ := _root_.LinearPMap.mem_resolventSet_iff.mp hz
  let S := W.toLinearIsometry.toContinuousLinearMap ∘L R ∘L
    W.symm.toLinearIsometry.toContinuousLinearMap
  have hdom (y : H') : S y ∈ (A.conj W.toLinearEquiv).domain := by
    apply _root_.LinearPMap.mem_conj_domain_iff.mpr
    change W.symm (W (R (W.symm y))) ∈ A.domain
    rw [W.symm_apply_apply]
    exact hR.mem_domain (W.symm y)
  refine (_root_.LinearPMap.mem_resolventSet_iff).mpr ⟨S, hdom, ?_, ?_⟩
  · intro y
    rw [_root_.LinearPMap.conj_apply]
    change z • W (R (W.symm y)) -
      W (A ⟨W.symm (W (R (W.symm y))),
        _root_.LinearPMap.mem_conj_domain_iff.mp (hdom y)⟩) = y
    have hx : (⟨W.symm (W (R (W.symm y))),
        _root_.LinearPMap.mem_conj_domain_iff.mp (hdom y)⟩ : A.domain) =
        ⟨R (W.symm y), hR.mem_domain (W.symm y)⟩ := Subtype.ext (W.symm_apply_apply _)
    rw [hx, ← map_smul, ← map_sub, hR.smul_sub_apply, W.apply_symm_apply]
  · intro x
    rw [_root_.LinearPMap.conj_apply]
    change W (R (W.symm (z • (x : H') - W (A ⟨W.symm (x : H'),
      _root_.LinearPMap.mem_conj_domain_iff.mp x.property⟩)))) = x
    rw [map_sub, map_smul, W.symm_apply_apply]
    let v : A.domain := ⟨W.symm (x : H'), _root_.LinearPMap.mem_conj_domain_iff.mp x.property⟩
    change W (R (z • (v : H) - A v)) = x
    exact (congrArg W (hR.apply_smul_sub v)).trans (W.apply_symm_apply _)

/-- Unitary conjugation preserves the resolvent set at every scalar. -/
theorem resolventSet_unitaryConj (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) :
    (A.conj W.toLinearEquiv).resolventSet = A.resolventSet := by
  ext z
  refine ⟨fun hz => ?_, mem_resolventSet_conj_of_mem W⟩
  have h := mem_resolventSet_conj_of_mem W.symm hz
  rwa [LinearIsometryEquiv.toLinearEquiv_symm, _root_.LinearPMap.conj_conj_symm] at h

/-- The real spectrum is invariant under unitary conjugation. -/
theorem realSpectrum_unitaryConj (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) :
    _root_.LinearPMap.realSpectrum (A.conj W.toLinearEquiv) =
      _root_.LinearPMap.realSpectrum A := by
  ext r
  simp only [_root_.LinearPMap.mem_realSpectrum_iff, _root_.LinearPMap.mem_spectrum_iff,
    resolventSet_unitaryConj]

/-! ### Operator-form semibounds -/

/-- A lower form bound transports to the unitary conjugate. -/
theorem semiboundedBelow_unitaryConj_of
    (W : H ≃ₗᵢ[𝕜] H') {A : H →ₗ.[𝕜] H} {c : ℝ}
    (h : SemiboundedBelow A c) : SemiboundedBelow (A.conj W.toLinearEquiv) c := by
  rw [semiboundedBelow_iff] at h ⊢
  intro x
  have hx : W.symm (x : H') ∈ A.domain :=
    (_root_.LinearPMap.mem_conj_domain_iff).mp x.property
  have hnorm : ‖(x : H')‖ = ‖W.symm (x : H')‖ := (W.symm.norm_map _).symm
  have hinner : ⟪(A.conj W.toLinearEquiv) x, (x : H')⟫_𝕜 =
      ⟪A ⟨W.symm (x : H'), hx⟩, W.symm (x : H')⟫_𝕜 := by
    rw [_root_.LinearPMap.conj_apply]
    dsimp only [LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.coe_symm_toLinearEquiv]
    rw [← W.symm.inner_map_map (W (A ⟨W.symm (x : H'), hx⟩)) (x : H'),
      W.symm_apply_apply]
  rw [hnorm, hinner]
  exact h ⟨W.symm (x : H'), hx⟩

/-- An upper form bound transports to the unitary conjugate. -/
theorem semiboundedAbove_unitaryConj_of
    (W : H ≃ₗᵢ[𝕜] H') {A : H →ₗ.[𝕜] H} {c : ℝ}
    (h : SemiboundedAbove A c) : SemiboundedAbove (A.conj W.toLinearEquiv) c := by
  rw [semiboundedAbove_iff] at h ⊢
  intro x
  have hx : W.symm (x : H') ∈ A.domain :=
    (_root_.LinearPMap.mem_conj_domain_iff).mp x.property
  have hnorm : ‖(x : H')‖ = ‖W.symm (x : H')‖ := (W.symm.norm_map _).symm
  have hinner : ⟪(A.conj W.toLinearEquiv) x, (x : H')⟫_𝕜 =
      ⟪A ⟨W.symm (x : H'), hx⟩, W.symm (x : H')⟫_𝕜 := by
    rw [_root_.LinearPMap.conj_apply]
    dsimp only [LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.coe_symm_toLinearEquiv]
    rw [← W.symm.inner_map_map (W (A ⟨W.symm (x : H'), hx⟩)) (x : H'),
      W.symm_apply_apply]
  rw [hnorm, hinner]
  exact h ⟨W.symm (x : H'), hx⟩

/-- Lower form bounds are invariant under unitary conjugation. -/
theorem semiboundedBelow_unitaryConj_iff
    (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) (c : ℝ) :
    SemiboundedBelow (A.conj W.toLinearEquiv) c ↔ SemiboundedBelow A c := by
  refine ⟨fun h => ?_, semiboundedBelow_unitaryConj_of W⟩
  have h' := semiboundedBelow_unitaryConj_of W.symm h
  rwa [LinearIsometryEquiv.toLinearEquiv_symm, _root_.LinearPMap.conj_conj_symm] at h'

/-- Upper form bounds are invariant under unitary conjugation. -/
theorem semiboundedAbove_unitaryConj_iff
    (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) (c : ℝ) :
    SemiboundedAbove (A.conj W.toLinearEquiv) c ↔ SemiboundedAbove A c := by
  refine ⟨fun h => ?_, semiboundedAbove_unitaryConj_of W⟩
  have h' := semiboundedAbove_unitaryConj_of W.symm h
  rwa [LinearIsometryEquiv.toLinearEquiv_symm, _root_.LinearPMap.conj_conj_symm] at h'

/-! ### Reducing subspaces -/

section Reducing

variable (W : H ≃ₗᵢ[𝕜] H') (A : H →ₗ.[𝕜] H) (U : Submodule 𝕜 H)
  [U.HasOrthogonalProjection]

/-- The image subspace of a reducing subspace reduces the conjugated operator.

Both halves of `_root_.LinearPMap.IsReducing` transport for the same two reasons: the
orthogonal projection onto `U.map W` is `W ∘ P_U ∘ W⁻¹`
(`Submodule.starProjection_map_apply`) and the orthogonal complement of an image
is the image of the complement (`Submodule.map_orthogonal_equiv`). -/
theorem reducesSubspace_unitaryConj (hred : _root_.LinearPMap.IsReducing A U) :
    _root_.LinearPMap.IsReducing (A.conj W.toLinearEquiv)
      (U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) := by
  have hperp : (U.map (W.toLinearEquiv : H →ₗ[𝕜] H'))ᗮ =
      Uᗮ.map (W.toLinearEquiv : H →ₗ[𝕜] H') :=
    (Submodule.map_orthogonal_equiv U W).symm
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Submodule.starProjection_map_apply,
      _root_.LinearPMap.mem_conj_domain_iff,
      LinearIsometryEquiv.coe_symm_toLinearEquiv, W.symm_apply_apply]
    exact hred.starProjection_mem_domain
      ((_root_.LinearPMap.mem_conj_domain_iff).mp hx)
  · rw [_root_.LinearPMap.isInvariant_iff]
    intro x hx
    have hpre : W.symm (x : H') ∈ U := by
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
      have hzz : W.symm (x : H') = z := by rw [← hzx]; exact W.symm_apply_apply z
      rw [hzz]; exact hz
    rw [_root_.LinearPMap.conj_apply]
    dsimp only [LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.coe_symm_toLinearEquiv]
    exact Submodule.mem_map.mpr
      ⟨A ⟨W.symm (x : H'),
          (_root_.LinearPMap.mem_conj_domain_iff).mp x.property⟩,
        hred.isInvariant.apply_mem ⟨W.symm (x : H'),
          (_root_.LinearPMap.mem_conj_domain_iff).mp x.property⟩ hpre, rfl⟩
  · rw [_root_.LinearPMap.isInvariant_iff]
    intro x hx
    rw [hperp] at hx ⊢
    have hpre : W.symm (x : H') ∈ Uᗮ := by
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
      have hzz : W.symm (x : H') = z := by rw [← hzx]; exact W.symm_apply_apply z
      rw [hzz]; exact hz
    rw [_root_.LinearPMap.conj_apply]
    dsimp only [LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.coe_symm_toLinearEquiv]
    exact Submodule.mem_map.mpr
      ⟨A ⟨W.symm (x : H'),
          (_root_.LinearPMap.mem_conj_domain_iff).mp x.property⟩,
        hred.isInvariant_orthogonal.apply_mem ⟨W.symm (x : H'),
          (_root_.LinearPMap.mem_conj_domain_iff).mp x.property⟩ hpre, rfl⟩

/-- The restriction of a unitary equivalence to a subspace and its image. -/
noncomputable def submoduleMapIsometry :
    U ≃ₗᵢ[𝕜] U.map (W.toLinearEquiv : H →ₗ[𝕜] H') where
  toLinearEquiv := W.toLinearEquiv.submoduleMap U
  norm_map' x := W.norm_map (x : H)

omit [U.HasOrthogonalProjection] in
/-- The restricted isometry acts by the ambient unitary. -/
@[simp] private theorem submoduleMapIsometry_coe_apply (x : U) :
    ((submoduleMapIsometry W U x :
      U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') = W (x : H) := rfl

omit [U.HasOrthogonalProjection] in
/-- Its inverse acts by the inverse unitary. -/
@[simp] private theorem submoduleMapIsometry_symm_coe_apply
    (x : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) :
    (((submoduleMapIsometry W U).symm x : U) : H) = W.symm (x : H') := rfl

/-- **The reducing restriction commutes with unitary conjugation.**

Restricting `W A W⁻¹` to the image subspace is the same partial map as
conjugating the restriction of `A` to `U` by the restricted unitary
`U ≃ₗᵢ U.map W`.  Both sides have domain `{x ∈ U.map W | W⁻¹ x ∈ dom A}` and both
send `x` to `W (A (W⁻¹ x))`, so this is an equality on the nose. -/
theorem reducingRestriction_unitaryConj (hred : _root_.LinearPMap.IsReducing A U) :
    reducingRestriction (A.conj W.toLinearEquiv) (U.map (W.toLinearEquiv : H →ₗ[𝕜] H'))
        (reducesSubspace_unitaryConj W A U hred) =
      ((reducingRestriction A U hred).conj (submoduleMapIsometry W U).toLinearEquiv) := by
  refine _root_.LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · ext z
    simp only [mem_reducingRestriction_domain_iff, _root_.LinearPMap.mem_conj_domain_iff,
      _root_.LinearPMap.mem_conj_domain_iff, mem_reducingRestriction_domain_iff,
      LinearIsometryEquiv.coe_symm_toLinearEquiv, submoduleMapIsometry_symm_coe_apply]
  · rintro u hx hy
    apply Subtype.ext
    have hxA : W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') ∈ A.domain :=
      (_root_.LinearPMap.mem_conj_domain_iff).mp
        ((mem_reducingRestriction_domain_iff _ _ _ u).mp hx)
    have hxU : W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') ∈ U := by
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp u.property
      have hzz : W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') = z := by
        rw [← hzx]; exact W.symm_apply_apply z
      rw [hzz]; exact hz
    have hxD : (⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxU⟩ : U) ∈
        (reducingRestriction A U hred).domain :=
      (mem_reducingRestriction_domain_iff A U hred _).mpr hxA
    have hL : ((reducingRestriction (A.conj W.toLinearEquiv)
          (U.map (W.toLinearEquiv : H →ₗ[𝕜] H'))
          (reducesSubspace_unitaryConj W A U hred) ⟨u, hx⟩ :
            U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') =
        W (A ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxA⟩) := by
      calc
        _ = (A.conj W.toLinearEquiv)
              ⟨u, (_root_.LinearPMap.mem_conj_domain_iff).mpr hxA⟩ :=
          coe_reducingRestriction_apply (A.conj W.toLinearEquiv)
            (U.map (W.toLinearEquiv : H →ₗ[𝕜] H'))
            (reducesSubspace_unitaryConj W A U hred) u
            ((_root_.LinearPMap.mem_conj_domain_iff).mpr hxA)
        _ = W (A ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxA⟩) := by
          rw [_root_.LinearPMap.conj_apply]
          dsimp only [LinearIsometryEquiv.coe_toLinearEquiv,
            LinearIsometryEquiv.coe_symm_toLinearEquiv]
    have hR : ((((reducingRestriction A U hred).conj
        (submoduleMapIsometry W U).toLinearEquiv) ⟨u, hy⟩ :
            U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H') =
        W (A ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxA⟩) := by
      have hstep : ((reducingRestriction A U hred
            ⟨⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxU⟩,
              hxD⟩ : U) : H) =
          A ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxA⟩ :=
        coe_reducingRestriction_apply A U hred
          ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxU⟩ hxA
      have hsymm : (submoduleMapIsometry W U).symm
          (u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) =
            ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxU⟩ := by
        apply Subtype.ext
        exact submoduleMapIsometry_symm_coe_apply W U u
      have hArg :
          (⟨(submoduleMapIsometry W U).symm u,
            (_root_.LinearPMap.mem_conj_domain_iff).mp hy⟩ :
              (reducingRestriction A U hred).domain) =
            ⟨⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxU⟩, hxD⟩ := by
        apply Subtype.ext
        exact hsymm
      calc ((((reducingRestriction A U hred).conj
          (submoduleMapIsometry W U).toLinearEquiv) ⟨u, hy⟩ :
              U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H')
          = W (((reducingRestriction A U hred
              ⟨⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxU⟩,
                hxD⟩ : U) : H)) := by
              rw [_root_.LinearPMap.conj_apply]
              dsimp only [LinearIsometryEquiv.coe_toLinearEquiv,
                LinearIsometryEquiv.coe_symm_toLinearEquiv]
              rw [submoduleMapIsometry_coe_apply, hArg]
        _ = W (A ⟨W.symm ((u : U.map (W.toLinearEquiv : H →ₗ[𝕜] H')) : H'), hxA⟩) := by
              rw [hstep]
    rw [hL, hR]

end Reducing

end LinearPMap
end TauCeti
