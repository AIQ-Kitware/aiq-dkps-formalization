/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ClosedOperator.Basic
import ForMathlib.Analysis.InnerProductSpace.ReducingSubspace

/-!
# Restrictions of closed operators to reducing subspaces

This module gives a scalar-generic restriction construction for a densely
specified closed operator and an orthogonally complemented reducing subspace.
The construction keeps domains explicit, proves density and graph closedness,
and shows that self-adjointness passes to the restriction.

The result is independent of spectral theory.  Spectral packages only need to
produce the reducing-subspace laws; the closed restriction and its inclusion
intertwining are then canonical.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

noncomputable local instance completeSpaceOfHasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

namespace ClosedOperator

/-- Compatibility facade for invariance under the canonical partial map. -/
abbrev InvariantSubspace
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) : Prop :=
  TauCeti.LinearPMap.InvariantSubspace A.toLinearPMap U

/-- Compatibility facade for reduction of the canonical partial map. -/
abbrev ReducesSubspace
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : Prop :=
  TauCeti.LinearPMap.ReducesSubspace A.toLinearPMap U

namespace ReducesSubspace

/-- The projection onto a reducing subspace preserves the operator domain. -/
theorem projection_mem_domain
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : A.ReducesSubspace U) (x : A.domain) :
    U.starProjection (x : E) ∈ A.domain :=
  h.1 x

/-- The complementary projection of a reducing subspace preserves the
operator domain. -/
theorem orthogonalProjection_mem_domain
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : A.ReducesSubspace U) (x : A.domain) :
    Uᗮ.starProjection (x : E) ∈ A.domain :=
  h.2.1 x

/-- The selected summand of a reducing subspace is invariant. -/
theorem invariant
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : A.ReducesSubspace U) : A.InvariantSubspace U :=
  h.2.2.1

/-- The complementary summand of a reducing subspace is invariant. -/
theorem orthogonal_invariant
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : A.ReducesSubspace U) : A.InvariantSubspace Uᗮ :=
  h.2.2.2

end ReducesSubspace

/-- Compatibility facade for the raw restricted domain. -/
abbrev reducingRestrictionDomain
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) : Submodule 𝕜 U where
  _ := TauCeti.LinearPMap.reducingRestrictionDomain A.toLinearPMap U

@[simp]
theorem mem_reducingRestrictionDomain_iff
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) (x : U) :
    x ∈ reducingRestrictionDomain A U ↔ (x : E) ∈ A.domain :=
  Iff.rfl

/-- Compatibility facade for the ambient-domain inclusion. -/
abbrev reducingRestrictionDomainToAmbient
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E)
    (x : reducingRestrictionDomain A U) : A.domain :=
  TauCeti.LinearPMap.reducingRestrictionDomainToAmbient A.toLinearPMap U x

@[simp]
theorem reducingRestrictionDomainToAmbient_coe
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E)
    (x : reducingRestrictionDomain A U) :
    ((reducingRestrictionDomainToAmbient A U x : A.domain) : E) =
      ((x : reducingRestrictionDomain A U) : U) :=
  rfl

/-- Compatibility facade for the raw restricted action. -/
abbrev reducingRestrictionLinearMap
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) :
    reducingRestrictionDomain A U →ₗ[𝕜] U :=
  TauCeti.LinearPMap.reducingRestrictionLinearMap A.toLinearPMap U hred

@[simp]
theorem coe_reducingRestrictionLinearMap
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U)
    (x : reducingRestrictionDomain A U) :
    ((reducingRestrictionLinearMap A U hred x : U) : E) =
      A.toLinearMap (reducingRestrictionDomainToAmbient A U x) :=
  rfl

/-- Compatibility facade for projection into the raw restricted domain. -/
noncomputable abbrev projectDomainToReducingRestriction
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) (x : A.domain) :
    reducingRestrictionDomain A U :=
  TauCeti.LinearPMap.projectDomainToReducingRestriction A.toLinearPMap U hred x

@[simp]
theorem coe_projectDomainToReducingRestriction
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) (x : A.domain) :
    (((projectDomainToReducingRestriction A U hred x :
        reducingRestrictionDomain A U) : U) : E) =
      U.starProjection (x : E) :=
  rfl

private theorem reducingRestrictionDomain_dense
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) :
    Dense ((reducingRestrictionDomain A U : Submodule 𝕜 U) : Set U) := by
  rw [dense_iff_closure_eq]
  ext u
  simp only [Set.mem_univ, iff_true]
  have hu : (u : E) ∈ closure (A.domain : Set E) := by
    rw [A.dense_domain.closure_eq]
    trivial
  obtain ⟨s, hs, hs_lim⟩ := mem_closure_iff_seq_limit.mp hu
  let t : ℕ → U := fun n =>
    ⟨U.starProjection (s n), U.starProjection_apply_mem (s n)⟩
  refine mem_closure_iff_seq_limit.mpr ⟨t, ?_, ?_⟩
  · intro n
    exact hred.projection_mem_domain ⟨s n, hs n⟩
  · have hlim := (U.starProjection.continuous.tendsto (u : E)).comp hs_lim
    have hfix : U.starProjection (u : E) = (u : E) :=
      Submodule.starProjection_eq_self_iff.mpr u.property
    change Tendsto (fun n => t n) atTop (𝓝 u)
    apply tendsto_subtype_rng.mpr
    simpa [t, hfix, Function.comp_def] using hlim

private theorem reducingRestrictionLinearMap_closedGraph
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) :
    IsClosed (Set.range fun x : reducingRestrictionDomain A U =>
      (((x : reducingRestrictionDomain A U) : U),
        reducingRestrictionLinearMap A U hred x)) := by
  let coords : U × U → E × E := fun p => ((p.1 : E), (p.2 : E))
  have hcoords : Continuous coords :=
    (U.subtypeL.continuous.comp continuous_fst).prodMk
      (U.subtypeL.continuous.comp continuous_snd)
  rw [show Set.range (fun x : reducingRestrictionDomain A U =>
      (((x : reducingRestrictionDomain A U) : U),
        reducingRestrictionLinearMap A U hred x)) =
      coords ⁻¹' (Set.range fun x : A.domain =>
        ((x : E), A.toLinearMap x)) by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨reducingRestrictionDomainToAmbient A U x, rfl⟩
    · rintro ⟨x, hx⟩
      have hx0 : (x : E) = (p.1 : E) := congrArg Prod.fst hx
      have hx1 : A.toLinearMap x = (p.2 : E) := congrArg Prod.snd hx
      have hpdom : (p.1 : E) ∈ A.domain := hx0 ▸ x.property
      let u : reducingRestrictionDomain A U := ⟨p.1, hpdom⟩
      refine ⟨u, Prod.ext rfl ?_⟩
      apply Subtype.ext
      change A.toLinearMap
          (reducingRestrictionDomainToAmbient A U u) = (p.2 : E)
      have hxu : reducingRestrictionDomainToAmbient A U u = x := by
        apply Subtype.ext
        exact hx0.symm
      simpa [hxu] using hx1]
  exact A.closed_graph.preimage hcoords

/-- The closed operator induced on a reducing subspace. -/
noncomputable def reducingRestriction
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) :
    ClosedOperator (𝕜 := 𝕜) (E := U) where
  domain := (TauCeti.LinearPMap.reducingRestriction A.toLinearPMap U hred).domain
  toLinearMap := (TauCeti.LinearPMap.reducingRestriction A.toLinearPMap U hred).toFun
  dense_domain := reducingRestrictionDomain_dense A U hred
  closed_graph := reducingRestrictionLinearMap_closedGraph A U hred

@[simp]
theorem reducingRestriction_domain
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) :
    (reducingRestriction A U hred).domain =
      reducingRestrictionDomain A U :=
  rfl

/-- The canonical inclusion of a reducing subspace. -/
def reducingSubspaceInclusion (U : Submodule 𝕜 E) : U →L[𝕜] E :=
  U.subtypeL

/-- The reducing-subspace inclusion is isometric. -/
theorem reducingSubspaceInclusion_isometric (U : Submodule 𝕜 E) :
    IsometricEmbedding (reducingSubspaceInclusion U) :=
  fun _ => rfl

/-- The inclusion maps the restricted domain into the ambient domain. -/
theorem reducingRestriction_inclusion_mem_domain
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U)
    (x : (reducingRestriction A U hred).domain) :
    reducingSubspaceInclusion U (x : U) ∈ A.domain :=
  x.property

/-- The inclusion intertwines the restricted and ambient operators. -/
theorem reducingRestriction_inclusion_intertwines
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U)
    (x : (reducingRestriction A U hred).domain) :
    A.toLinearMap
        ⟨reducingSubspaceInclusion U (x : U),
          reducingRestriction_inclusion_mem_domain A U hred x⟩ =
      reducingSubspaceInclusion U
        ((reducingRestriction A U hred).toLinearMap x) :=
  rfl

private theorem continuous_projectDomainToReducingRestriction
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) :
    Continuous (projectDomainToReducingRestriction A U hred) := by
  have hproj : Continuous fun x : A.domain =>
      U.starProjection (x : E) :=
    U.starProjection.continuous.comp A.domain.subtypeL.continuous
  have hprojU : Continuous fun x : A.domain =>
      (⟨U.starProjection (x : E),
        U.starProjection_apply_mem (x : E)⟩ : U) :=
    hproj.subtype_mk _
  exact hprojU.subtype_mk fun x => hred.projection_mem_domain x

/-- Adjoint-domain membership of the restriction is exactly ambient
adjoint-domain membership for the included vector. -/
theorem mem_reducingRestriction_adjoint_domain_iff
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) (y : U) :
    y ∈ (reducingRestriction A U hred).toLinearPMap.adjoint.domain ↔
      (y : E) ∈ A.toLinearPMap.adjoint.domain := by
  rw [LinearPMap.mem_adjoint_domain_iff,
    LinearPMap.mem_adjoint_domain_iff]
  constructor
  · intro hy
    have hcomp : Continuous fun x : A.domain =>
        ⟪y, (reducingRestriction A U hred).toLinearPMap
          (projectDomainToReducingRestriction A U hred x)⟫_𝕜 :=
      hy.comp (continuous_projectDomainToReducingRestriction A U hred)
    have hfun : (fun x : A.domain =>
        ⟪y, (reducingRestriction A U hred).toLinearPMap
          (projectDomainToReducingRestriction A U hred x)⟫_𝕜) =
        fun x : A.domain => ⟪(y : E), A.toLinearMap x⟫_𝕜 := by
      funext x
      let xu : A.domain :=
        ⟨U.starProjection (x : E), hred.projection_mem_domain x⟩
      let xo : A.domain :=
        ⟨Uᗮ.starProjection (x : E), hred.orthogonalProjection_mem_domain x⟩
      have hxsplit : x = xu + xo := by
        apply Subtype.ext
        exact (U.starProjection_add_starProjection_orthogonal (x : E)).symm
      have horth : ⟪(y : E), A.toLinearMap xo⟫_𝕜 = 0 := by
        exact Submodule.inner_right_of_mem_orthogonal y.property
          (hred.orthogonal_invariant xo
            (Uᗮ.starProjection_apply_mem (x : E)))
      calc
        ⟪y, (reducingRestriction A U hred).toLinearPMap
            (projectDomainToReducingRestriction A U hred x)⟫_𝕜 =
            ⟪(y : E), A.toLinearMap xu⟫_𝕜 := rfl
        _ = ⟪(y : E), A.toLinearMap xu + A.toLinearMap xo⟫_𝕜 := by
              rw [inner_add_right, horth, add_zero]
        _ = ⟪(y : E), A.toLinearMap (xu + xo)⟫_𝕜 := by rw [map_add]
        _ = ⟪(y : E), A.toLinearMap x⟫_𝕜 := by rw [← hxsplit]
    rw [hfun] at hcomp
    exact hcomp
  · intro hy
    have hincl : Continuous fun x : (reducingRestriction A U hred).domain =>
        reducingRestrictionDomainToAmbient A U x := by
      have hcoe : Continuous fun x : (reducingRestriction A U hred).domain =>
          (((x : (reducingRestriction A U hred).domain) : U) : E) :=
        U.subtypeL.continuous.comp
          (reducingRestriction A U hred).domain.subtypeL.continuous
      exact hcoe.subtype_mk fun x => x.property
    have hcomp := hy.comp hincl
    have hcomp' : Continuous fun x : (reducingRestriction A U hred).domain =>
        ⟪(y : E),
          A.toLinearMap (reducingRestrictionDomainToAmbient A U x)⟫_𝕜 := hcomp
    exact hcomp'

/-- Symmetry passes to the reducing restriction. -/
theorem reducingRestriction_isSymmetric
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U)
    (hA : A.IsSymmetric) :
    (reducingRestriction A U hred).IsSymmetric := by
  intro x y
  exact hA (reducingRestrictionDomainToAmbient A U x)
    (reducingRestrictionDomainToAmbient A U y)

/-- A self-adjoint operator restricts to a self-adjoint operator on every
reducing subspace. -/
theorem reducingRestriction_isSelfAdjoint
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U)
    (hA : A.IsSelfAdjoint) :
    (reducingRestriction A U hred).IsSelfAdjoint := by
  let R := reducingRestriction A U hred
  rw [R.isSelfAdjoint_iff_toLinearPMap_adjoint_eq]
  refine LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · ext y
    change y ∈ R.toLinearPMap.adjoint.domain ↔ y ∈ R.domain
    rw [mem_reducingRestriction_adjoint_domain_iff A U hred]
    rw [hA.toLinearPMap_adjoint_eq]
    rfl
  · intro y hyAdj hyR
    let yAdj : U := R.toLinearPMap.adjoint ⟨y, hyAdj⟩
    let yAct : U := R.toLinearPMap ⟨y, hyR⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      R.toLinearPMap_dense ⟨y, hyAdj⟩
    have hsymm := reducingRestriction_isSymmetric A U hred hA.isSymmetric
    have hinner : (fun x : U => ⟪yAdj, x⟫_𝕜) =
        fun x : U => ⟪yAct, x⟫_𝕜 := by
      apply Continuous.ext_on R.dense_domain
      · exact continuous_const.inner continuous_id
      · exact continuous_const.inner continuous_id
      · intro x hx
        let xDom : R.domain := ⟨x, hx⟩
        calc
          ⟪yAdj, x⟫_𝕜 = ⟪y, R.toLinearPMap xDom⟫_𝕜 := by
            simpa [yAdj, xDom] using hformal xDom
          _ = ⟪yAct, x⟫_𝕜 := by
            simpa [yAct, xDom, R] using (hsymm ⟨y, hyR⟩ xDom).symm
    have hzero : ⟪yAdj - yAct, yAdj - yAct⟫_𝕜 = 0 := by
      rw [inner_sub_left, congrFun hinner (yAdj - yAct), sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

end ClosedOperator
end DavisKahanExt
end TauCeti
