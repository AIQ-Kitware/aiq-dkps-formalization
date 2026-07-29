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

omit [CompleteSpace E] in
/-- The projection onto a reducing subspace preserves the operator domain. -/
theorem projection_mem_domain
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : A.ReducesSubspace U) (x : A.domain) :
    U.starProjection (x : E) ∈ A.domain :=
  h.1 x

omit [CompleteSpace E] in
/-- The complementary projection of a reducing subspace preserves the
operator domain. -/
theorem orthogonalProjection_mem_domain
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : A.ReducesSubspace U) (x : A.domain) :
    Uᗮ.starProjection (x : E) ∈ A.domain :=
  h.2.1 x

omit [CompleteSpace E] in
/-- The selected summand of a reducing subspace is invariant. -/
theorem invariant
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : A.ReducesSubspace U) : A.InvariantSubspace U :=
  h.2.2.1

omit [CompleteSpace E] in
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
    (U : Submodule 𝕜 E) : Submodule 𝕜 U :=
  TauCeti.LinearPMap.reducingRestrictionDomain A.toLinearPMap U

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
@[simp]
theorem coe_projectDomainToReducingRestriction
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) (x : A.domain) :
    (((projectDomainToReducingRestriction A U hred x :
        reducingRestrictionDomain A U) : U) : E) =
      U.starProjection (x : E) :=
  rfl

omit [CompleteSpace E] in
private theorem reducingRestrictionDomain_dense
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) :
    Dense ((reducingRestrictionDomain A U : Submodule 𝕜 U) : Set U) :=
  TauCeti.LinearPMap.reducingRestriction_dense A.toLinearPMap U hred
    A.toLinearPMap_dense

omit [CompleteSpace E] in
private theorem reducingRestrictionLinearMap_closedGraph
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) :
    IsClosed (Set.range fun x : reducingRestrictionDomain A U =>
      (((x : reducingRestrictionDomain A U) : U),
        reducingRestrictionLinearMap A U hred x)) :=
  TauCeti.LinearPMap.reducingRestriction_closedGraph A.toLinearPMap U hred
    A.closed_graph

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

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
/-- The reducing-subspace inclusion is isometric. -/
theorem reducingSubspaceInclusion_isometric (U : Submodule 𝕜 E) :
    IsometricEmbedding (reducingSubspaceInclusion U) :=
  fun _ => rfl

omit [CompleteSpace E] in
/-- The inclusion maps the restricted domain into the ambient domain. -/
theorem reducingRestriction_inclusion_mem_domain
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U)
    (x : (reducingRestriction A U hred).domain) :
    reducingSubspaceInclusion U (x : U) ∈ A.domain :=
  x.property

omit [CompleteSpace E] in
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

/-- Adjoint-domain membership of the restriction is exactly ambient
adjoint-domain membership for the included vector. -/
theorem mem_reducingRestriction_adjoint_domain_iff
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U) (y : U) :
    y ∈ (reducingRestriction A U hred).toLinearPMap.adjoint.domain ↔
      (y : E) ∈ A.toLinearPMap.adjoint.domain :=
  TauCeti.LinearPMap.mem_reducingRestriction_adjoint_domain_iff
    A.toLinearPMap U hred y

omit [CompleteSpace E] in
/-- Symmetry passes to the reducing restriction. -/
theorem reducingRestriction_isSymmetric
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U)
    (hA : A.IsSymmetric) :
    (reducingRestriction A U hred).IsSymmetric :=
  TauCeti.LinearPMap.reducingRestriction_isSymmetric A.toLinearPMap U hred hA

/-- A self-adjoint operator restricts to a self-adjoint operator on every
reducing subspace. -/
theorem reducingRestriction_isSelfAdjoint
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.ReducesSubspace U)
    (hA : A.IsSelfAdjoint) :
    (reducingRestriction A U hred).IsSelfAdjoint :=
  TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A.toLinearPMap U hred
    A.toLinearPMap_dense hA

end ClosedOperator
end DavisKahanExt
end TauCeti
