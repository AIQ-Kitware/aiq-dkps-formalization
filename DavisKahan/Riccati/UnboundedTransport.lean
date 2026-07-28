/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Riccati.UnboundedExistence

/-!
# Transport of closed operators by bounded linear equivalences

This leaf constructs the pullback of a closed operator through a continuous
linear equivalence.  The transported domain is explicit, closedness is proved
by pulling the graph back through the product homeomorphism, and both action
identities are exposed for later graph-rotation diagonalization.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

namespace ClosedOperator

/-- Domain obtained by pulling an operator domain back through a continuous
linear equivalence. -/
abbrev pullbackDomain
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E) :
    Submodule 𝕜 E :=
  TauCeti.LinearPMap.pullbackDomain A.toLinearPMap e

@[simp] theorem mem_pullbackDomain_iff
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E)
    (x : E) :
    x ∈ pullbackDomain A e ↔ e x ∈ A.domain :=
  Iff.rfl

/-- A vector in the pulled-back domain, transported to the original operator
 domain with its membership witness. -/
abbrev pullbackDomainToOriginal
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E) :
    pullbackDomain A e →ₗ[𝕜] A.domain :=
  TauCeti.LinearPMap.pullbackDomainToOriginal A.toLinearPMap e

@[simp] theorem pullbackDomainToOriginal_coe
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E)
    (x : pullbackDomain A e) :
    ((pullbackDomainToOriginal A e x : A.domain) : E) = e (x : E) :=
  rfl

/-- Action of the pulled-back operator on its explicit transported domain. -/
abbrev pullbackLinearMap
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E) :
    pullbackDomain A e →ₗ[𝕜] E :=
  TauCeti.LinearPMap.pullbackLinearMap A.toLinearPMap e

@[simp] theorem pullbackLinearMap_apply
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E)
    (x : pullbackDomain A e) :
    pullbackLinearMap A e x =
      e.symm (A.toLinearMap (pullbackDomainToOriginal A e x)) :=
  rfl

private theorem pullbackDomain_dense
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E) :
    Dense ((pullbackDomain A e : Submodule 𝕜 E) : Set E) :=
  TauCeti.LinearPMap.pullback_dense A.toLinearPMap e A.toLinearPMap_dense

private theorem pullbackLinearMap_closedGraph
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E) :
    IsClosed (Set.range fun x : pullbackDomain A e =>
      ((x : E), pullbackLinearMap A e x)) := by
  let coords : E × E → E × E := fun p => (e p.1, e p.2)
  have hcoords : Continuous coords := by
    fun_prop
  rw [show Set.range (fun x : pullbackDomain A e =>
      ((x : E), pullbackLinearMap A e x)) =
      coords ⁻¹' (Set.range fun x : A.domain =>
        ((x : E), A.toLinearMap x)) by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨pullbackDomainToOriginal A e x, ?_⟩
      apply Prod.ext
      · rfl
      · simp [coords]
    · rintro ⟨x, hx⟩
      have hfst : (x : E) = e p.1 := congrArg Prod.fst hx
      have hsnd : A.toLinearMap x = e p.2 := congrArg Prod.snd hx
      have hp1 : p.1 ∈ pullbackDomain A e := by
        change e p.1 ∈ A.domain
        rw [← hfst]
        exact x.property
      let z : pullbackDomain A e := ⟨p.1, hp1⟩
      have hz : pullbackDomainToOriginal A e z = x := by
        apply Subtype.ext
        exact hfst.symm
      refine ⟨z, Prod.ext rfl ?_⟩
      apply e.injective
      change e (pullbackLinearMap A e z) = e p.2
      rw [pullbackLinearMap_apply, e.apply_symm_apply, hz]
      exact hsnd]
  exact A.closed_graph.preimage hcoords

/-- Pull a closed operator back through a continuous linear equivalence.  Its
 domain is exactly the inverse image of the original domain. -/
noncomputable def pullback
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E) :
    ClosedOperator (𝕜 := 𝕜) (E := E) where
  domain := pullbackDomain A e
  toLinearMap := pullbackLinearMap A e
  dense_domain := pullbackDomain_dense A e
  closed_graph := pullbackLinearMap_closedGraph A e

@[simp] theorem pullback_domain
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E) :
    (pullback A e).domain = pullbackDomain A e :=
  rfl

@[simp] theorem mem_pullback_domain_iff
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E)
    (x : E) :
    x ∈ (pullback A e).domain ↔ e x ∈ A.domain :=
  Iff.rfl

@[simp] theorem pullback_apply
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E)
    (x : (pullback A e).domain) :
    (pullback A e).toLinearMap x =
      e.symm (A.toLinearMap (pullbackDomainToOriginal A e x)) :=
  rfl

/-- The original equivalence intertwines its operator pullback with the
 original closed operator, including both directions of domain transport. -/
theorem pullback_unitaryEquivalent
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (e : E ≃L[𝕜] E)
    (he : IsUnitaryOperator e.toContinuousLinearMap) :
    ClosedOperator.UnitaryEquivalent
      (pullback A e) A e.toContinuousLinearMap
        e.symm.toContinuousLinearMap := by
  have hesymm : IsUnitaryOperator e.symm.toContinuousLinearMap := by
    constructor
    · intro y
      have h := he.1 (e.symm y)
      simpa using h.symm
    · exact e.symm.surjective
  have hleft : e.symm.toContinuousLinearMap ∘L e.toContinuousLinearMap =
      ContinuousLinearMap.id 𝕜 E := by
    apply ContinuousLinearMap.ext
    intro x
    simp
  have hright : e.toContinuousLinearMap ∘L e.symm.toContinuousLinearMap =
      ContinuousLinearMap.id 𝕜 E := by
    apply ContinuousLinearMap.ext
    intro x
    simp
  refine ⟨he, hesymm, hleft, hright, ?_⟩
  let hWdom : ∀ x : (pullback A e).domain,
      e (x : E) ∈ A.domain := fun x => x.property
  refine ⟨hWdom, ?_⟩
  let hWinvdom : ∀ y : A.domain,
      e.symm (y : E) ∈ (pullback A e).domain := fun y => by
        change e (e.symm (y : E)) ∈ A.domain
        simpa using y.property
  refine ⟨hWinvdom, ?_, ?_⟩
  · intro x
    change A.toLinearMap ⟨e (x : E), hWdom x⟩ =
      e ((pullback A e).toLinearMap x)
    rw [pullback_apply, e.apply_symm_apply]
    rfl
  · intro y
    change (pullback A e).toLinearMap
        ⟨e.symm (y : E), hWinvdom y⟩ =
      e.symm (A.toLinearMap y)
    rw [pullback_apply]
    congr 2
    apply Subtype.ext
    simp

end ClosedOperator

end DavisKahanExt
end TauCeti
