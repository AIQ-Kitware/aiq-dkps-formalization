/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Riccati.UnboundedCore

/-!
# Strong unbounded Riccati graph reduction

This leaf proves the domain-controlled equivalence between invariance of a
bounded angular graph under the closed block operator and the strong Riccati
equation.  Operator-domain membership, graph membership, and coordinate action
are kept as separate lemmas so later existence and diagonalization arguments
can reuse the same core calculation.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- A direct-sum vector belongs to the unbounded block graph exactly when its
second coordinate is the angular operator applied to its first coordinate. -/
theorem toLp_mem_unboundedBlockGraph_iff
    (X : E0 →L[𝕜] E1) (u : E0) (v : E1) :
    WithLp.toLp 2 (u, v) ∈ unboundedBlockGraph X ↔ v = X u := by
  constructor
  · intro hmem
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
    change WithLp.toLp 2 (w, X w) = WithLp.toLp 2 (u, v) at hw
    have hp : (w, X w) = (u, v) :=
      (WithLp.linearEquiv 2 𝕜 (E0 × E1)).symm.injective hw
    have hfst : w = u := congrArg Prod.fst hp
    have hsnd : X w = v := congrArg Prod.snd hp
    calc
      v = X w := hsnd.symm
      _ = X u := congrArg X hfst
  · intro hv
    refine LinearMap.mem_range.mpr ⟨u, ?_⟩
    change WithLp.toLp 2 (u, X u) = WithLp.toLp 2 (u, v)
    rw [hv]

/-- Coordinate characterization of membership in an unbounded block graph. -/
theorem mem_unboundedBlockGraph_iff
    (X : E0 →L[𝕜] E1) (z : WithLp 2 (E0 × E1)) :
    z ∈ unboundedBlockGraph X ↔ WithLp.snd z = X (WithLp.fst z) := by
  change WithLp.toLp 2 (WithLp.fst z, WithLp.snd z) ∈
      unboundedBlockGraph X ↔ WithLp.snd z = X (WithLp.fst z)
  exact toLp_mem_unboundedBlockGraph_iff X (WithLp.fst z) (WithLp.snd z)

/-- The graph vector associated with a vector in the first diagonal domain,
carrying its membership witness in the full block-operator domain. -/
noncomputable def unboundedBlockGraphDomainVectorPMap
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) : (unboundedBlockOperatorCorePMap H).domain :=
  ⟨WithLp.toLp 2 ((x : E0), X (x : E0)), by
    rw [unboundedBlockOperatorCorePMap_domain]
    exact ⟨x.property, hdom x⟩⟩

/-- Compatibility spelling of the raw graph-domain vector. -/
noncomputable abbrev unboundedBlockGraphDomainVector
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) : (unboundedBlockOperatorCore H).domain :=
  unboundedBlockGraphDomainVectorPMap H X hdom x

/-- Every raw-domain graph vector belongs to the angular graph. -/
theorem unboundedBlockGraphDomainVectorPMap_mem_graph
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) :
    ((unboundedBlockGraphDomainVectorPMap H X hdom x :
        (unboundedBlockOperatorCorePMap H).domain) : WithLp 2 (E0 × E1)) ∈
      unboundedBlockGraph X := by
  change WithLp.toLp 2 ((x : E0), X (x : E0)) ∈ unboundedBlockGraph X
  exact (toLp_mem_unboundedBlockGraph_iff X (x : E0) (X (x : E0))).2 rfl

@[simp] theorem unboundedBlockGraphDomainVector_coe
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) :
    ((unboundedBlockGraphDomainVector H X hdom x :
        (unboundedBlockOperatorCore H).domain) : WithLp 2 (E0 × E1)) =
      WithLp.toLp 2 ((x : E0), X (x : E0)) :=
  rfl

@[simp] theorem unboundedBlockOperatorCorePMap_graphVector_fst
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) :
    WithLp.fst ((unboundedBlockOperatorCorePMap H)
      (unboundedBlockGraphDomainVectorPMap H X hdom x)) =
        H.A0.toLinearMap x + H.B01 (X (x : E0)) := by
  rfl

@[simp] theorem unboundedBlockOperatorCorePMap_graphVector_snd
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) :
    WithLp.snd ((unboundedBlockOperatorCorePMap H)
      (unboundedBlockGraphDomainVectorPMap H X hdom x)) =
        H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) := by
  rfl

@[simp] theorem unboundedBlockGraphDomainVector_fst
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) :
    closedOperatorDirectSumDomainFst H.A0 H.A1
        (unboundedBlockGraphDomainVector H X hdom x) = x := by
  apply Subtype.ext
  rfl

@[simp] theorem unboundedBlockGraphDomainVector_snd
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) :
    closedOperatorDirectSumDomainSnd H.A0 H.A1
        (unboundedBlockGraphDomainVector H X hdom x) =
      ⟨X (x : E0), hdom x⟩ := by
  apply Subtype.ext
  rfl

/-- Every domain-controlled graph vector belongs to the angular graph. -/
theorem unboundedBlockGraphDomainVector_mem_graph
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) :
    ((unboundedBlockGraphDomainVector H X hdom x :
        (unboundedBlockOperatorCore H).domain) : WithLp 2 (E0 × E1)) ∈
      unboundedBlockGraph X := by
  change WithLp.toLp 2 ((x : E0), X (x : E0)) ∈ unboundedBlockGraph X
  exact (toLp_mem_unboundedBlockGraph_iff X (x : E0) (X (x : E0))).2 rfl

@[simp] theorem unboundedBlockOperatorCore_graphVector_fst
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) :
    WithLp.fst ((unboundedBlockOperatorCore H).toLinearMap
      (unboundedBlockGraphDomainVector H X hdom x)) =
        H.A0.toLinearMap x + H.B01 (X (x : E0)) := by
  rw [unboundedBlockOperatorCore_apply_fst]
  rfl

@[simp] theorem unboundedBlockOperatorCore_graphVector_snd
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hdom : PreservesRiccatiDomains H X)
    (x : H.A0.domain) :
    WithLp.snd ((unboundedBlockOperatorCore H).toLinearMap
      (unboundedBlockGraphDomainVector H X hdom x)) =
        H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) := by
  rw [unboundedBlockOperatorCore_apply_snd]
  rfl

/-- Pointwise coordinate form of the strong unbounded Riccati equation. -/
theorem strongSolvesRiccati_iff_pointwise
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    StrongSolvesRiccati H X ↔
      ∃ hdom : PreservesRiccatiDomains H X,
        ∀ x : H.A0.domain,
          H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
            X (H.A0.toLinearMap x + H.B01 (X (x : E0))) := by
  constructor
  · rintro ⟨hdom, hric⟩
    refine ⟨hdom, ?_⟩
    intro x
    rw [map_add]
    have hx := hric x
    calc
      H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
          (H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ -
              X (H.A0.toLinearMap x) - X (H.B01 (X (x : E0))) +
              H.B10 (x : E0)) +
            (X (H.A0.toLinearMap x) + X (H.B01 (X (x : E0)))) := by
        abel
      _ = 0 + (X (H.A0.toLinearMap x) + X (H.B01 (X (x : E0)))) := by
        rw [hx]
      _ = X (H.A0.toLinearMap x) + X (H.B01 (X (x : E0))) := zero_add _
  · rintro ⟨hdom, hpoint⟩
    refine ⟨hdom, ?_⟩
    intro x
    have hx := hpoint x
    rw [map_add] at hx
    calc
      H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ -
            X (H.A0.toLinearMap x) - X (H.B01 (X (x : E0))) +
            H.B10 (x : E0) =
          (H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0)) -
            (X (H.A0.toLinearMap x) + X (H.B01 (X (x : E0)))) := by
        abel
      _ = 0 := sub_eq_zero.mpr hx

/-- Invariance of the domain-controlled angular graph under the closed block
operator is equivalent to the strong unbounded Riccati equation. -/
theorem unboundedBlockGraph_invariantPMap_iff_strongRiccatiCore
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    (PreservesRiccatiDomains H X ∧
      TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCorePMap H)
        (unboundedBlockGraph X)) ↔
      StrongSolvesRiccati H X := by
  rw [strongSolvesRiccati_iff_pointwise]
  constructor
  · rintro ⟨hdom, hinv⟩
    refine ⟨hdom, ?_⟩
    intro x
    have hout := hinv (unboundedBlockGraphDomainVectorPMap H X hdom x)
      (unboundedBlockGraphDomainVectorPMap_mem_graph H X hdom x)
    simpa only [unboundedBlockOperatorCorePMap_graphVector_snd,
      unboundedBlockOperatorCorePMap_graphVector_fst] using
        (mem_unboundedBlockGraph_iff X _).1 hout
  · rintro ⟨hdom, hpoint⟩
    refine ⟨hdom, ?_⟩
    intro z hz
    rw [mem_unboundedBlockGraph_iff] at hz ⊢
    rw [unboundedBlockOperatorCorePMap_apply_snd,
      unboundedBlockOperatorCorePMap_apply_fst]
    let x0 : H.A0.domain :=
      closedOperatorDirectSumDomainFst H.A0 H.A1 z
    have hfst : WithLp.fst (z : WithLp 2 (E0 × E1)) = (x0 : E0) := by rfl
    have hsnd : WithLp.snd (z : WithLp 2 (E0 × E1)) = X (x0 : E0) := by
      rw [hz, hfst]
    have hx1 : closedOperatorDirectSumDomainSnd H.A0 H.A1 z =
        ⟨X (x0 : E0), hdom x0⟩ := by
      apply Subtype.ext
      exact hsnd
    rw [hx1, hfst, hsnd]
    exact hpoint x0

theorem unboundedBlockGraph_invariant_iff_strongRiccatiCore
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    (PreservesRiccatiDomains H X ∧
      (unboundedBlockOperatorCore H).InvariantSubspace
        (unboundedBlockGraph X)) ↔
      StrongSolvesRiccati H X := by
  change (PreservesRiccatiDomains H X ∧
    TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCorePMap H)
      (unboundedBlockGraph X)) ↔ StrongSolvesRiccati H X
  exact unboundedBlockGraph_invariantPMap_iff_strongRiccatiCore H X

end DavisKahanExt
end TauCeti
