/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
import DavisKahan.Riccati.UnboundedReduction

/-!
# The complementary graph of a reducing Riccati selection

`ContractiveReducingGraphSelection.reduces` asserts that the angular graph
*reduces* the block core, which is strictly more than invariance: the orthogonal
complement is invariant too.  That second half has not been exploited anywhere,
and it is what supplies the adjoint-side domain compatibility

```
z ∈ dom A₁  →  X* z ∈ dom A₀
```

together with the adjoint Riccati equation.  Both are needed by the sharp
unbounded `tan 2Theta` argument, where the commutator `A₀X*X - X*XA₀` must be
shown bounded; see `dev/finishtantwotheta-completion-lane.md` (ticket T1.1).

The file mirrors `UnboundedReduction`: first a coordinate characterization of
membership in the complement, then the domain-vector constructor, then the
equation itself.

The key geometric fact is that the orthogonal complement of the graph of `X` is
the graph of `-X*` **taken in the other order**:

```
(u, v) ⟂ {(w, X w)}  ↔  ∀ w, ⟪u, w⟫ + ⟪v, X w⟫ = 0  ↔  u = -X* v
```
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- Coordinate characterization of membership in the orthogonal complement of an
unbounded block graph: the complement of the graph of `X` is the graph of `-X†`
read in the opposite coordinate order. -/
theorem mem_unboundedBlockGraph_orthogonal_iff
    (X : E0 →L[𝕜] E1) (z : WithLp 2 (E0 × E1)) :
    z ∈ (unboundedBlockGraph X)ᗮ ↔
      WithLp.fst z = -(ContinuousLinearMap.adjoint X) (WithLp.snd z) := by
  set u : E0 := WithLp.fst z with hu
  set v : E1 := WithLp.snd z with hv
  constructor
  · intro hz
    -- Testing against the graph vector of `w` gives `⟪w, u + X† v⟫ = 0`.
    have hall : ∀ w : E0, ⟪w, u + (ContinuousLinearMap.adjoint X) v⟫_𝕜 = 0 := by
      intro w
      have hmem : WithLp.toLp 2 (w, X w) ∈ unboundedBlockGraph X :=
        (toLp_mem_unboundedBlockGraph_iff X w (X w)).2 rfl
      have h0 := hz _ hmem
      rw [inner_add_right, ContinuousLinearMap.adjoint_inner_right]
      simpa [hu, hv] using h0
    have hzero : u + (ContinuousLinearMap.adjoint X) v = 0 :=
      inner_self_eq_zero.1 (hall _)
    linear_combination (norm := module) hzero
  · intro hzu y hy
    rw [mem_unboundedBlockGraph_iff] at hy
    have hexp : ⟪y, z⟫_𝕜 = ⟪WithLp.fst y, u⟫_𝕜 + ⟪WithLp.snd y, v⟫_𝕜 := by
      simp [hu, hv]
    rw [hexp, hy, hzu, inner_neg_right,
      ContinuousLinearMap.adjoint_inner_right, neg_add_cancel]

/-- The angular operator maps the second diagonal domain into the first.  This
is the adjoint-side counterpart of `PreservesRiccatiDomains`, and unlike it, it
is *not* a hypothesis one may assume: it is a consequence of the graph reducing
the block core. -/
def PreservesAdjointRiccatiDomains
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∀ z : H.A1.domain, (ContinuousLinearMap.adjoint X) (z : E1) ∈ H.A0.domain

/-- The complementary-graph vector attached to a vector of the second diagonal
domain, carrying its membership witness in the full block-operator domain. -/
noncomputable def unboundedBlockGraphOrthogonalDomainVector
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hadj : PreservesAdjointRiccatiDomains H X)
    (z : H.A1.domain) : (unboundedBlockOperatorCore H).domain :=
  ⟨WithLp.toLp 2 (-(ContinuousLinearMap.adjoint X) (z : E1), (z : E1)), by
    rw [unboundedBlockOperatorCore_domain]
    exact ⟨Submodule.neg_mem _ (hadj z), z.property⟩⟩

/-- Every complementary-graph vector lies in the orthogonal complement of the
angular graph. -/
theorem unboundedBlockGraphOrthogonalDomainVector_mem
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hadj : PreservesAdjointRiccatiDomains H X)
    (z : H.A1.domain) :
    ((unboundedBlockGraphOrthogonalDomainVector H X hadj z :
        (unboundedBlockOperatorCore H).domain) : WithLp 2 (E0 × E1)) ∈
      (unboundedBlockGraph X)ᗮ := by
  rw [mem_unboundedBlockGraph_orthogonal_iff]
  rfl

/-- **The adjoint Riccati equation.**

Invariance of the *orthogonal complement* of the angular graph — the half of
`ReducesSubspace` that plain invariance does not give — is exactly the statement
that `X†` intertwines the two diagonal blocks up to the off-diagonal coupling.

Together with `strongSolvesRiccati_iff_pointwise` this is what makes the
commutator `A₀X†X - X†XA₀` bounded, which is the analytic engine of the sharp
unbounded `tan 2Theta` estimate. -/
theorem adjoint_riccati_of_invariant_orthogonal
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) (hadj : PreservesAdjointRiccatiDomains H X)
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (z : H.A1.domain) :
    H.A0 ⟨(ContinuousLinearMap.adjoint X) (z : E1), hadj z⟩ =
      H.B01 (z : E1) + (ContinuousLinearMap.adjoint X) (H.A1 z) -
        (ContinuousLinearMap.adjoint X)
          (H.B10 ((ContinuousLinearMap.adjoint X) (z : E1))) := by
  have hout := hinv (unboundedBlockGraphOrthogonalDomainVector H X hadj z)
    (unboundedBlockGraphOrthogonalDomainVector_mem H X hadj z)
  rw [mem_unboundedBlockGraph_orthogonal_iff,
    unboundedBlockOperatorCore_apply_fst,
    unboundedBlockOperatorCore_apply_snd] at hout
  -- `hout` says `A₀(-X†z) + B₀₁z = -X†(A₁z + B₁₀(-X†z))`.
  have hfst : TauCeti.LinearPMap.directSumDomainFst H.A0 H.A1
      (unboundedBlockGraphOrthogonalDomainVector H X hadj z) =
      ⟨-(ContinuousLinearMap.adjoint X) (z : E1),
        Submodule.neg_mem _ (hadj z)⟩ := rfl
  have hsnd : TauCeti.LinearPMap.directSumDomainSnd H.A0 H.A1
      (unboundedBlockGraphOrthogonalDomainVector H X hadj z) = z := rfl
  rw [hfst, hsnd] at hout
  have hneg : (⟨-(ContinuousLinearMap.adjoint X) (z : E1),
        Submodule.neg_mem _ (hadj z)⟩ : H.A0.domain) =
      -(⟨(ContinuousLinearMap.adjoint X) (z : E1), hadj z⟩ : H.A0.domain) := rfl
  rw [hneg, LinearPMap.map_neg] at hout
  have hfstcoe :
      ((unboundedBlockGraphOrthogonalDomainVector H X hadj z :
        (unboundedBlockOperatorCore H).domain) :
          WithLp 2 (E0 × E1)).fst =
      -(ContinuousLinearMap.adjoint X) (z : E1) := rfl
  have hsndcoe :
      ((unboundedBlockGraphOrthogonalDomainVector H X hadj z :
        (unboundedBlockOperatorCore H).domain) :
          WithLp 2 (E0 × E1)).snd = (z : E1) := rfl
  rw [hfstcoe, hsndcoe, map_add, map_neg, map_neg] at hout
  linear_combination (norm := module) -hout

end DavisKahanExt
end TauCeti
