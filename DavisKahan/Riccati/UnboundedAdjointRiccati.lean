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

/-- The angular operator maps the second diagonal domain into the first.

This is the adjoint-side counterpart of `PreservesRiccatiDomains`, and it has
exactly the same status: a genuine hypothesis, not a consequence of reduction.
`ContractiveReducingGraphSelection` already records the forward version as a
separate field for this reason ("domain preservation is a separate field
because it is not a consequence of the ambient graph equality alone"), and the
adjoint side is no better.

Concretely, reduction *does* give something, just not enough. Writing
`R₀ := (I + X†X)⁻¹`, the projection-preserves-domain half of `ReducesSubspace`
applied to `(u, 0)` and to `(0, z)` yields

```
R₀ preserves dom A₀,      and      R₀ X† z ∈ dom A₀  for z ∈ dom A₁.
```

Recovering `X† z = (I + X†X)(R₀ X† z)` from the second then needs `X†X` to
preserve `dom A₀` — which is `gram_mem_domain`, itself a consequence of the
very statement being derived. The loop does not close, and the symmetric
attempt through `R₁ := (I + XX†)⁻¹` fails the same way: `R₁` preserves
`dom A₁`, but showing it *surjects* onto `dom A₁` again needs `X† z ∈ dom A₀`.

So this is carried as an explicit hypothesis throughout. It is not a hidden
seam: it is the adjoint twin of a hypothesis the repository already assumes. -/
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

/-- The commutator of the first diagonal block with the Gram operator `X†X`.

Both Riccati equations conspire so that this commutator, which a priori pairs an
unbounded operator with a bounded one, is itself **bounded**: writing `K = B₀₁X`
and `T = X†X` it is `(I + T)K - K†(I + T)`, so `‖G‖ ≤ 2(‖B₀₁‖ + ‖B₁₀‖)`. -/
noncomputable def riccatiGramCommutator
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : E0 →L[𝕜] E0 :=
  H.B01 ∘L X + ((ContinuousLinearMap.adjoint X) ∘L X) ∘L (H.B01 ∘L X) -
    ((ContinuousLinearMap.adjoint X) ∘L H.B10) -
      ((ContinuousLinearMap.adjoint X) ∘L H.B10) ∘L
        ((ContinuousLinearMap.adjoint X) ∘L X)

/-- The Gram operator of a reducing Riccati selection preserves the first
diagonal domain. -/
theorem gram_mem_domain
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hdom : PreservesRiccatiDomains H X)
    (hadj : PreservesAdjointRiccatiDomains H X) (x : H.A0.domain) :
    (ContinuousLinearMap.adjoint X) (X (x : E0)) ∈ H.A0.domain :=
  hadj ⟨X (x : E0), hdom x⟩

/-- **The Riccati commutator identity.**

`A₀` commutes with the Gram operator `X†X` up to the *bounded* operator
`riccatiGramCommutator`.  This is ticket T1.2 of the sharp unbounded
`tan 2Theta` lane: it is the reason the whole argument can be run with band
projections of `X†X` while keeping the unbounded block under control. -/
theorem gram_commutator_eq
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hdom : PreservesRiccatiDomains H X)
    (hadj : PreservesAdjointRiccatiDomains H X)
    (hinv : TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorCore H)
      (unboundedBlockGraph X)ᗮ)
    (hric : ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ + H.B10 (x : E0) =
        X (H.A0 x + H.B01 (X (x : E0))))
    (x : H.A0.domain) :
    H.A0 ⟨(ContinuousLinearMap.adjoint X) (X (x : E0)),
        gram_mem_domain H hdom hadj x⟩ =
      (ContinuousLinearMap.adjoint X) (X (H.A0 x)) +
        riccatiGramCommutator H X (x : E0) := by
  have hz := adjoint_riccati_of_invariant_orthogonal H X hadj hinv
    ⟨X (x : E0), hdom x⟩
  have hA1 : H.A1 ⟨X (x : E0), hdom x⟩ =
      X (H.A0 x + H.B01 (X (x : E0))) - H.B10 (x : E0) := by
    rw [← hric x]; abel
  rw [hA1, map_sub, map_add] at hz
  simp only [riccatiGramCommutator, add_apply, sub_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hz]
  simp only [map_add]
  abel

/-- The Riccati commutator is bounded by the off-diagonal coupling alone: no
norm of a diagonal block appears.  This is what allows band projections of
`X†X` to be used against the unbounded blocks. -/
theorem norm_riccatiGramCommutator_le
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hX : ‖X‖ ≤ 1) :
    ‖riccatiGramCommutator H X‖ ≤ 2 * (‖H.B01‖ + ‖H.B10‖) := by
  have hXa : ‖(ContinuousLinearMap.adjoint X)‖ = ‖X‖ :=
    ContinuousLinearMap.adjoint.norm_map X
  have hX0 : (0 : ℝ) ≤ ‖X‖ := norm_nonneg X
  have hB01 : (0 : ℝ) ≤ ‖H.B01‖ := norm_nonneg _
  have hB10 : (0 : ℝ) ≤ ‖H.B10‖ := norm_nonneg _
  have h1 : ‖H.B01 ∘L X‖ ≤ ‖H.B01‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    nlinarith
  have h2 : ‖((ContinuousLinearMap.adjoint X) ∘L X) ∘L (H.B01 ∘L X)‖ ≤
      ‖H.B01‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hc : ‖(ContinuousLinearMap.adjoint X) ∘L X‖ ≤ 1 := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [hXa]; nlinarith
    nlinarith [norm_nonneg (H.B01 ∘L X), norm_nonneg
      ((ContinuousLinearMap.adjoint X) ∘L X)]
  have h3 : ‖(ContinuousLinearMap.adjoint X) ∘L H.B10‖ ≤ ‖H.B10‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [hXa]; nlinarith
  have h4 : ‖((ContinuousLinearMap.adjoint X) ∘L H.B10) ∘L
      ((ContinuousLinearMap.adjoint X) ∘L X)‖ ≤ ‖H.B10‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hc : ‖(ContinuousLinearMap.adjoint X) ∘L X‖ ≤ 1 := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [hXa]; nlinarith
    nlinarith [norm_nonneg ((ContinuousLinearMap.adjoint X) ∘L H.B10),
      norm_nonneg ((ContinuousLinearMap.adjoint X) ∘L X)]
  refine (norm_sub_le _ _).trans ?_
  have h5 := (norm_sub_le
    (H.B01 ∘L X + ((ContinuousLinearMap.adjoint X) ∘L X) ∘L (H.B01 ∘L X))
    ((ContinuousLinearMap.adjoint X) ∘L H.B10))
  have h6 := norm_add_le (H.B01 ∘L X)
    (((ContinuousLinearMap.adjoint X) ∘L X) ∘L (H.B01 ∘L X))
  linarith

end DavisKahanExt
end TauCeti
