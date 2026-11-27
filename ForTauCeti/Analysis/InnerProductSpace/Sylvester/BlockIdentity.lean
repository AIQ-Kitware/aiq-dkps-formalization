/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Generator
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure

/-!
# The Sylvester operator on a spectral block

On a block cut out by spectral projections of the two generators, the Sylvester
operator is a scalar plus two small corrections:

`𝒮 Z - (λ - α) Z = (A - λ)|_block ∘ Z - Z ∘ (B - α)|_block`

and both corrections are *bounded* operators of norm at most the block radius
(`LinearPMap.spectralCut`).  That is what turns the pointwise Sylvester equation into a
Hilbert–Schmidt estimate: the ideal properties of the energy need bounded
factors, which the pointwise form does not provide.

## Why the identity needs a density argument

`generator_sylvesterGroup_apply` supplies `(𝒮 Z) x = A (Z x) - Z (B x)` only for
`x` in the domain of `B` — that is all an unbounded generator can give.  The
statement wanted is between bounded operators on all of `F`.  Both sides are
continuous and the domain is dense, so `ContinuousLinearMap.ext_on` closes the
gap.

The one step that is not formal: `Z (B x) = Z (B (Q x))`, which holds because
`Z = Z ∘ Q` and `Q` intertwines `B` (`specProjection_apply_domain`).  Without
the intertwining the two sides differ by `Z ((1 - Q) B x)`, which is not small.

## Sources

The block form of the Sylvester operator, and its use to reduce a spectral-gap
estimate to one block at a time, follow Bhatia--Davis--McIntosh; see
`prose/distilled_literature/BhatiaDavisMcIntosh1983_spectral_subspaces_sylvester.tex`.

## Provenance

*New.*

Moved from
`ForTauCeti/Analysis/InnerProductSpace/SylvesterBlockIdentity.lean` to
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/BlockIdentity.lean`.  The `Sylvester/`
directory already held `Basic`, `Interval`, `SpectralDistance` and `Internal/`, while
six siblings of the same family used a flat `Sylvester*` prefix in the directory above;
one family now has one convention.  Path change and import repoint only — no statement,
signature, proof, attribute, declaration name or namespace changed.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace HilbertSchmidt

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The Sylvester operator on a spectral block.**  Both correction terms are
bounded by the block radii, so this converts the pointwise Sylvester equation
into something the Hilbert–Schmidt ideal properties can consume.

The self-adjointness proofs are taken as *arguments*, together with the
identifications `(U.val.stoneGenerator U.property) = A` and `(V.val.stoneGenerator V.property) =
      B`, rather than being
manufactured internally from `isSelfAdjoint_generator`.  That is deliberate: the
consumer has a given `hA : IsSelfAdjoint A` and works with projections of `A`,
and `isSelfAdjoint_generator U` proves a different proposition — equal only
across `(U.val.stoneGenerator U.property) = A`. Since `LinearPMap.spectralPVM`
takes the proof as an argument, manufacturing it here would push a dependent rewrite through every
projection, domain membership and cut operator at the call site.  Taking it as a
hypothesis does the transport once, here. -/
theorem sylvester_block_identity
    (U : {G : TauCeti.Semigroups.StronglyContinuousGroup E // G.IsUnitary}) (V : {G :
          TauCeti.Semigroups.StronglyContinuousGroup F // G.IsUnitary})
    (b : HilbertBasis ι ℂ F)
    {A : E →ₗ.[ℂ] E} {Bop : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint Bop)
    (hUA : (U.val.stoneGenerator U.property) = A) (hVB : (V.val.stoneGenerator V.property) = Bop)
    {SA SB : Set ℝ} (hSA : MeasurableSet SA) (hSB : MeasurableSet SB)
    {MA lam rA : ℝ} (hbndA : ∀ s ∈ SA, |s| ≤ MA) (hrA : 0 ≤ rA)
    (hcrA : ∀ s ∈ SA, |s - lam| ≤ rA)
    {MB alp rB : ℝ} (_hbndB : ∀ s ∈ SB, |s| ≤ MB) (hrB : 0 ≤ rB)
    (hcrB : ∀ s ∈ SB, |s - alp| ≤ rB)
    (z : ((sylvesterGroup U V b).val.stoneGenerator (sylvesterGroup U V b).property).domain)
    (hZP : ((A.spectralPVM hA).proj SA hSA).comp
        (b.columnOperator (z : lp (fun _ : ι => E) 2)) =
        b.columnOperator (z : lp (fun _ : ι => E) 2))
    (hZQ : (b.columnOperator (z : lp (fun _ : ι => E) 2)).comp
        ((Bop.spectralPVM hB).proj SB hSB)
        = b.columnOperator (z : lp (fun _ : ι => E) 2)) :
    b.columnOperator ((sylvesterGroup U V b).val.stoneGenerator (sylvesterGroup U V b).property z)
        - ((lam : ℂ) - (alp : ℂ)) • b.columnOperator (z : lp (fun _ : ι => E) 2)
      = (A.spectralCut hA SA hSA lam rA hrA hcrA).comp
          (b.columnOperator (z : lp (fun _ : ι => E) 2))
        - (b.columnOperator (z : lp (fun _ : ι => E) 2)).comp
          (Bop.spectralCut hB SB hSB alp rB hrB hcrB) := by
  set Z := b.columnOperator (z : lp (fun _ : ι => E) 2) with hZ
  set P := (A.spectralPVM hA).proj SA hSA with hP
  set Q := (Bop.spectralPVM hB).proj SB hSB with hQ
  have hdomV : ((V.val.stoneGenerator V.property)).domain = Bop.domain := congrArg
        LinearPMap.domain hVB
  have hdense : Dense (((V.val.stoneGenerator V.property)).domain : Set F) := by
    rw [hdomV]; exact hB.dense_domain
  refine ContinuousLinearMap.ext_on (R₁ := ℂ) (s := (((V.val.stoneGenerator V.property)).domain :
        Set F))
    (by rwa [Submodule.span_eq]) ?_
  intro x hx
  have hx' : x ∈ Bop.domain := (le_of_eq hdomV) hx
  obtain ⟨hmem, heq⟩ := generator_sylvesterGroup_apply U V b z ⟨x, hx⟩
  -- the left factor
  have hZx : Z x ∈ ((A.spectralPVM hA).proj SA hSA).range := by
    rw [← Submodule.starProjection_eq_self_iff, ProjValMeasure.starProjection_range_proj]
    have := congrArg (fun T : F →L[ℂ] E => T x) hZP
    simpa [hP] using this
  have hZxdom : Z x ∈ A.domain :=
    TauCeti.LinearPMap.mem_domain_of_mem_specRange_of_bounded hA SA hSA hbndA hZx
  have hcutA := hA.mem_graph_spectralCut SA hSA lam rA hrA hcrA (Z x)
  have hfixA : (A.spectralPVM hA).proj SA hSA (Z x) = Z x := by
    exact
      (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap ((A.spectralPVM hA).proj_idem SA hSA))
      (x := (Z x))).mp hZx
  rw [hfixA] at hcutA
  have hactA := A.mem_graph_snd_inj (A.mem_graph ⟨Z x, hZxdom⟩) hcutA rfl
  have hleft : A.spectralCut hA SA hSA lam rA hrA hcrA (Z x) =
      A ⟨Z x, hZxdom⟩ - (lam : ℂ) • Z x := by
    rw [hactA, add_sub_cancel_right]
  have hUval : (U.val.stoneGenerator U.property) ⟨Z x, hmem⟩ = A ⟨Z x, hZxdom⟩ :=
    (LinearPMap.ext_iff.mp hUA).2 (x := Z x) (hf := hmem) (hg := hZxdom)
  have hVval : (V.val.stoneGenerator V.property) ⟨x, hx⟩ = Bop ⟨x, hx'⟩ :=
    (LinearPMap.ext_iff.mp hVB).2 (x := x) (hf := hx) (hg := hx')
  -- the right factor, valid at every vector
  have hcutB := hB.mem_graph_spectralCut SB hSB alp rB hrB hcrB x
  have hQx : Q x ∈ Bop.domain := by
    simpa only [hQ] using
      _root_.LinearPMap.mem_domain_of_mem_graph hcutB
  have hactB := Bop.mem_graph_snd_inj (Bop.mem_graph ⟨Q x, hQx⟩) hcutB rfl
  have hright : Bop ⟨Q x, hQx⟩ - (alp : ℂ) • Q x =
      Bop.spectralCut hB SB hSB alp rB hrB hcrB x := by
    rw [hactB, add_sub_cancel_right]
  have hQint : Bop ⟨Q x, (hB.intertwines_spectralPVM_proj SB hSB).mem_domain ⟨x, hx'⟩⟩
      = Q (Bop ⟨x, hx'⟩) :=
    ((hB.intertwines_spectralPVM_proj SB hSB).apply_eq ⟨x, hx'⟩).symm
  have hZQx : ∀ y : F, Z (Q y) = Z y := by
    intro y
    have := congrArg (fun T : F →L[ℂ] E => T y) hZQ
    simpa [hQ] using this
  -- assemble
  have heq' : (b.columnOperator ((sylvesterGroup U V b).val.stoneGenerator (sylvesterGroup U V
        b).property z)) x
      = A ⟨Z x, hZxdom⟩ - Z (Bop ⟨x, hx'⟩) := by
    rw [← heq, hUval, hVval]
  have hcut : Bop.spectralCut hB SB hSB alp rB hrB hcrB x
      = Bop ⟨Q x, hQx⟩ - (alp : ℂ) • Q x := hright.symm
  have hBQ : Z (Bop ⟨Q x, hQx⟩) = Z (Bop ⟨x, hx'⟩) := by
    rw [show (⟨Q x, hQx⟩ : Bop.domain)
        = ⟨Q x, (hB.intertwines_spectralPVM_proj SB hSB).mem_domain ⟨x, hx'⟩⟩ from rfl,
      hQint, hZQx]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, hleft, heq', hcut,
    map_sub, map_smul, hBQ, hZQx]
  module

end HilbertSchmidt
end TauCeti
