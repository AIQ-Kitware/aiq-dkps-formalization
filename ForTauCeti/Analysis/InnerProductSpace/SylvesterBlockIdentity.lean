/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.SylvesterGenerator
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralCutOperator

/-!
# The Sylvester operator on a spectral block

On a block cut out by spectral projections of the two generators, the Sylvester
operator is a scalar plus two small corrections:

`𝒮 Z - (λ - α) Z = (A - λ)|_block ∘ Z - Z ∘ (B - α)|_block`

and both corrections are *bounded* operators of norm at most the block radius
(`specCutOp`).  That is what turns the pointwise Sylvester equation into a
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

## Provenance

*New.*
-/

open scoped InnerProductSpace
open TauCeti.OneParameterUnitaryGroup (generator)

namespace TauCeti
namespace HilbertSchmidt

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The Sylvester operator on a spectral block.**  Both correction terms are
bounded by the block radii, so this converts the pointwise Sylvester equation
into something the Hilbert–Schmidt ideal properties can consume. -/
theorem sylvester_block_identity
    (U : TauCeti.OneParameterUnitaryGroup E) (V : TauCeti.OneParameterUnitaryGroup F)
    (b : HilbertBasis ι ℂ F)
    {SA SB : Set ℝ} (hSA : MeasurableSet SA) (hSB : MeasurableSet SB)
    {MA lam rA : ℝ} (hbndA : ∀ s ∈ SA, |s| ≤ MA) (hrA : 0 ≤ rA)
    (hcrA : ∀ s ∈ SA, |s - lam| ≤ rA)
    {MB alp rB : ℝ} (hbndB : ∀ s ∈ SB, |s| ≤ MB) (hrB : 0 ≤ rB)
    (hcrB : ∀ s ∈ SB, |s - alp| ≤ rB)
    (z : (generator (sylvesterGroup U V b)).domain)
    (hZP : (TauCeti.LinearPMap.specProjection
        (TauCeti.OneParameterUnitaryGroup.isSelfAdjoint_generator U) SA hSA).comp
        (ofLp b (z : lp (fun _ : ι => E) 2)) = ofLp b (z : lp (fun _ : ι => E) 2))
    (hZQ : (ofLp b (z : lp (fun _ : ι => E) 2)).comp
        (TauCeti.LinearPMap.specProjection
          (TauCeti.OneParameterUnitaryGroup.isSelfAdjoint_generator V) SB hSB)
        = ofLp b (z : lp (fun _ : ι => E) 2)) :
    ofLp b (generator (sylvesterGroup U V b) z)
        - ((lam : ℂ) - (alp : ℂ)) • ofLp b (z : lp (fun _ : ι => E) 2)
      = (TauCeti.LinearPMap.specCutOp
            (TauCeti.OneParameterUnitaryGroup.isSelfAdjoint_generator U) SA hSA hrA hcrA).comp
          (ofLp b (z : lp (fun _ : ι => E) 2))
        - (ofLp b (z : lp (fun _ : ι => E) 2)).comp
          (TauCeti.LinearPMap.specCutOp
            (TauCeti.OneParameterUnitaryGroup.isSelfAdjoint_generator V) SB hSB hrB hcrB) := by
  set hA := TauCeti.OneParameterUnitaryGroup.isSelfAdjoint_generator U with hAdef
  set hB := TauCeti.OneParameterUnitaryGroup.isSelfAdjoint_generator V with hBdef
  set Z := ofLp b (z : lp (fun _ : ι => E) 2) with hZ
  set P := TauCeti.LinearPMap.specProjection hA SA hSA with hP
  set Q := TauCeti.LinearPMap.specProjection hB SB hSB with hQ
  have hdense : Dense ((generator V).domain : Set F) := hB.dense_domain
  refine ContinuousLinearMap.ext_on (R₁ := ℂ) (s := ((generator V).domain : Set F))
    (by rwa [Submodule.span_eq]) ?_
  intro x hx
  obtain ⟨hmem, heq⟩ := generator_sylvesterGroup_apply U V b z ⟨x, hx⟩
  -- the left factor: `Z x` sits in the spectral range of `SA`, where `A - lam` is `specCutOp`
  have hZx : Z x ∈ TauCeti.LinearPMap.specRange hA SA hSA := by
    rw [TauCeti.LinearPMap.mem_specRange_iff]
    have := congrArg (fun T : F →L[ℂ] E => T x) hZP
    simpa [hP] using this
  have hZxdom : Z x ∈ (generator U).domain :=
    TauCeti.LinearPMap.mem_domain_of_mem_specRange_of_bounded hA SA hSA hbndA hZx
  have hleft : TauCeti.LinearPMap.specCutOp hA SA hSA hrA hcrA (Z x)
      = generator U ⟨Z x, hZxdom⟩ - (lam : ℂ) • Z x :=
    TauCeti.LinearPMap.specCutOp_apply hA SA hSA hbndA hrA hcrA hZx hZxdom
  -- the right factor, valid at every vector
  obtain ⟨hQx, hright⟩ :=
    TauCeti.LinearPMap.specProjection_apply_sub_smul hB SB hSB hbndB hrB hcrB x
  -- `Q` intertwines `B`, and `Z = Z ∘ Q`, so `Z (B x) = Z (B (Q x))`
  have hQint : generator V ⟨Q x, TauCeti.LinearPMap.specProjection_mem_domain hB SB hSB ⟨x, hx⟩⟩
      = Q (generator V ⟨x, hx⟩) :=
    TauCeti.LinearPMap.specProjection_apply_domain hB SB hSB ⟨x, hx⟩
  have hZQx : ∀ y : F, Z (Q y) = Z y := by
    intro y
    have := congrArg (fun T : F →L[ℂ] E => T y) hZQ
    simpa [hQ] using this
  -- assemble
  have heq' : (ofLp b (generator (sylvesterGroup U V b) z)) x
      = generator U ⟨Z x, hZxdom⟩ - Z (generator V ⟨x, hx⟩) := heq.symm
  have hcut : TauCeti.LinearPMap.specCutOp hB SB hSB hrB hcrB x
      = generator V ⟨Q x, hQx⟩ - (alp : ℂ) • Q x := hright.symm
  have hBQ : Z (generator V ⟨Q x, hQx⟩) = Z (generator V ⟨x, hx⟩) := by
    rw [show (⟨Q x, hQx⟩ : (generator V).domain)
        = ⟨Q x, TauCeti.LinearPMap.specProjection_mem_domain hB SB hSB ⟨x, hx⟩⟩ from rfl,
      hQint, hZQx]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, hleft, heq', hcut,
    map_sub, map_smul, hBQ, hZQx]
  module

end HilbertSchmidt
end TauCeti
