/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Group

/-!
# The generator of the Sylvester flow is `Z ↦ A Z - Z B`

`SylvesterGroup.lean` shows that `W t Z = U t ∘ Z ∘ (V t)⋆` is a one-parameter
unitary group on the Hilbert–Schmidt space and that its generator is
self-adjoint.  This module identifies what that generator *is*.

`generator_sylvesterGroup_apply` — if `z` lies in the domain of
`(sylvesterGroup U V b).val.stoneGenerator (sylvesterGroup U V b).property` and `x` lies in the
      domain of `(V.val.stoneGenerator V.property)`,
then `Z x` lies in the domain of `(U.val.stoneGenerator U.property)`, and

`A (Z x) - Z (B x) = C x`

where `Z` is the operator represented by `z`, `C` the one represented by
`(sylvesterGroup U V b).val.stoneGenerator (sylvesterGroup U V b).property z`, and `A`, `B` the
      generators of `U`, `V`.

## Only one direction, on purpose

The converse — a characterisation of the generator's domain — is the theorem
that the generator is the closure of `A ⊗ 1 - 1 ⊗ B`, and nothing in the tree
needs it.  The defect-first Sylvester theorem consumes exactly the direction
proved here, and it consumes it in this shape *because* the conclusion
**produces** the domain membership `Z x ∈ dom A` instead of assuming it.  That
is what lets the paper theorem avoid assuming its solution is Hilbert–Schmidt
before proving that it is.

## The argument

Split the difference quotient of the flow at a vector `x`:

`(U t (Z (V (-t) x)) - Z x)/(i t) = U t ((Z (V (-t) x) - Z x)/(i t)) + (U t (Z x) - Z x)/(i t)`

The left-hand side converges to `C x`, because `z` is in the generator domain
and `ℓ²` convergence dominates pointwise convergence — the operator norm of
`b.columnOperator h` is at most `‖h‖`.  The first right-hand term converges to `-Z (B x)`,
because `Z` is bounded and `U t → 1` strongly.  So the *second* term converges,
and that is precisely the assertion that `Z x` lies in the domain of `A`, with
the value `C x + Z (B x)`.

## Sources

That the generator of the Sylvester flow is `Z ↦ A Z - Z B` is the semigroup form
of Rosenblum's argument, and the `π / 2` mass that makes it sharp is distilled in
`prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`.
The donor derived the same equation from a tensor factorisation of the flow; none
of that is used here, as the provenance note records.

## Provenance

*New.*  The donor derives the same equation from the tensor factorisation of the
flow; nothing of that is used.

Moved from
`ForTauCeti/Analysis/InnerProductSpace/SylvesterGenerator.lean` to
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Generator.lean`.  The `Sylvester/`
directory already held `Basic`, `Interval`, `SpectralDistance` and `Internal/`, while
six siblings of the same family used a flat `Sylvester*` prefix in the directory above;
one family now has one convention.  Path change and import repoint only — no statement,
signature, proof, attribute, declaration name or namespace changed.
-/

public section

open TauCeti.Semigroups.StronglyContinuousGroup (stoneDiffQuot_apply complexOperator_apply)

open scoped ENNReal NNReal
open Filter Topology Complex

namespace TauCeti
namespace HilbertSchmidt


variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

section Sylvester

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (U : {G : TauCeti.Semigroups.StronglyContinuousGroup E // G.IsUnitary}) (V : {G :
      TauCeti.Semigroups.StronglyContinuousGroup F // G.IsUnitary})
variable (b : HilbertBasis ι ℂ F)

/-- The negated, time-reversed difference quotient converges to the generator. -/
theorem tendsto_stoneDiffQuot_neg_time (x : ((V.val.stoneGenerator V.property)).domain) :
    Tendsto (fun t : ℝ => ((I * (t : ℂ))⁻¹) • (V.val.complexOperator V.property (-t) (x : F) - (x
          : F)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-((V.val.stoneGenerator V.property) x))) := by
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    exact (continuous_neg.tendsto' 0 0 neg_zero).inf
      (tendsto_principal_principal.2 fun t ht => by simpa using ht)
  refine (((V.val.tendsto_stoneDiffQuot V.property x).comp hneg).neg).congr fun t => ?_
  rw [Function.comp_apply, stoneDiffQuot_apply, ← neg_smul]
  congr 1
  push_cast
  rw [mul_neg, inv_neg, neg_neg]

/-- **The generator of the Sylvester flow satisfies the Sylvester equation.**

If `z` is in the domain of the flow's generator and `x` is in the domain of
`(V.val.stoneGenerator V.property)`, then `Z x` is in the domain of `(U.val.stoneGenerator
      U.property)` and

`A (Z x) - Z (B x) = C x`,

with `Z` and `C` the operators represented by `z` and by the generator applied
to `z`.  The domain membership is a *conclusion*, not a hypothesis. -/
@[simp]
theorem generator_sylvesterGroup_apply
    (z : ((sylvesterGroup U V b).val.stoneGenerator (sylvesterGroup U V b).property).domain) (x :
          ((V.val.stoneGenerator V.property)).domain) :
    ∃ hmem : b.columnOperator (z : lp (fun _ : ι => E) 2) (x : F) ∈ ((U.val.stoneGenerator
          U.property)).domain,
      (U.val.stoneGenerator U.property) ⟨b.columnOperator (z : lp (fun _ : ι => E) 2) (x : F), hmem⟩
          - b.columnOperator (z : lp (fun _ : ι => E) 2) ((V.val.stoneGenerator V.property) x)
        = b.columnOperator ((sylvesterGroup U V b).val.stoneGenerator (sylvesterGroup U V
              b).property z) (x : F) := by
  set Z := b.columnOperator (z : lp (fun _ : ι => E) 2) with hZ
  set C := b.columnOperator ((sylvesterGroup U V b).val.stoneGenerator (sylvesterGroup U V
        b).property z) with hC
  -- (1) the flow's difference quotient, evaluated at `x`, converges to `C x`
  have hquot : Tendsto
      (fun t : ℝ =>
        b.columnOperator ((sylvesterGroup U V b).val.stoneDiffQuot (z : lp (fun _ : ι => E) 2) t)
              (x : F))
      (𝓝[≠] (0 : ℝ)) (𝓝 (C (x : F))) := by
    have hc : Continuous (fun f : lp (fun _ : ι => E) 2 =>
        b.columnOperator f (x : F)) :=
      b.columnOperator.continuous.clm_apply continuous_const
    exact (hc.tendsto _).comp ((sylvesterGroup U V b).val.tendsto_stoneDiffQuot (sylvesterGroup U
          V b).property z)
  -- (2) that quotient splits into the two pieces of the Sylvester expression
  have hsplit : ∀ t : ℝ,
      b.columnOperator ((sylvesterGroup U V b).val.stoneDiffQuot (z : lp (fun _ : ι => E) 2) t) (x
            : F)
        = U.val.complexOperator U.property t (Z (((I * (t : ℂ))⁻¹) • (V.val.complexOperator
              V.property (-t) (x : F) - (x : F))))
          + U.val.stoneDiffQuot (Z (x : F)) t := by
    intro t
    simp only [stoneDiffQuot_apply, map_smul, map_sub, sylvesterGroup_apply,
      columnOperator_sylvesterFun, conjOp, complexOperator_apply]
    simp only [smul_apply, sub_apply, ContinuousLinearMap.comp_apply,
      complexOperator_apply, ← hZ]
    rw [← smul_add]
    congr 1
    abel
  -- (3) the first piece converges to `-Z (B x)`
  have hfirst : Tendsto
      (fun t : ℝ => U.val.complexOperator U.property t (Z (((I * (t : ℂ))⁻¹) •
            (V.val.complexOperator V.property (-t) (x : F) - (x : F)))))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-(Z ((V.val.stoneGenerator V.property) x)))) := by
    have hw := (Z.continuous.tendsto (-((V.val.stoneGenerator V.property) x))).comp
      (tendsto_stoneDiffQuot_neg_time V x)
    have h := U.val.tendsto_apply (tendsto_id.mono_left nhdsWithin_le_nhds) hw
    simpa only [U.val.map_zero_apply, Function.comp_def, id_eq, map_neg,
      complexOperator_apply] using h
  -- (4) hence the second piece converges, which is the domain membership
  have hsecond : Tendsto (fun t : ℝ => U.val.stoneDiffQuot (Z (x : F)) t) (𝓝[≠] (0 : ℝ))
      (𝓝 (C (x : F) + Z ((V.val.stoneGenerator V.property) x))) := by
    have hdiff : Tendsto (fun t : ℝ =>
        b.columnOperator ((sylvesterGroup U V b).val.stoneDiffQuot (z : lp (fun _ : ι => E) 2) t)
              (x : F)
          - U.val.complexOperator U.property t (Z (((I * (t : ℂ))⁻¹) • (V.val.complexOperator
                V.property (-t) (x : F) - (x : F)))))
        (𝓝[≠] (0 : ℝ)) (𝓝 (C (x : F) + Z ((V.val.stoneGenerator V.property) x))) := by
      simpa only [sub_neg_eq_add] using hquot.sub hfirst
    refine hdiff.congr fun t => ?_
    rw [hsplit t]
    abel
  have hmem : Z (x : F) ∈ (U.val.stoneGenerator U.property).domain :=
    U.val.mem_stoneGenerator_domain_of_tendsto U.property hsecond
  refine ⟨hmem, ?_⟩
  have hval : (U.val.stoneGenerator U.property) ⟨Z (x : F), hmem⟩ = C (x : F) + Z
        ((V.val.stoneGenerator V.property) x) :=
    tendsto_nhds_unique (U.val.tendsto_stoneDiffQuot U.property ⟨Z (x : F), hmem⟩) hsecond
  rw [hval]
  abel

end Sylvester

end HilbertSchmidt
end TauCeti
