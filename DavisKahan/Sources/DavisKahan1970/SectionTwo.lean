/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation
import DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbient
import DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbientReal
import DavisKahan.Sources.DavisKahan1970.SinTwoTheta
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaUnboundedDirectedResidual
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaUnboundedDirectedResidualReal
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaDirectedAngle
import DavisKahan.Sources.DavisKahan1970.TanThetaDirectedUnbounded
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedAmbientExact
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExactReal

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The four Section 2 theorems, in one place

Davis--Kahan 1970 opens with four unnumbered theorems -- `sin Θ`, `tan Θ`, `sin 2Θ`,
`tan 2Θ` -- and the rest of the paper is their proof, their sharpness and their
consequences.  **This module is the public inventory of those four, over both scalar
fields, and is the module to cite.**

## The table

Three of the four print *two* conclusions, a directed one bounding the trial-side angle
by the residual and an ambient one bounding the whole-space angle by the perturbation.
The names say which.

| result | directed clause | ambient clause |
| --- | --- | --- |
| `sin Θ` | `sinTheta`, `sinTheta_complex`, `sinTheta_real` | -- (one printed conclusion) |
| `tan Θ` | `tanTheta_directed_complex`, `tanTheta_directed_real` | `tanTheta_ambient_complex`, `tanTheta_ambient_real` |
| `sin 2Θ` | `sinTwoTheta_directed_complex`, `sinTwoTheta_directed_real` | `sinTwoTheta_ambient_complex`, `sinTwoTheta_ambient_real` |
| `tan 2Θ` | `tanTwoTheta_directed_complex`, `tanTwoTheta_directed_real` | `tanTwoTheta_ambient_complex`, `tanTwoTheta_ambient_real` |

`sinTwoTheta_bothConclusions_{complex,real}` and `tanTwoTheta_bothConclusions_{complex,real}`
state both clauses of one result under one set of separation hypotheses, so a reviewer has a
single name to point at.

The unqualified `tanTheta_{complex,real}`, `sinTwoTheta_{complex,real}` and
`tanTwoTheta_{complex,real}` are **deprecated**.  They were not uniform -- two of the three
named the ambient clause and one the directed -- and each now carries a `@[deprecated]`
pointing at the name that says which.  They survive only because the standalone Davis--Kahan
submission repository under `submodules/` still consumes them.

## `sinTheta` is bound; the other three short names are reserved

A short unqualified name is bound only to a declaration that is **both** scalar-generic over
`RCLike 𝕜` **and** at the printed source scope.  `SectionTwo.sinTheta` satisfies that;
`SectionTwo.tanTheta`, `.sinTwoTheta` and `.tanTwoTheta` name nothing, because no such
declaration exists for those three yet.  Binding a short name to a complex-only statement is
what once made `SectionTwo.sinTheta` read as the canonical theorem when it was the complex
one, so the three stay empty.  Which of the four are bound is recorded structurally, in
`section_two_short_names` in the result inventory, and checked against this file -- a prose
copy of that fact went stale once and is deliberately not restated here.

## What these names carry

Each is an `alias`, so each has exactly the type of the declaration it names: an unbounded
self-adjoint `LinearPMap` ambient operator, arbitrary Hilbert dimension, an arbitrary source
unitarily invariant norm, both printed conclusions where the result has two, no capability
class, no finite-dimensional hypothesis and no proof vehicle in the conclusion.
`SectionTwoUsage.lean` calls each from ordinary operator-theory hypotheses, so the advertised
entry points are compiler-checked to be reachable without building Sylvester witnesses,
reflection blocks or spectral reflections by hand.

The tangent endpoints additionally *conclude* their own pole exclusion, so a reader can see
from the type that the object bounded is the paper's tangent and not the value Mathlib's
totalised `cfc` assigns at a quarter turn.

## What is deliberately not here

Presentation forms, finite-dimensional specializations, operator-norm statements, bundled
problem entry points and the proofs' own block representatives all live in the modules that
own them and are registered separately in the census.  This module holds names, not
mathematics.

The history of how these names were arrived at -- which bindings were wrong, which clause an
alias used to point at, and what each repair changed -- is in Git history and in the
`review_note` fields of the four Section 2 rows of
`dev/davis-kahan-1970-formalization-result-inventory.json`.  It used to be here, and it made
the file long enough that the table above was hard to find.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), 1--46, Section 2.
-/

namespace TauCeti
namespace DavisKahan1970
namespace SectionTwo


/-! ## `sin Θ` -/

/-- **Davis--Kahan 1970, the `sin Θ` theorem, over an arbitrary `RCLike` field.**

The scalar-generic endpoint at the printed source scope: unbounded self-adjoint
ambient `LinearPMap`, arbitrary Hilbert dimension, the whole
`FormBoundedSylvesterGap`, an arbitrary `SymmetricNormingFunction`, and both
printed conclusions.  **This is the theorem to cite.**  Its hypotheses are the
paper's; the analytic capabilities its proof runs on -- a min-max lower bound and
the unbounded Sylvester Ky Fan estimate -- hold at every `RCLike` field and are
supplied by instance search, so they do not appear in the signature.

`sinTheta_complex` and `sinTheta_real` below are this statement at the two fields
Davis and Kahan write about.  They are corroboration, and convenient when a fixed
field is already in hand. -/
alias sinTheta := DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike

/-- **Davis--Kahan 1970, the `sin Θ` theorem, over `ℂ`.**

`δ · N(sin Θ₀) ≤ N(R)` with `sin Θ₀ = (I - F₀F₀⋆) E₀`, together with membership of
`sin Θ₀` in the norm's ideal.  Unbounded self-adjoint ambient operator, arbitrary
Hilbert dimension, the whole `FormBoundedSylvesterGap` rather than one of its
branches, and an arbitrary source unitarily invariant norm.

`DavisKahan1970.sinTheta_unbounded_intervalExterior_symmetricNorming_complex` states the same theorem with
the gap written out as the printed interval/exterior separation. -/
alias sinTheta_complex := DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex

/-- **Davis--Kahan 1970, the `sin Θ` theorem, over `ℝ`.**

The real sibling of `sinTheta`, with the same argument list, the same full gap
scope and the same two conclusions.  The descent from the complex case happens
inside the proof and is not visible in the statement. -/
alias sinTheta_real := DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_real

/-! ## `tan Θ` -/

/-- **Davis--Kahan 1970, the `tan Θ` theorem, over `ℂ` -- the AMBIENT clause.**

The printed `tan Θ` theorem has two boxed conclusions.  This name is the second,
`δ N(tan Θ) ≤ N(H)`; the first, `δ N(tan Θ₀) ≤ N(R)`, is `tanTheta_directed_complex`.
The pair is the whole result; neither alone is.

`δ · N(tan Θ) ≤ N(H)` on the ambient tangent `tanAngleOperatorC U V`, with
ideal membership, for an unbounded self-adjoint `A`, its unbounded Ritz pair on
the trial subspace `U`, and a subspace `V` whose complement reduces `A`.

The caller supplies the mathematics -- semiboundedness of the compression above
`α`, coercivity `α + δ` on the unwanted subspace, the standing crossed-defect
condition (3.5) of Section 3, and the Rayleigh--Ritz residual identity -- and
nothing else: the structural facts live in `DavisKahan.UnboundedRitzPair` and
`DavisKahan.ReducingComplement`. -/
@[deprecated "The unqualified clause names are not uniform; use `tanTheta_ambient_complex`, which says which of the two printed conclusions it is." (since := "2026-09-05")]
alias tanTheta_complex := tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_complex

/-- **Davis--Kahan 1970, the `tan Θ` theorem, over `ℝ` -- the AMBIENT clause.**

Its directed partner is `tanTheta_directed_real`.

The real sibling of `tanTheta_ambient_complex`, on the real ambient tangent
`tanAngleOperatorR U V`.  Space, operator, subspaces, perturbation, angle and
gauge are all real; only the Appendix Ky Fan passage is proved by
complexification, at the level where approximation numbers are preserved
exactly. -/
@[deprecated "The unqualified clause names are not uniform; use `tanTheta_ambient_real`, which says which of the two printed conclusions it is." (since := "2026-09-05")]
alias tanTheta_real := tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_real

/-! ## `sin 2Θ` -/

/-- **Davis--Kahan 1970, the `sin 2Θ` theorem, over `ℂ` -- the DIRECTED clause.**

The printed `sin 2Θ` theorem has two boxed conclusions.  This name is the first,
`δ N(sin 2Θ₀) ≤ 2 N(R)`, on the printed trial residual `R = A E₀ - E₀ A₀`; the
ambient one, `δ N(sin 2Θ) ≤ 2 N(H)`, is `sinTwoTheta_ambient_complex`.
`sinTwoTheta_bothConclusions_complex` below states both together.

The conclusion is on `Angle.directedSinTwoAngleOperator V U` with `V` the trial
subspace and `U` the spectral subspace whose two blocks the gap separates: that is
the paper's `Θ₀`, whose sine is `Q^⊥ E₀` in the source's own notation, and it is
the trial-side object.  Not the proof's overlap block, and not the other ordering
of the pair.

Until 2026-09-04 this alias named
`sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex`, whose
right-hand side is `2 N(E)` for the full bounded perturbation `E`.  That is a
different source quantity from the printed residual `R`; that theorem is retained
as a derived perturbation-norm corollary and is no longer presented as this
clause. -/
@[deprecated "The unqualified clause names are not uniform; use `sinTwoTheta_directed_complex`, which says which of the two printed conclusions it is." (since := "2026-09-05")]
alias sinTwoTheta_complex := sinTwoTheta_directed_unboundedResidual_symmetricNorming_complex

/-- **Davis--Kahan 1970, the `sin 2Θ` theorem, over `ℝ` -- the DIRECTED clause.**

Its ambient partner is `sinTwoTheta_ambient_real`, and `sinTwoTheta_bothConclusions_real`
states both together.

The real sibling of `sinTwoTheta_complex`: the printed trial residual on the right,
`FormBoundedSylvesterGap` for the separation, and the conclusion on the real directed
double-angle sine of the real pair in the trial-side ordering.  Nothing here is read
in a complexification. -/
@[deprecated "The unqualified clause names are not uniform; use `sinTwoTheta_directed_real`, which says which of the two printed conclusions it is." (since := "2026-09-05")]
alias sinTwoTheta_real := sinTwoTheta_directed_unboundedResidual_symmetricNorming_real

/-! ## The two printed clauses, named

The two clauses of a theorem are different statements -- a different angle object,
and the trial residual rather than the ambient perturbation on the right -- so each
gets its own name rather than being folded into the other with irrelevant
hypotheses.  Every name below says which clause it is.

The six unqualified legacy names are **deprecated since 2026-09-05** (finding F6.6 of the
2026-09-04 hostile review).  They were not uniform, and a reader had to guess:
`tanTheta_{complex,real}` and `tanTwoTheta_{complex,real}` name the AMBIENT clause while
`sinTwoTheta_{complex,real}` names the DIRECTED one.  Each now carries a `@[deprecated]`
attribute pointing at its `_ambient_` or `_directed_` name.  They are retained only because
the standalone Davis--Kahan submission repository under `submodules/` still consumes them;
delete them once that repository has been refreshed. -/

/-- **`tan Θ`, ambient clause, over `ℂ`**: `δ N(tan Θ) ≤ N(H)`. -/
alias tanTheta_ambient_complex := tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_complex

/-- **`tan Θ`, ambient clause, over `ℝ`**. -/
alias tanTheta_ambient_real := tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_real

/-- **`tan Θ`, directed clause, over `ℂ`**: `δ N(tan Θ₀) ≤ N(R)` with the paper's residual
`R` of (1.8) on the right, and with the representative *constructed* rather than supplied.

Retargeted 2026-09-05.  Until then this named
`tanTheta_directed_unboundedTrial_symmetricNorming_complex`, which assumes the perturbed
operator has no spectrum in `(α, α + δ)` and compares against the spectral subspace below
`α` -- a specialization the printed theorem does not impose (finding F1 of the 2026-09-04
hostile review). -/
alias tanTheta_directed_complex :=
  tanTheta_directed_unboundedRitz_symmetricNorming_exists_complex

/-- **`tan Θ`, directed clause, over `ℝ`**, likewise with the representative constructed. -/
alias tanTheta_directed_real :=
  tanTheta_directed_unboundedRitz_symmetricNorming_exists_real

/-- **`sin 2Θ`, directed clause, over `ℂ`**: `δ N(sin 2Θ₀) ≤ 2 N(R)`, on the paper's
own trial-side directed double-angle sine.

Until 2026-09-04 this named the `blockRepresentative` theorem, whose conclusion is
on `sinTwoThetaIdealBlock U V` -- a one-sided block, not an angle.  That theorem is
the proof's own statement and is retained;
`Angle.sinTwoThetaIdealBlock_hasSameApproximationNumbers_trialSide` is what carries
it to the angle, and it is a theorem rather than a rewriting, because it composes
the block correspondence with the order swap. -/
alias sinTwoTheta_directed_complex :=
  sinTwoTheta_directed_unboundedResidual_symmetricNorming_complex

/-- **`sin 2Θ`, directed clause, over `ℝ`**, on the paper's own trial-side directed
double-angle sine. -/
alias sinTwoTheta_directed_real :=
  sinTwoTheta_directed_unboundedResidual_symmetricNorming_real

/-- **`sin 2Θ`, directed clause, over `ℂ`, in the proof's block form**:
`δ N(P_U P_{J_V Uᗮ}) ≤ 2 N(R)`.  The estimate is proved here and transported to the
angle by `sinTwoTheta_directed_complex`. -/
alias sinTwoTheta_directed_blockRepresentative_complex :=
  sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex

/-- **`sin 2Θ`, directed clause, over `ℝ`, in the proof's block form**. -/
alias sinTwoTheta_directed_blockRepresentative_real :=
  sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real

/-- **`tan 2Θ`, directed clause, over `ℂ`**: `(b − a) N(tan 2Θ₀) ≤ 2 N(R)`, on the
paper's directed object -- the `U → Uᗮ` projection block of the doubled tangent
expression -- for a subspace `V` reducing `A + B`, with the block's singular values
identified as `tan (arcsin aₙ(sin 2Θ₀))` in the statement itself.

Until 2026-09-02 this alias named
`tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex`,
which quantifies over an arbitrary self-adjoint involution `Z` and concludes on
`reflectionTangentCorner U Z`; that theorem remains as the general result. -/
alias tanTwoTheta_directed_complex :=
  tanTwoTheta_directed_unboundedResidual_symmetricNorming_complex

/-- **`tan 2Θ`, directed clause, over `ℝ`**, on `tanTwoDirectedCornerR U V`. -/
alias tanTwoTheta_directed_real :=
  tanTwoTheta_directed_unboundedResidual_symmetricNorming_real

/-- **`tan 2Θ`, ambient clause, over `ℂ`**: `(b − a) N(|tan 2Θ|) ≤ 2 N(B)`. -/
alias tanTwoTheta_ambient_complex := tanTwoTheta_ambient_unbounded_symmetricNorming_complex

/-- **`tan 2Θ`, ambient clause, over `ℝ`**. -/
alias tanTwoTheta_ambient_real := tanTwoTheta_ambient_unbounded_symmetricNorming_real

/-- **`sin 2Θ`, ambient clause, over `ℂ`**: `δ N(sin 2Θ) ≤ 2 N(H)` on the paper's
*ambient* double-angle sine, at this result's unbounded scope and at the printed
hypothesis -- `U` reduces `A`, `V` reduces `A + H`, and neither is required to be a
spectral subspace.

Retargeted 2026-09-05, closing finding F5 of the 2026-09-04 hostile review.  Until
then this alias named `sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex`,
which forces both subspaces to be spectral subspaces selected by measurable sets.
That is how a reader *produces* such a pair in the source, not what the printed
theorem assumes.  The spectral endpoint is retained as a specialization. -/
alias sinTwoTheta_ambient_complex :=
  sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_complex

/-- **`sin 2Θ`, ambient clause, over `ℝ`**, likewise at an arbitrary reducing pair. -/
alias sinTwoTheta_ambient_real :=
  sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_real

/-! ## `tan 2Θ` -/

/-- **Davis--Kahan 1970, the `tan 2Θ` theorem, over `ℂ` -- the AMBIENT clause.**

The printed `tan 2Θ` theorem has two boxed conclusions.  This name is the second,
`(b − a) N(|tan 2Θ|) ≤ 2 N(B)`; the directed one is `tanTwoTheta_directed_complex`.

`(b - a) · N(|tan 2Θ|) ≤ 2 N(B)` on the paper's ambient branch-free double-angle
tangent, with ideal membership, for an unbounded self-adjoint `A`, a bounded
self-adjoint perturbation `B` odd for the selected spectral subspace, and a
subspace `V` whose reflection intertwines `A + B`
(`DavisKahan.ReflectionIntertwines`, built from a `ReducesSubspace` by
`.ofReducesSubspace`).

No pole certificate is asked for: the ordered gap forces the reflection's diagonal
block to be a unit, and that unit excludes the quarter-turn poles. -/
@[deprecated "The unqualified clause names are not uniform; use `tanTwoTheta_ambient_complex`, which says which of the two printed conclusions it is." (since := "2026-09-05")]
alias tanTwoTheta_complex := tanTwoTheta_ambient_unbounded_symmetricNorming_complex

/-- **Davis--Kahan 1970, the `tan 2Θ` theorem, over `ℝ` -- the AMBIENT clause.**

Its directed partner is `tanTwoTheta_directed_real`.

The real sibling of `tanTwoTheta_ambient_complex`, on the real ambient `|tan 2Θ|`.  The real
statement is transported from the complex one through the complexification, with
no loss of constant or norm class and no second analytic proof. -/
@[deprecated "The unqualified clause names are not uniform; use `tanTwoTheta_ambient_real`, which says which of the two printed conclusions it is." (since := "2026-09-05")]
alias tanTwoTheta_real := tanTwoTheta_ambient_unbounded_symmetricNorming_real

/-! ## The whole printed `sin 2Θ` theorem, in one declaration

Davis and Kahan print two boxed conclusions under one set of separation
hypotheses.  The two clause aliases above are those two conclusions; the two
declarations here are the *result*, so a reviewer has one name to point at.

Both clauses take the same operator, the same measurable selection of its
spectrum and the same `FormBoundedSylvesterGap`, so that data is shared.  What is
not shared stays inside its own conjunct: the directed clause quantifies over the
trial subspace and its residual, the ambient clause over the bounded perturbation
and the selection it makes from the perturbed operator.  Forcing either one's data
into the other's telescope would change the printed statement, so it is not done.

`tan Θ` and `tan 2Θ` have no such certificate: their two clauses share almost no
data -- an unbounded Ritz pair against a trial block, a reflection intertwiner
against an involution -- so a conjunction would be two disjoint theorems written
next to each other, which is what the clause aliases already are. -/

section SinTwoThetaSource

open TauCeti.DavisKahan TauCeti.DavisKahan.ExactSinTheta TauCeti.DavisKahanExt

universe v

/-- A subspace admitting an orthogonal projection inside a complete ambient space
is itself complete.  `local instance` does not propagate through imports, so it is
reinstalled here for the trial subspaces the directed clause quantifies over. -/
local instance instCompleteSpaceCoeSectionTwoSource
    {𝕜 : Type*} [RCLike 𝕜] {G : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (W : Submodule 𝕜 G) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-- **Davis--Kahan 1970, the `sin 2Θ` theorem over `ℂ`, both printed conclusions.**

Under one separation hypothesis: `δ N(sin 2Θ₀) ≤ 2 N(R)` for every trial subspace
inside `dom A` with residual `R`, and `δ N(sin 2Θ) ≤ 2 N(H)` for every bounded
self-adjoint perturbation `H` and every measurable selection from the perturbed
operator's spectrum.  Unbounded self-adjoint ambient operator, arbitrary Hilbert
dimension, arbitrary source unitarily invariant norm, the whole gap. -/
theorem sinTwoTheta_bothConclusions_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (N : SymmetricNormingFunction)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (selfAdjointSpectralRestriction A hA B hB)
      (selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ) :
    (∀ {V : Submodule ℂ Hc} [V.HasOrthogonalProjection]
        {M : V →L[ℂ] V} {R : V →L[ℂ] Hc}
        (hVdom : ∀ v : V, ((v : V) : Hc) ∈ A.domain),
        (∀ v : V, A ⟨((v : V) : Hc), hVdom v⟩ = R v + ((M v : V) : Hc)) →
        N.Mem R →
          N.Mem (Angle.directedSinTwoAngleOperator V
              (selfAdjointSpectralSubspace A hA B hB)) ∧
            δ * N.gauge (Angle.directedSinTwoAngleOperator V
                (selfAdjointSpectralSubspace A hA B hB)) ≤ 2 * N.gauge R) ∧
      (∀ (Eop : Hc →L[ℂ] Hc) (_hEop : IsSelfAdjointOperator Eop)
        (W : Submodule ℂ Hc) [W.HasOrthogonalProjection]
        (_hW : TauCeti.LinearPMap.ReducesSubspace
          (TauCeti.LinearPMap.addBounded A Eop) W), N.Mem Eop →
          N.Mem (sinTwoAngleOperatorC (selfAdjointSpectralSubspace A hA B hB) W) ∧
            δ * N.gauge (sinTwoAngleOperatorC
                (selfAdjointSpectralSubspace A hA B hB) W) ≤ 2 * N.gauge Eop) :=
  ⟨fun hVdom hres hR =>
      sinTwoTheta_directed_complex N hA B hB hVdom hres hδ hgap hR,
    fun Eop hEop W _ hW hEmem =>
      sinTwoTheta_ambient_complex N hA Eop hEop
        (selfAdjointSpectralSubspace_reducing A hA B hB) hW hδ
        (by
          rw [selfAdjointSpectralRestriction_eq_reducingRestriction A hA B hB,
            selfAdjointSpectralRestriction_eq_reducingRestriction A hA Bᶜ hB.compl] at hgap
          exact FormBoundedSylvesterGap.reducingRestriction_congr_right
            (selfAdjointSpectralSubspace_compl_eq_orthogonal A hA B hB)
            (selfAdjointSpectralSubspace_reducing A hA Bᶜ hB.compl)
            (selfAdjointSpectralSubspace_reducing A hA B hB).orthogonal hgap)
        hEmem⟩

/-- **Davis--Kahan 1970, the `sin 2Θ` theorem over `ℝ`, both printed
conclusions.**  The real sibling of `sinTwoTheta_bothConclusions_complex`, at the same
strength. -/
theorem sinTwoTheta_bothConclusions_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : SymmetricNormingFunction)
    (A : Er →ₗ.[ℝ] Er) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA B hB)
      (RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ) :
    (∀ {V : Submodule ℝ Er} [V.HasOrthogonalProjection]
        {M : V →L[ℝ] V} {R : V →L[ℝ] Er}
        (hVdom : ∀ v : V, ((v : V) : Er) ∈ A.domain),
        (∀ v : V, A ⟨((v : V) : Er), hVdom v⟩ = R v + ((M v : V) : Er)) →
        N.Mem R →
          N.Mem (Angle.directedSinTwoAngleOperator V
              (RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)) ∧
            δ * N.gauge (Angle.directedSinTwoAngleOperator V
                (RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)) ≤
              2 * N.gauge R) ∧
      (∀ (Eop : Er →L[ℝ] Er) (_hEop : IsSelfAdjointOperator Eop)
        (W : Submodule ℝ Er) [W.HasOrthogonalProjection]
        (_hW : TauCeti.LinearPMap.ReducesSubspace
          (TauCeti.LinearPMap.addBounded A Eop) W), N.Mem Eop →
          N.Mem (sinTwoAngleOperatorR
              (RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB) W) ∧
            δ * N.gauge (sinTwoAngleOperatorR
                (RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB) W) ≤
              2 * N.gauge Eop) :=
  ⟨fun hVdom hres hR =>
      sinTwoTheta_directed_real N hA B hB hVdom hres hδ hgap hR,
    fun Eop hEop W _ hW hEmem => by
      rw [← Angle.sinTwoAngleOperator_real]
      exact sinTwoTheta_ambient_real N hA Eop hEop
        (RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing A hA B hB) hW hδ
        (FormBoundedSylvesterGap.reducingRestriction_congr_right
          (RealSpectralRestriction.realSelfAdjointSpectralSubspace_compl A hA B hB)
          (RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing A hA Bᶜ hB.compl)
          (RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing A hA B hB).orthogonal
          hgap)
        hEmem⟩

end SinTwoThetaSource

end SectionTwo
end DavisKahan1970
end TauCeti
