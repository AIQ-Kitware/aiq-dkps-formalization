# Roadmap: resolvents of unbounded self-adjoint operators

**Topic T15b of the candidate design.** Seven modules, and — since lane
T15-SPLIT cut the old 25-module T15 — **no prerequisites at all**:
`scripts/check_tauceti_roadmap_topics.py --needs` reports T15b as independent.
It is the cheapest way into the unbounded theory.

## The theorem this topic exists for

A self-adjoint operator has real spectrum, with a quantitative inverse off the
axis:

```lean
theorem mem_resolventSet_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ resolventSet A

theorem norm_resolvent_le_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolvent A (mem_resolventSet_of_im_ne_zero hA hz)‖ ≤ |z.im|⁻¹
```

so `spectrum A ⊆ ℝ`, with the resolvent norm controlled by the distance to the
axis. The proof is the classical three steps — the estimate
`‖(A - z) x‖ ≥ |Im z| ‖x‖` (the cross term in `‖(A - Re z)x - i (Im z)x‖²` is
purely imaginary and drops out), closed range, dense range.

Everything else here is the API that statement needs to be usable: what the
resolvent set *is* for a partially defined operator, that the resolvent is a
genuine bounded operator with the first resolvent identity, that the resolvent
set is open, and what replaces the free estimate `|Im z|` at a real point.

## Why `LinearPMap` needs its own resolvent set

Mathlib's `spectrum R a` is `¬IsUnit (algebraMap R A z - a)`, defined for an
element of an algebra. **A `LinearPMap` is not an algebra element** — it has a
domain, and `A - z` is only defined on that domain — so the definition does not
apply and cannot be made to apply by a coercion.

The topic therefore defines, for `A : E →ₗ.[𝕜] E`:

- `resolventSet A` — the `z` for which `A - z` has a two-sided **bounded**
  inverse: an `R : E →L[𝕜] E` inverting `A - z` on `dom A`, solving
  `(A - z) x = φ` for every `φ`, with the solution back in `dom A`;
- `spectrum A` — its complement.

**Both halves of "two-sided" are load-bearing** and this is the design point a
reviewer should be shown first: for an unbounded operator, injectivity on the
domain and surjectivity onto the whole space are independent conditions, and a
one-sided definition would admit operators whose "inverse" leaves the domain.

## Pinned conventions

### The resolvent is named, not just asserted to exist

`resolventSet` says a bounded inverse exists; `LinearPMap/ResolventBound.lean`
names it and proves what downstream actually consumes — the **first resolvent
identity** `R w - R z = (w - z) • R w ∘ R z`, and resolvent spectral mapping in
the direction that matters (if `μ ≠ 0` and `z + μ⁻¹ ∈ resolventSet A` then `μ` is
not in the spectrum of the bounded `R z`). Uniqueness (`resolvent_unique`) is
what lets later proofs produce an inverse by any construction and know it is
*the* resolvent.

### Openness is proved for the sake of measurability, not elegance

Mathlib has `spectrum.isOpen_resolventSet` for bounded operators. For a
`LinearPMap` it must be proved, by the Neumann-series perturbation run through
`resolvent_unique`. It is here because **the spectrum has to be a measurable set
before it can be fed to a projection-valued measure** — the consumer is
`specProjection hA (Complex.ofReal ⁻¹' spectrum A)` in T15c.

### The real-point case is a hypothesis, not a theorem

Off the real axis the lower bound `‖(A - z) x‖ ≥ |Im z| ‖x‖` comes for free, and
the three steps that follow — injectivity, closed range, dense range — use only
that bound. At a *real* `z` there is no free bound, so `RealLowerBound.lean`
takes `c ‖x‖ ≤ ‖A x - z x‖` as a hypothesis and reruns the same three steps.
**Not a weaker theorem: a factored one.** The split is deliberate and should stay
— the caller who has a lower bound (a semibounded operator, a spectral gap)
should not have to reprove closed range.

### The C⋆-algebra facts are stated for C⋆-algebras

`Analysis/CStarAlgebra/SelfAdjointGapInverse.lean` proves that a self-adjoint
element with `‖a‖ ≤ r` iff real spectrum in `[-r, r]`, and that spectrum avoiding
`(-r, r)` makes `a` a unit with `‖a⁻¹‖ ≤ r⁻¹`. These are facts about C⋆-algebra
elements and are stated that way, not about operators on a Hilbert space, even
though that is the only consumer here. Invertibility needs neither
self-adjointness nor a norm bound, and the file says so.

### Intertwiners come this far and stop

`SeparatedIntertwiner.lean` carries the chain *an `X` intertwining two operators
intertwines their resolvents, their Cayley transforms, and their continuous
functional calculus*. It stops before the Borel calculus on purpose: the step
from continuous to Borel is T14's, and pulling it in would make this topic depend
on T14 and stop being independent. The payoff — disjoint spectra force `X = 0` —
lands once T15c is available.

## Existing foundations

Mathlib supplies `LinearPMap` with its graph, adjoint and `IsSelfAdjoint`,
`ContinuousLinearMap` with operator norms, `IsUnit`/`spectrum` for algebra
elements, the continuous functional calculus, and the Neumann series.

A sorry-free staged implementation exists under `ForTauCeti/`, in seven modules
(`scripts/check_tauceti_roadmap_topics.py --topic T15b`). These results still
require Tau Ceti review and migration.

## What remains to land

- **A resolvent-set characterisation a reviewer can check against a textbook**:
  currently the definition is the working one (bounded two-sided inverse) and the
  equivalence with *closed, injective, surjective* is spread across the proofs of
  `SelfAdjointResolvent`. Stating it once as an iff is worth doing before
  submission.
- **The analytic structure of `z ↦ R z`.** The first resolvent identity is here;
  analyticity on the resolvent set is not, and it is what a reader expects next.
- **Theorem-level acceptance examples**, in Tau Ceti's shape.

## Ordering and PR slices

1. `LinearPMap/{Resolvent, ResolventBound, ResolventOpen}` — the definition, the
   named resolvent with its identity, and openness. Self-contained.
2. `LinearPMap/{SelfAdjointResolvent, RealLowerBound}` — real spectrum with the
   `|Im z|⁻¹` bound, and the real-point variant.
3. `Analysis/CStarAlgebra/SelfAdjointGapInverse` and `SeparatedIntertwiner` — the
   C⋆-algebra gap inverse and the intertwining chain.

Slice 1 alone is a coherent contribution: *unbounded operators have a resolvent
set, it is open, and the resolvent satisfies the first resolvent identity.*

## Provenance and coordination

The seven modules were authored in place in this repository (Davis–Kahan/DKPS
formalization, Kitware, Inc.). `SeparatedIntertwiner.lean` came from Spectra
removal lane SR-E, replacing the donor's
`generatorIntertwiner_eq_zero_of_disjoint_spectrum`; nothing here imports Spectra.

T15b is rung **M** of `dev/tauceti/submission-ladder.md`. It is consumed by T15c
(the spectral measure) and, through it, by T16 and T17.

Written 2026-07-29 by `jon (yardrat)` under lane ROADMAP-WRITE, one topic per
claim, immediately after lane T15-SPLIT made this topic exist. T01, T21 and T22
remain independent and unwritten; T15a and T15c are the other two pieces of the
old T15 and neither has a roadmap yet.
