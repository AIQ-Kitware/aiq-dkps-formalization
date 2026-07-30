# Roadmap: Gram matrices, orthogonal projections, and spectral subspaces

**Topic T04 of the candidate design.** Eight modules. Depends on T01. Consumed by
T05, T06, T07, T15a, T16 and T17 — **seven dependents, second only to T01's
nine.** Between them those two supply the vocabulary the rest of the development
states its theorems in.

## The theorem this topic exists for

```
‖P − Q‖ = max(‖(1−Q)P‖, ‖(1−P)Q‖)      for orthogonal projections P, Q
```

**This is the sharp projector-difference identity, and it is why T17 depends on
this topic.** The Davis–Kahan machinery naturally produces two *one-sided*
sin Θ estimates — one bounding `(1−Q)P`, one bounding `(1−P)Q`. This identity is
what upgrades that pair to a bound on `‖P − Q‖` itself **with factor one and no
equal-rank hypothesis**.

Without it the development would either lose a factor of two or have to carry a
rank condition through every statement. The proof is the block decomposition
`(P−Q)² = P(1−Q)P + (1−P)Q(1−P)` together with the C⋆-norm identities, and it is
scalar-generic over `RCLike`.

A reviewer checking one thing in this topic should check this: that the identity
is an equality rather than a two-sided estimate, and that no equal-rank
hypothesis appears.

## The module that has already been through Mathlib review

`GramMatrix` is unusual and worth flagging, because it carries evidence about
the submission surface rather than about itself.

It was submitted as **mathlib4 PR #40567**, reviewed by @wwylele, and folded
into a `def` with an `@[simp]` apply lemma in response. The PR was subsequently
closed — `ForTauCeti/README.md` records that Mathlib is no longer the
destination — and the module was then *restructured again* rather than left at
the shape the closed PR had reached: the quotient plumbing is now a standalone
**isometric first isomorphism theorem**, `LinearMap.rangeEquivOfInnerEq`, stated
for an arbitrary pair of linear maps, whose `@[simp]` apply lemma carries an
arbitrary membership proof so downstream proofs are a one-line `simp`.

The point for a reviewer: this is a module whose API was shaped by real upstream
feedback and then generalised past what that feedback asked for. If any part of
the topic is close to Mathlib-ready, it is this one, and the generalisation is
the reason.

## The vocabulary the rest of the development uses

Five of the eight modules exist to give later topics a stable way to *say*
things, not to prove hard theorems:

| Module | What it fixes |
|---|---|
| `ProjectionGeometry` | Projection geometry for finite orthonormal families. |
| `ProjectionBlocks` | Projection blocks and reflections — the `2×2` decomposition everything downstream is written in. |
| `ReducingSubspace` | Invariant and reducing subspaces for bounded operators, over `RCLike`. **Independent of Davis–Kahan theory**, and says so. |
| `SpectralSubspace` | Restricted spectra, canonical spectral projectors, and the quadratic-form bridges the finite Davis–Kahan theorems use. |
| `SpectralGap` | The canonical separation hypotheses used by the sine, tangent, double-angle and Sylvester theorem families. |

`SpectralGap` deserves particular attention. Four theorem families state their
hypotheses in terms of a spectral separation, and if each defined its own
predicate the statements could not be compared. Fixing them once here is what
makes "the same gap hypothesis" a checkable claim rather than an informal one.

`ReducingSubspace` being independent of Davis–Kahan is a deliberate boundary,
not an accident of drafting — it means the module can be read, reviewed, and if
desired submitted without any of the perturbation theory.

## `OrthogonalSeries` fills a real gap in Mathlib

Mathlib's `OrthogonalFamily` is indexed by a family of *subspaces* `G i` with
isometries `V i : G i →ₗᵢ[𝕜] E`. The common special case — a family of pairwise
orthogonal *vectors* — is not directly available, because the only upstream
constructor, `Orthonormal.orthogonalFamily`, requires the vectors to be **unit**.

That is a genuine hole rather than a naming inconvenience: the vectors this
development produces are `σᵢ • uᵢ` and rank-one images, which are orthogonal but
not normalised, and normalising them is exactly what one cannot do when some
`σᵢ` are zero. This module supplies the missing constructor.

## What a reviewer should check

1. **That the projector-difference identity is an equality**, with no equal-rank
   hypothesis — see above.
2. **That `SpectralGap`'s predicates are shared**, not four parallel definitions
   with one name.
3. **That `ReducingSubspace` really is independent of the perturbation theory** —
   it claims to be, and that claim is what makes it separately submittable.
4. **That `OrthogonalSeries` is filling a hole rather than duplicating
   `OrthogonalFamily`** — the distinguishing fact is the unit-vector requirement
   upstream.

## Prerequisites

T01, and nothing else. That is the useful shape: T04 has seven dependents and one
prerequisite, so it sits directly above the root of the DAG. Anything that makes
T04 harder to submit blocks seven topics; anything that makes T01 harder blocks
nine, through T04 among others.
