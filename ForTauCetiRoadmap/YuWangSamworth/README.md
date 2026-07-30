# Roadmap: the Yu–Wang–Samworth statistical variant

**Topic T18 of the candidate design.** Three modules. Depends on T01, T05, T06,
T08, T17 — it is a *leaf*, consumed by nothing. Together with T19 and T20 it
forms the statistical track: see *How the three compose* below.

## Why a separate topic from T17

Davis–Kahan bounds a subspace rotation by an operator perturbation, and its
hypothesis is a gap in the spectrum of **one** of the two operators. That is the
wrong shape for statistics.

In a statistical problem the perturbed operator is a *sample* covariance and its
spectrum is random; the gap one can actually assume is a gap in the *population*
spectrum. Yu–Wang–Samworth is the variant stated that way, and the substance of
the topic is exactly that hypothesis change.

`Statistics.lean` is explicit that this is a literature-facing surface, mapped
to `prose/core-arguments/Yu-Wang-Samworth-2014-core-arguments.tex` in full and to
the "Hoffman–Wielandt and the exact YWS theorem" and "aligned-basis (Procrustes)
bound" paragraphs of `papers/DavisKahan-formalized-vs-literature.tex`.

## The modules

| Module | Role |
|---|---|
| `Residual` | The sin-Θ overlap between an `S`-block subspace and a `T`-block subspace, for symmetric `T`, `S` and a fixed index block. The quantity the bound is about. |
| `SingularSubspace` | The rectangular case: singular subspaces via the Gram operators, which is what makes the theorem apply to non-square data matrices. |
| `Statistics` | The canonical subspace-facing API — interval-block, aligned-basis (Procrustes) and single-vector surfaces. |

The `SingularSubspace` file in **T05** exists for this topic, and is called out
there for that reason: the YWS singular-vector bound applies the symmetric
result to `A⋆A`, so it needs the Gram perturbation bounded in terms of the
original one. If T18 were dropped, that T05 module would have no consumer.

## How the three statistical topics compose

T18, T19 and T20 are one argument in three pieces, and each is separately
submittable:

1. **T20** concentrates a sample covariance onto the population matrix —
   entrywise mean-square closeness plus Chebyshev and a union bound over `n²`
   entries gives an operator-norm bound with high probability.
2. **T19** supplies the measurability that makes a random spectral quantity
   well-defined at all: for continuous `h`, the spectral transform
   `Σₖ h(λₖ) uₖ uₖᵀ` of a measurable Hermitian family is measurable.
3. **T18** is the deterministic inequality those two feed: given an
   operator-norm perturbation bound and a **population** gap, the subspace
   rotation is controlled.

The order matters for reading but not for submission — T18 is deterministic and
depends on neither of the other two.

## What a reviewer should check

1. **That the gap hypothesis is on the population operator**, not the sample
   one. This is the entire reason the topic is separate from T17, and it is the
   thing a reader coming from Davis–Kahan will not expect.
2. **That the aligned-basis (Procrustes) surface is stated**, since it is what
   makes the bound usable when the two eigenbases are only determined up to
   rotation — the situation in every application.
3. **That `Residual` is stated for an arbitrary index block**, not just a leading
   one; leading-block-only would not cover the interval case.

## Prerequisites

T01, T05, T06, T08, T17. Nothing depends on this topic.
