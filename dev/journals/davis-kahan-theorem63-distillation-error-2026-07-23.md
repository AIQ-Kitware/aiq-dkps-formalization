# Davis--Kahan Theorem 6.3 distillation error: unequal dimension is directed, not acute

**Date:** 2026-07-23  
**Severity:** high — a source theorem was replaced by a materially different and false geometric statement.

## Symptom

The frontier version of Davis--Kahan 1970, Theorem 6.3 assumed only an
isometric embedding of a smaller trial subspace `Z` into a larger exact
subspace `V`, then concluded that the full pair was symmetrically acute:

```lean
hdim : Nonempty (Z →ₗᵢ[ℂ] V)
⊢ ∃ hacute : IsAcute Z V, ...
```

This looked plausible because the paper explicitly assumes a strict dimension
inequality.  It was not faithful to the source.

## What the paper actually says

Theorem 6.3 assumes

```text
dim X(E₀) < dim X(F₀)
```

and defines the directed sine data by the singular values of `E₀⋆ F₁`.
Equivalently one may use the adjoint cross block `F₁⋆ E₀`, the projection of the
trial coordinates into the orthogonal complement of the larger exact space.
The theorem then bounds a rectangular `tan Θ₀` representative with the tangent
of that same singular-value list.

The theorem does **not** assert a direct rotation of the full unequal-dimensional
pair, and it does not require or conclude symmetric `IsAcute`.

## Why the distilled implication is false

An isometric embedding controls only Hilbert dimension.  It says nothing about
the reverse directed projection from `V` to `Z`.

The regression theorem

```lean
ForMathlib.DavisKahan1970.Theorem63DistillationAudit.
  not_mistranscribedDimensionImpliesAcute
```

uses `Z = ⊥` and `V = ⊤` in the one-dimensional complex Hilbert space.  There is
a strict dimension inequality and an isometric inclusion `Z →ₗᵢ V`, but the
nonzero vector `1 ∈ V` projects to zero in `Z`, so `IsAcute Z V` is false.
A nontrivial version is the same geometry with
`span(e₀) ⊂ span(e₀,e₁)`.

## Root cause

We compressed three different notions into one:

1. strict inequality of the source coordinate-space dimensions;
2. one-sided transversality of the trial space toward the exact space;
3. symmetric acuteness, which is the hypothesis needed by the repository's
   equal-rank direct-rotation tangent operator.

Only the first is a literal Theorem 6.3 hypothesis.  The paper proves the
needed directed no-pole statement inside its singular-vector/Ky-Fan argument;
it never promotes the unequal-dimensional pair to symmetric acuteness.

## Repair

- The distillation now quotes the directed cross-block formulation explicitly.
- The finite strict-lower-rank theorem is labeled a compiled specialization,
  not the full Hilbert-space source endpoint.
- The frontier no longer credits the finite specialization as completion of
  Theorem 6.3 or of the unbounded arbitrary-UI-norm scope.
- `Experimental/Scratch/Section6/Theorem63SourceFaithful.lean` records the
  directed sine block, a directed tangent approximation-number interface, and
  the already-proved Fan-dominance promotion.
- The remaining hard blocker is named honestly: prove the source finite-Ky-Fan
  inequalities (and then the unbounded cutoff passage) without introducing a
  symmetric `IsAcute` premise.

## Durable rules

1. **Dimension comparison is not angle control.** Never derive acuteness,
   transversality, surjectivity, or a direct rotation from a Hilbert-dimension
   embedding alone.
2. **Preserve direction in unequal-rank angle theorems.** Track the exact cross
   block and its source/target spaces before choosing an angle API.
3. **Do not let a compiled specialization rename itself into a source theorem.**
   The frontier endpoint must preserve the paper's dimensional and analytic
   scope.
4. **For unusual source hypotheses, compare the literal statement and proof
   before distilling.** Here the proof's use of `E₀⋆ F₁`, rather than a direct
   rotation, would have exposed the mistake immediately.
5. **Keep a kernel-checked counterexample for every rejected transcription.**
   Prose warnings alone are too easy to regress.
