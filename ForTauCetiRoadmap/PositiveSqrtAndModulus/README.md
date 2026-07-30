# Roadmap: the positive square root, the modulus, and the finite functional calculus

**Topic T01 of the candidate design.** Nine modules, no prerequisites — the base
of the finite-dimensional half of the library. Seven topics name it directly (T02, T03, T04,
T09, T17, T18, T19) and more reach it transitively.

## What the topic supplies

For a symmetric endomorphism of a finite-dimensional inner product space over
`𝕜 : RCLike`, apply a real function to the spectrum:

```lean
noncomputable def selfAdjointFunctionalCalculus
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) : E →ₗ[𝕜] E :=
  ∑ i, ((f (hT.eigenvalues rfl i) : ℝ) : 𝕜) •
    (InnerProductSpace.rankOne 𝕜 (hT.eigenvectorBasis rfl i)
      (hT.eigenvectorBasis rfl i)).toLinearMap
```

Everything else in the topic is either an instance of that, a bound on
eigenvalues, or the algebra needed to state it:

* `LinearMap.IsPositive.sqrt` — the calculus at `Real.sqrt`, with the uniqueness
  theory (`sqrt_unique`, `sqrt_mul_self`, `ker_sqrt`, `range_sqrt`) that only the
  square root has;
* `TauCeti.abs` — the modulus `|A| = (A⋆A)^{1/2}`, and the polar decomposition
  `A = U |A|` with `U` unitary when `A` is invertible;
* `ContinuousLinearMap.modulus` — the rectangular complex modulus, through
  Mathlib's continuous functional calculus;
* `CourantFischer` — the min–max principle and Weyl's perturbation inequality;
* the supporting algebra: inner products of linear combinations, spans of
  orthonormal subfamilies, the eigenvector cross-term identity, two scalar
  square-root estimates near `1`, and one `LinearIsometryEquiv.ofEq` `rfl` lemma.

## Pinned conventions

Three of these were **decided in lanes on 2026-07-29/30 rather than inherited**,
and each is recorded with its evidence in the source.

### One square root, defined once (lane T01-SQRT)

`IsPositive.sqrt` **is** `selfAdjointFunctionalCalculus hT.isSymmetric Real.sqrt`
— by definition, not by a lemma. It used to be a second `noncomputable def`
spelling out the same `∑ᵢ √λᵢ • rankOne eᵢ eᵢ`, with the two shown equal by
`rfl`; one object was defined twice and its diagonal-action lemma proved twice.
The definition is collapsed and the square-root-specific theory kept where it
was. A roadmap reader should not meet two constructions of one object.

### Two moduli, and neither subsumes the other (lane MODULUS-DEDUP)

`TauCeti.abs : (E →ₗ[𝕜] E) → (E →ₗ[𝕜] E)` is square, `RCLike`-generic and
finite-dimensional. `ContinuousLinearMap.modulus : (E →L[ℂ] F) → (E →L[ℂ] E)` is
rectangular and complex, because Mathlib registers the C⋆-instances only over `ℂ`.
**They agree exactly where both are defined**, and the library proves it —
`abs_toContinuousLinearMap_eq_cfcAbs`. One is more general in the field, the other
in the shape; deleting either loses theorems. The same shape of answer as the
square root above: the `RCLike`-generic construction is the library's own, and the
C-only CFC version stays beside it.

### Three polar factors, one hierarchy

`polarFactor` (square, `RCLike`, a unitary), `polarPartial` (rectangular, `ℂ`, a
partial isometry) and `polarIsometryOfIsUnitModulus` (rectangular, `ℂ`, an
isometry once the modulus is a unit). Reading down: dropping finite dimension
costs the unitary; assuming the modulus invertible buys an isometry back. Each
module now says so; before 2026-07-30 none of the three mentioned the others.

### `𝕜 : RCLike`, and finite dimension where the eigenbasis is used

The calculus is built from `LinearMap.IsSymmetric.eigenvectorBasis`, so finite
dimension is not a convenience here — it is what makes the definition a finite
sum. Modules that do not need it (`Basic`, `SpecialFunctions.Sqrt`,
`Normed.Operator.LinearIsometry`) do not assume it, and that is deliberate: they
are the parts a reviewer can take without taking the spectral theory.

## Existing foundations

Mathlib supplies `LinearMap.IsSymmetric` with `eigenvalues` / `eigenvectorBasis`,
`LinearMap.IsPositive`, `ContinuousLinearMap` adjoints, `IsStarProjection` and
partial isometries in a star monoid, `CFC.sqrt` and `CFC.abs` over `ℂ`, and
`Matrix`-side spectral theory.

What Mathlib does **not** have, and this topic adds: a functional calculus for a
symmetric `LinearMap` over `RCLike` (Mathlib's is C⋆-algebraic and complex), the
`RCLike` positive square root with its uniqueness theory, the `RCLike` modulus and
polar decomposition on a `LinearMap`, and Courant–Fischer/Weyl in that setting.

A sorry-free staged implementation of all nine modules exists under `ForTauCeti/`
(`scripts/check_tauceti_roadmap_topics.py --topic T01`). These results still
require Tau Ceti review and migration.

## What remains to land

- **The uniqueness of the calculus.** `sqrt_unique` exists for the square root;
  the general statement — that `selfAdjointFunctionalCalculus` is the unique
  symmetric operator acting as `f (λᵢ)` on each eigenvector — is not stated, and
  it is the characterisation a reviewer will look for first.
- **Agreement with Mathlib's CFC in general.** The bridge exists at `Real.sqrt`
  (`abs_toContinuousLinearMap_eq_cfcAbs`); the corresponding statement for a
  general continuous `f` on a complex space is not proved, and it is what would
  let a consumer move between the two calculi freely.
- **Theorem-level acceptance examples**, in Tau Ceti's shape.

None of these changes a statement already staged.

## Ordering and PR slices

1. `InnerProductSpace.Basic`, `BasisSpan`, `Normed.Operator.LinearIsometry`,
   `SpecialFunctions.Sqrt` — the supporting algebra and two scalar estimates. No
   spectral theory; independently reviewable and independently useful.
2. `SelfAdjointFunctionalCalculus`, `PositiveSqrt`, `Spectrum` — the calculus, the
   square root as its instance at `Real.sqrt`, and the eigenvector cross-term
   identity.
3. `OperatorModulus`, `CourantFischer` — the modulus (both carriers, with the
   bridge) and min–max/Weyl.

Slice 2 is where the topic's own idea lives; slices 1 and 3 are shorter.

## Provenance and coordination

The nine modules were authored in place in this repository (Davis–Kahan/DKPS
formalization, Kitware, Inc.). One carries real Mathlib history:
`Analysis/InnerProductSpace/Basic.lean` was submitted as Mathlib PR #40567 and
reshaped on @wwylele's review; its header records that, and lane HDR-DEST kept it
while re-aiming the rest of the library's headers at Tau Ceti.

T01 is rung **G** of `dev/tauceti/submission-ladder.md` (which completes topics
T01–T10 after the historical rungs A–F). Its dependents, from `--needs`, are T02, T03, T04, T09, T17,
T18 and T19 — most of the finite-dimensional library.

Written 2026-07-30 by `jon (yardrat)` under lane ROADMAP-WRITE, one topic per
claim. T21 and T22 remain independent and unwritten.
