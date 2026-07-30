# Roadmap: matrix spectra and spectral measurability

**Topic T19 of the candidate design.** Six modules. Depends on T01 and T14.
Consumed by T20. Part of the statistical track — see the T18 roadmap for how the
three compose.

## What this topic is for

Everything else in the development is about operators on abstract inner product
spaces. This topic is about **matrices**, and about matrices whose entries are
random. Both departures are deliberate and neither is a lapse into coordinates:

* statistical data arrives as a matrix, entrywise, and the bounds a statistician
  can assume are **entrywise** bounds;
* a sample covariance is a *measurable function of ω*, so any spectral quantity
  built from it has to be measurable before it can be integrated or bounded in
  probability.

## Two gaps in Mathlib, both stated precisely

**1. No entrywise-to-operator-norm comparison.** Mathlib has the `ℓ²`
operator-norm API for matrices in `Mathlib/Analysis/CStarAlgebra/Matrix.lean`,
but nothing bounding it by the entrywise norm. `EntrywiseOpNorm` supplies
`‖toEuclideanLin A‖ ≤ n · (entrywise sup of A)`.

Combined with Weyl's inequality — which bounds eigenvalue perturbation by the
*operator* norm — that yields the directly usable **entrywise** eigenvalue
perturbation bound in `EntrywiseEigenvalue`. That composite is the whole reason
the pair exists: a statistician has entrywise control and needs spectral
conclusions.

**2. The sorted eigenvalue indexing is underdeveloped upstream.** Mathlib indexes
a Hermitian matrix's eigenvalues twice — `eigenvalues₀`, sorted decreasingly on
`Fin (Fintype.card n)`, and `eigenvalues`, reusing the matrix index — with the
second *defined* from the first. But the basic theory is stated only for
`eigenvalues`; `eigenvalues₀` carries just `eigenvalues₀_antitone` and the
characteristic-polynomial identities.

`Spectrum` transports the two facts the sorted indexing actually needs — the rank
count, and nonnegativity for a positive semidefinite matrix — and deduces the
vanishing tail of a low-rank positive semidefinite matrix. Sorted indexing is
what any "top-`k` eigenvalues" statement needs, so this is a prerequisite for the
statistical use rather than a convenience.

## The measurability result

```
specTransform h B = Σₖ h(λₖ) uₖ uₖᵀ      is measurable in B,
                                          for fixed continuous h
```

For a measurable Hermitian-matrix family. Equivalently, for continuous `h`, this
is the matrix continuous functional calculus, and the statement is that it is
measurable as a function of the matrix.

**This is the module that makes the statistical track well-posed.** Without it,
"the top-`k` eigenspace of the sample covariance" is a set-valued expression with
no measurability, and no probability statement about it means anything. It is
easy to overlook precisely because in the deterministic development the question
never arises.

## The modules

| Module | Role |
|---|---|
| `EntrywiseOpNorm` | `‖toEuclideanLin A‖ ≤ n · ‖A‖_∞`, absent upstream. |
| `EntrywiseEigenvalue` | Weyl composed with the above: entrywise perturbation ⇒ eigenvalue perturbation. |
| `Spectrum` | The sorted-indexing facts `eigenvalues₀` lacks upstream, and the low-rank tail. |
| `SpectralFunctionMeasurable` | Measurability of the spectral `h`-transform. |
| `MeasureTheory.Function.ConvergenceInMeasure`, `MeasureTheory.Measure.Typeclasses.Probability` | Supporting measure-theoretic additions. |

The last two are in `MeasureTheory`, not `Analysis` — this topic contributes to
two parts of the library, like T05.

## What a reviewer should check

1. **That the entrywise bound carries the factor `n`** and is not silently
   dimension-free — the `n` is what a statistician must pay, and dropping it
   would make the downstream concentration bound wrong rather than weak.
2. **That `SpectralFunctionMeasurable` is about measurability in the matrix**,
   not in `ω` for a particular family — the general statement is what T20 needs.
3. **That the `eigenvalues₀` facts are transported, not re-proved** — they exist
   upstream for `eigenvalues`, and duplicating them would be the wrong fix.

## Prerequisites

T01 and T14 (Borel functional calculus, for the spectral transform).
