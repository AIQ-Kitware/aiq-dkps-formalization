# Section 4 independent scratch lane

Base: `7f9f562b50443bb4e66c4bc7b32413c2ae019a6a`.

## Collision audit

`dev/LANES.md` contains no claim for the Section 4 frontier or for a Section 4
scratch lane.  This overlay adds files only under
`DavisKahan/Experimental/Scratch/Section4/` and does not edit any active agent
file.

The remaining Section 8 frontier declarations were considered and rejected as
a scratch target because the current upper/lower compression statements imply
quadratic-form monotonicity under an arbitrary perturbation and their proposed
`id`/`id` certificates cannot satisfy the displayed decomposition in general.

## Mathematical output

### Infinite ideal dominance

`InfiniteIdealDominance.lean` proves that pointwise approximation singular-value
dominance implies every finite Ky Fan dominance inequality and therefore gives
membership and gauge domination for `KyFanDominantIdealFamily`.

This exposes a type-level issue in the current frontier Corollary 4.1.  The bare
`RectangularSymmetricIdealFamily` structure contains ideal estimates and
completeness but no monotonicity under singular-value or Ky Fan dominance.  The
repository's stronger `KyFanDominantIdealFamily` is the correct source-facing
scope for this deduction.

### Finite certified source surface

`FiniteSourceSurface.lean` wraps the already proved finite-dimensional results:

- Proposition 4.1, singular-value form;
- Proposition 4.1, approximation-singular-value form;
- Corollary 4.1 for ordinary square UI norms;
- Proposition 4.3 for the displacement square;
- Proposition 4.2 in the compiled full-orthonormal-basis energy form.

These wrappers are not an infinite-dimensional proof.  They establish a clean,
certifiable source specialization and make the remaining infinite lift precise.

## Remaining mathematical obligation

The load-bearing infinite result is:

```lean
forall n,
  approximationSingularValue n ((1 - R) comp projection U) <=
  approximationSingularValue n ((1 - W) comp projection U)
```

for the acute direct rotation `R` and every unitary projection intertwiner `W`.
Once that statement is proved, the scratch dominance theorem gives the corrected
Corollary 4.1 immediately.

## Lemma ledger

### Expected stable names

- `ExactSinTheta.approximationSingularValue`
- `ExactSinTheta.kyFanApproximationGauge`
- `ExactSinTheta.mem_and_gauge_le_of_all_kyFanApproximationGauge_le`
- `ExactSinTheta.approximationSingularValue_eq_singularValues`
- `DavisKahanTheory.singularValues_restrictedDisplacement_le`
- `DavisKahanTheory.directRotation_minimizes_restrictedDisplacement_uiNorm`
- `DavisKahanTheory.directRotation_minimizes_displacementSquare_uiNorm`
- `DavisKahanTheory.directRotation_minimizes_sum_sq_basis_angles`

### Likely elaboration seams

- Whether the composed `LinearMap` requires an explicit finite-dimensional
  `CompleteSpace` instance before `.toContinuousLinearMap` elaborates.
- Whether `rw [approximationSingularValue_eq_singularValues]` needs explicit
  operator arguments.
- Namespace qualification for `displacementSquare` and the finite direct
  rotation theorems.

## Confidence

- Ky Fan sum bridge: complete.
- Fan-dominant ideal bridge: complete.
- Finite wrappers: probably complete; only coercion and namespace repair expected.
- Infinite Proposition 4.1: not attempted in this overlay.
- Current frontier Proposition 4.2 statement: requires source audit before use.
