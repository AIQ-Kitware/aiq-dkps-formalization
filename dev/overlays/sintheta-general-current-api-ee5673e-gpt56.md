# `SinTheta/General.lean` current-API migration

Base: `ee5673e`

## Purpose

This overlay removes the stale uses of the deleted bounded-map codomain
restriction helper and the deleted orthogonal-restriction convenience method.
It adds an explicit compatibility module and migrates the existing theorem
proofs without changing their mathematical statements.

## Files

- `DavisKahan/Experimental/InfiniteDimensional/SinTheta/RestrictionCompat.lean`
- `DavisKahan/Experimental/InfiniteDimensional/SinTheta/General.lean`

## Expected compile order

```bash
lake env lean \
  DavisKahan/Experimental/InfiniteDimensional/SinTheta/RestrictionCompat.lean
lake env lean \
  DavisKahan/Experimental/InfiniteDimensional/SinTheta/General.lean
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.General
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.All
lake build DavisKahan.Experimental.InfiniteDimensional.DoubleAngle
```

Then rebuild the Section 8 and Section 9 aggregates that were previously hidden
behind the stale object file.

## Mathematical status

The migration proves the rectangular block equations directly and preserves the
existing sine-theorem arguments.  It does not by itself make the chain
recursively grounded.  In particular, the following imported leaves remain
separate obligations in the current base:

- `restrictedSpectrum_top_eq_realSpectrum`;
- the remaining finite-step and limit reconstruction declarations in
  `FourierSemigroup.lean`;
- the ordered semigroup reconstruction declarations in
  `OrderedSemigroup.lean`;
- two public Sylvester declarations in `Basic.lean`.

Accordingly, a successful rebuild means that the stale API blocker is removed
and the frontier becomes measurable.  It is not alone evidence that every
Section 8 or Section 9 theorem is recursively admission-free.

## Likely elaboration repairs

- simplification of `codRestrict` coercions;
- exact namespace of `restrictedSpectrum_top_eq_realSpectrum`;
- whether `rw` or `simpa` is preferred for the restricted-spectrum bridges;
- implicit ambient-space inference in the projection norm estimates.

No theorem statement was weakened.  The general two-sided Sylvester constant
remains `pi / 2`; the ordered branch remains constant one.

## Latent semantic issue exposed by rebuilding

The existing proof of `sinTheta_perturbation` passes
`le_of_mem_Icc hgap` as the interval-order proof.  That expression is not
mathematically justified: `hgap` is an `IntervalExteriorSeparated` predicate,
not membership in an interval, and the predicate currently does not store
`left ≤ right`.

The printed paper speaks of an interval `[left,right]`, so the formal API must
either:

1. carry `left ≤ right` explicitly and propagate it through the symmetric and
   spectral-projection wrappers; or
2. prove that an unordered interval forces the selected source subspace to be
   trivial, discharge that branch directly, and derive `left ≤ right` in the
   nontrivial branch from nonemptiness of the restricted self-adjoint spectrum.

Do not replace this with an unrelated inequality merely to make elaboration
succeed.  This issue is separate from the removed-API migration and may be one
of the remaining errors once the compatibility declarations resolve.
