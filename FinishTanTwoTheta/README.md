# FinishTanTwoTheta

This temporary library now has a completed, literature-certified target.

`lake build FinishTanTwoTheta` builds the theorem scopes that are actually
proved in the distilled Davis--Kahan/GKMV development:

- sharp finite-dimensional rectangular unitarily-invariant norms;
- sharp ambient-Hilbert operator norm with the acute branch;
- sharp infinite-dimensional finite-carrier Ky Fan/ideal results;
- genuine unbounded spectral-subspace companions at the proved denominator;
- the exact unbounded Sylvester equation with its explicit commutator defect.

The former unrestricted sharp unbounded ideal attempt is not part of the
completion target.  Its graph-domain approximate-singular-family step is false
in the required generality, and the exact Sylvester equation has a nonzero
defect in general.  Those files remain individually available as historical
experiments rather than being hidden or rewritten as proved results.

## Build

From the repository root:

```bash
lake build FinishTanTwoTheta
lake build DavisKahan.Sources.DavisKahan1970.Audits.DoubleAngleTangent
```

The first command builds the completed facade.  The second checks the original
source-facing theorem aliases and prints their axiom dependencies.
