# FinishTanTwoTheta

This target develops the sharp bounded `tan 2Theta` theorem through
approximation numbers, Riccati coordinates, Ky Fan domination, and symmetric
ideal promotion.

## Current proof structure

The main Davis--Kahan repository already contains the finite-dimensional
Section 7 UI-norm theorem.  The local theorem
`paperTanTwoTheta_uiNorm_finite_alternate` is retained only as an independent
regression derivation through the newer Riccati/approximation-number stack; it
is intentionally labeled duplicate/alternate and is not evidence that the
unrestricted target is complete.

The exact unrestricted bounded target is
`paperFaithful_tanTwoTheta_uiNorm`.  Its statement has no
`FiniteDimensional` or finite-carrier hypothesis, derives quarter-acuteness
from the original ordered-gap and fully off-diagonal perturbation hypotheses,
and estimates the canonical ambient `tanTwoAngleOperatorC` in every source
unitary-invariant ideal.

The new proof attempt contains all mathematical steps and no admission.  Its
two new hard modules are:

- `FinishTanTwoTheta.DavisKahan.InfiniteQuarterAcute`: a dimension-free
  reflection/Lyapunov/spectral proof of the strict quarter-angle branch;
- `FinishTanTwoTheta.DavisKahan.CanonicalTangentBridge`: graph-projection
  algebra identifying the canonical tangent with the graph-coordinate tangent
  at the level of the full approximation-number sequence.

This archive is ready for compiler review.  It must not be described as
compiled or axiom-clean until those modules, `PaperFaithful`, the aggregate,
and `#print axioms` all pass.

## Build order

```bash
scripts/lake_build_report.py --fail-fast \
    FinishTanTwoTheta.DavisKahan.InfiniteQuarterAcute
scripts/lake_build_report.py --fail-fast \
    FinishTanTwoTheta.DavisKahan.CanonicalTangentBridge
scripts/lake_build_report.py --fail-fast \
    FinishTanTwoTheta.DavisKahan.PaperFaithful
scripts/lake_build_report.py --fail-fast FinishTanTwoTheta
```

`FinishTanTwoTheta.DavisKahan.Unbounded` remains a separate research target and
is not silently included in this bounded theorem.
