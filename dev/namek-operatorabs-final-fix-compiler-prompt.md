Inspect the latest commit in `/home/joncrall/code/aiq-dkps-namek` and compile:

```bash
scripts/lake_build_report.py \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.OperatorAbsoluteValueComplex \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.ReflectionTransport
```

The overlay fixes the last known `OperatorAbsoluteValueComplex` namespace
lookup by deriving the rectangular result directly from
`SymmetricNormIdeal.operatorAbs_mem_iff_and_gauge_eq`. Repair any remaining
compiler-only issue without weakening statements or using proof escapes.
