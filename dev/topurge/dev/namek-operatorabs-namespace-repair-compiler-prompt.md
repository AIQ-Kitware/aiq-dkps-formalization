Inspect the latest commit. Build only the shared ideal scratch chain, stopping
at the first failure:

```bash
scripts/lake_build_report.py --fail-fast \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.OperatorAbsoluteValueComplex \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.ReflectionTransport
```

The latest patch changes two accidentally nested theorem declaration names in
`OperatorAbsoluteValueComplex.lean` from
`DavisKahanExt.SymmetricNormIdeal.*` to the scratch-local
`SymmetricNormIdeal.*` namespace. Do not redesign the mathematics. Repair only
new compiler errors, without `sorry`, `admit`, new axioms, or statement changes.
