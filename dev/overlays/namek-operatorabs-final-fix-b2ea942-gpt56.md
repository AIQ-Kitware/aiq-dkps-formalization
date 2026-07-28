# Namek operator-absolute-value final compile fix

Target worktree:

`/home/joncrall/code/aiq-dkps-namek`

This overlay repairs the final remaining error in
`OperatorAbsoluteValueComplex.lean` after the shared ideal compile-repair
campaign.

The rectangular specialization no longer refers to the fragile local helper
name `SymmetricNormIdeal.modulus_mem_and_gauge_eq`. It derives the same
result directly from the already-elaborated
`SymmetricNormIdeal.operatorAbs_mem_iff_and_gauge_eq` theorem.

Expected verification:

```bash
scripts/lake_build_report.py \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.OperatorAbsoluteValueComplex \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.ReflectionTransport
```
