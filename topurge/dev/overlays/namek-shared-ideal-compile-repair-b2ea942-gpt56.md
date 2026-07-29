# Namek shared ideal scratch compile repair

Target worktree: `/home/joncrall/code/aiq-dkps-namek`

This overlay repairs the next two isolated shared-foundation ideal modules after
`TwoWayFactorization` was made green.

## Files

- `DavisKahan/Experimental/Scratch/SharedFoundations/Ideal/OperatorAbsoluteValueComplex.lean`
- `DavisKahan/Experimental/Scratch/SharedFoundations/Ideal/ReflectionTransport.lean`

## Repairs

### OperatorAbsoluteValueComplex

- Qualify Spectra's bounded `polar_decomposition` to avoid resolving the older
  `ForMathlib` linear-map theorem.
- Replace the unavailable `ContinuousLinearMap.norm_adjoint` rewrite with
  `ContinuousLinearMap.adjoint.norm_map`.
- Replace field notation for scratch-local helper theorems with explicit calls
  through the local `SymmetricNormIdeal` namespace.

### ReflectionTransport

- Prove the reverse gauge inequalities with explicit `calc` chains instead of
  rewriting the goal in the wrong direction.
- Replace field notation for scratch-local reflection helpers with explicit
  namespace calls.
- Swap the two factorizations supplied to
  `mem_iff_and_gauge_eq_of_twoWayContractions`, because the available
  hypothesis is membership of `sinTwoAngleOperator`, not membership of the
  directed block.

## Verification

Run:

```bash
scripts/lake_build_report.py \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.OperatorAbsoluteValueComplex \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.ReflectionTransport
```

This overlay was statically audited but not compiled in the packaging
environment because the host Lake toolchain is unavailable there.
