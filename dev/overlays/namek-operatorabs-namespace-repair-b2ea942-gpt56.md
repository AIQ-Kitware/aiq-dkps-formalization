# Namek OperatorAbs namespace repair

Target repository: `/home/joncrall/code/aiq-dkps-namek`

This overlay repairs the scratch-local theorem namespaces in
`OperatorAbsoluteValueComplex.lean`.

The two helpers were declared as:

- `DavisKahanExt.SymmetricNormIdeal.operatorAbs_mem_iff_and_gauge_eq`
- `DavisKahanExt.SymmetricNormIdeal.operatorAbs_mem_and_gauge_eq`

inside the already nested scratch namespace. Lean therefore placed them under a
nested scratch `DavisKahanExt` namespace rather than the local
`SymmetricNormIdeal` namespace used by the surrounding scratch API. Later calls
to `SymmetricNormIdeal...` could not resolve them.

The declarations now follow the same local namespace pattern as
`TwoWayFactorization.lean`.
