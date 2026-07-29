# FinishTanTwoTheta

This target now builds the **actual bounded sharp proof stack**, not an alias-only
facade.

## Compiled theorem scope

The aggregate target includes:

1. simultaneous approximate leading singular families for arbitrary bounded
   operators;
2. the canonical operator `2 X (I - X*X)^-1` and its approximation-number
   transformation law;
3. the stable Riccati scalar estimate and sharp Ky Fan prefix inequality;
4. Fan-dominance promotion to maximal and minimal standard symmetric ideals;
5. the source audit containing the finite-dimensional Section 7 UI-norm theorem
   and the arbitrary-inner-product-space sharp operator-norm theorem with its
   acute branch.

This is stronger than an alias facade: the `FinishTanTwoTheta` modules that prove
the bounded infinite-dimensional ideal result are imported and compiled.

## Unbounded extension

`FinishTanTwoTheta.DavisKahan.Unbounded` is a separate research target.  Its
current approximate graph-domain selection theorem is not part of the aggregate
because the proposed spectral-band/domain-density route is false.  The genuine
unbounded Sylvester equation with its commutator defect remains available in the
production Davis--Kahan library.

The distinction is deliberate:

- source theorem and bounded ideal completion: proof target;
- unrestricted unbounded sharp ideal extension: open research target, not
  silently weakened and not falsely certified.

## Build

```bash
lake build FinishTanTwoTheta.DavisKahan.SharpIdeal
lake build FinishTanTwoTheta
lake build DavisKahan.Sources.DavisKahan1970.Audits.DoubleAngleTangent
```
