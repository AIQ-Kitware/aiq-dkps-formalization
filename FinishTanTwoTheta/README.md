# FinishTanTwoTheta

This target builds the bounded sharp Riccati/ideal proof stack and now also
contains the exact paper-facing theorem shape as an explicit admitted target.
It is not an alias-only facade, but a green build is not yet an axiom-clean proof
of the full paper-shaped `tan 2Theta` theorem.

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
   acute branch;
6. `paperFaithful_tanTwoTheta_uiNorm`, an explicit `sorry`-backed statement of
   the missing arbitrary-Hilbert-space source theorem, beginning from the full
   off-diagonal perturbation and concluding both quarter-acuteness and the sharp
   source-norm estimate.

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
