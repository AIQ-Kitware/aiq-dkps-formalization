# FinishTanTwoTheta

This target builds the bounded sharp Riccati/ideal proof stack and the complete
finite-dimensional paper-facing `tan 2Theta` endpoint.  The aggregate imports
the proof modules themselves; it is not an alias-only facade.

## Compiled theorem scope

The aggregate target includes:

1. simultaneous approximate leading singular families for arbitrary bounded
   operators;
2. the canonical graph-coordinate operator `2 X (I - X*X)^-1` and its
   approximation-number transformation law;
3. the stable Riccati scalar estimate and sharp Ky Fan prefix inequality;
4. Fan-dominance promotion to maximal and minimal standard symmetric ideals;
5. the finite-dimensional Davis--Kahan/GKMV acute-branch theorem;
6. `paperFaithful_tanTwoTheta_uiNorm`, proved from the original self-adjoint,
   reducing-subspace, common-form-gap, and fully off-diagonal perturbation
   hypotheses.

The paper-facing theorem derives quarter-acuteness, constructs the canonical
contractive graph coordinate, transports the source norm from the full ambient
perturbation to its rectangular upper-right block through exact approximation-
singular-value equality, and concludes

```text
(b - a) * N(tan 2Theta_0) <= 2 * N(H).
```

Here `tan 2Theta_0` is the graph-coordinate representative permitted by the
Section 7 statement.  The theorem deliberately does not identify that
rectangular representative definitionally with an ambient canonical angle
operator.

## Infinite-dimensional boundary

The local Riccati/Ky-Fan machinery proves sharp bounded ideal estimates after a
strictly contractive graph coordinate is supplied.  The source audit also has a
sharp infinite-dimensional ideal theorem for finite-dimensional invariant
configurations.  A source-shaped theorem with an arbitrary infinite-dimensional
reference subspace still requires an independent acute-branch argument and is
not claimed by this target.

`FinishTanTwoTheta.DavisKahan.Unbounded` remains a separate research target. Its
former spectral-band/domain-density route is false; the unrestricted unbounded
sharp ideal extension is not silently weakened or certified here.

## Build

```bash
lake build FinishTanTwoTheta.DavisKahan.PaperFaithful
lake build FinishTanTwoTheta.DavisKahan.SharpIdeal
lake build FinishTanTwoTheta
lake build DavisKahan.Sources.DavisKahan1970.Audits.DoubleAngleTangent
```
