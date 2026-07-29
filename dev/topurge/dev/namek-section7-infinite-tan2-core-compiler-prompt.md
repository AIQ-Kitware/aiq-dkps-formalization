# Compiler handoff: dimension-free tan 2Theta paired-singular-family core

Inspect the latest commit and compile:

```bash
scripts/lake_build_report.py --fail-fast \
    DavisKahan.Experimental.Scratch.Section7.InfiniteTanTwoThetaCore
```

Then compile:

```bash
scripts/lake_build_report.py --fail-fast \
    DavisKahan.Experimental.Scratch.Section7.All
```

The mathematics to preserve is:

1. `exactSingularPair_doubleAngleTangent_le_neg_re_inner` keeps the actual
   matched coefficient `-re <x, B01 y>` from the Riccati identity. Do not
   weaken it to `||B01||`; the coefficient is needed for Ky Fan summation.
2. `kyFan_doubleAngleTangent_le_of_exactSingularFamily` is dimension-free and
   sums that coefficient over orthonormal exact singular pairs using
   `sum_le_kyFanApproximationGauge_of_orthonormal`.
3. `kyFan_doubleAngleTangent_offDiagonal_le_of_exactFamilies` converts a family
   attaining the approximation singular values into the desired prefix bound.
4. `HasExactApproximationSingularFamilies` is intentionally explicit. Do not
   add an axiom, `sorry`, or false blanket instance for arbitrary bounded maps.
   Exact attainment is expected for the future compact-coordinate bridge; the
   fully noncompact theorem needs approximate families plus a limit.

Repair namespace, coercion, inner-product orientation, and algebra/tactic API
issues only. If an exact scalar identity has the opposite inner-product
orientation, use `inner_re_symm`; do not change the sign in the retained
coefficient without rechecking the Riccati equation.
