# FinishTanTwoTheta

This is a temporary, mathematics-first Lean library for completing the sharp
infinite-dimensional `tan 2Theta` theory before moving the polished declarations
into their final Tau Ceti and Davis--Kahan modules.

The sources are grouped under `FinishTanTwoTheta/`, but they are registered as a
non-default library in the repository's root `lakefile.toml`. They therefore use
the root dependency graph and root `.lake/` build directory rather than a nested
Lake workspace.

## Mathematical scope

The library develops four layers.

1. **Standard symmetric ideals.** It uses the repository's proved coherent
   finite-gauge/Fatou theory for maximal ideals and states the missing fully
   symmetric finite-rank-closure theorem for minimal ideals locally. Fan
   dominance is a theorem, not a field hidden in the definition.
2. **Approximate leading singular families.** A PVM spectral-band construction
   for `X*X` supplies simultaneous approximate right/left singular vectors for
   arbitrary bounded operators.
3. **Canonical tangent operator.** For `||X|| < 1`, the operator
   `2 X (I - X*X)^-1` is constructed and its approximation numbers are shown to
   be `2 a_n(X) / (1-a_n(X)^2)`.
4. **Sharp Davis--Kahan estimate.** The stable Riccati coefficient estimate is
   summed and the error removed. A separate unbounded proof uses graph-norm
   residuals, rather than invalid bounded norms of the closed diagonal blocks.

## Grounding policy

Every nonlocal theorem used here was located in either:

- the repository snapshot at merge commit `4285a6e`; or
- Mathlib commit `3dffaf2f18b47d11948f6390838ea6f2ae662aaf`, the commit pinned by the
  repository's Lean 4.32.0 toolchain.

No speculative helper theorem is referenced. New mathematical seams are local
theorems in this library with proof bodies. See `GROUNDING.md` and run:

```bash
python3 FinishTanTwoTheta/scripts/verify_grounding.py
```

## Build order

Run these commands from the repository root. No nested `lake update` is needed:

```bash
lake build FinishTanTwoTheta.Sequence.WeakSubmajorization
lake build FinishTanTwoTheta.OperatorIdeal.StandardFanDominance
lake build FinishTanTwoTheta.OperatorIdeal.StandardInstances
lake build FinishTanTwoTheta.ApproximationNumber.SpectralSelection
lake build FinishTanTwoTheta.FunctionalCalculus.DoubleAngleTangent
lake build FinishTanTwoTheta.DavisKahan.StableRiccatiPair
lake build FinishTanTwoTheta.DavisKahan.SharpKyFan
lake build FinishTanTwoTheta.DavisKahan.SharpIdeal
lake build FinishTanTwoTheta.DavisKahan.Unbounded
lake build FinishTanTwoTheta
```

Because `FinishTanTwoTheta` is not in `defaultTargets`, an ordinary root
`lake build` continues to omit this unfinished library.

The authoring environment did not contain Lean, so this overlay is not claimed
to elaborate. The compiler agent's remaining work should be local proof,
coercion, namespace, or tactic repair. It should not encounter an unknown
constant caused by an invented helper theorem.
