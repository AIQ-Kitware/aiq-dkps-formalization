# Historical technical note: sharp tan(2Theta) completion

This file is **not a current completion lane**.  The bounded sharp tan(2Theta)
theorem was completed and promoted into the production `DavisKahan` tree.
`FinishTanTwoTheta` now provides a compatibility/regression surface for that
bounded result.

A separate **unbounded research target remains open** in
`FinishTanTwoTheta/FinishTanTwoTheta/DavisKahan/Unbounded.lean`; it is deliberately
outside the package aggregate.  The source files cite this note for the analytic
obstruction that explains why the old proof sketch was abandoned.

Current package status and build instructions live in
`FinishTanTwoTheta/README.md` and `FinishTanTwoTheta/PROOF_OBLIGATIONS.md`.

## T1.1 — durable unbounded-domain lesson

The original selection route tried to obtain approximate singular vectors in
`dom A₀` and `dom A₁` by taking bounded spectral-band vectors, approximating them
by domain vectors, and repairing orthonormality with finite Gram--Schmidt.
Ordinary density only controls the Hilbert norm.  It does not provide the graph
norm or the pairings involving `A₀` and `A₁` that an unbounded argument needs.
Consequently that route cannot justify those stronger residual fields merely by
norm approximation.

The local structure was later weakened from graph-norm residual control to the
pairings actually consumed by the downstream estimate.  Even with that corrected
statement, `exists_unboundedApproximateLeadingSingularFamily` remains the honest
open theorem in the standalone unbounded research file.

The important distinction is:

- failure of the discarded domain-selection mechanism is **not** a
  counterexample to the sharp unbounded tan(2Theta) theorem;
- the completed bounded theorem is independent of this open research target.

## Riccati/Sylvester route

The production unbounded Riccati infrastructure now proves complementary-graph
domain compatibility, the adjoint Riccati equation, and a genuine Sylvester
equation for the double-angle tangent.  Its right-hand side contains the
Riccati-gram commutator term, so that route yields a defect estimate rather than
silently recovering the sharp constant.  This is why comments in
`DavisKahan/Riccati/UnboundedAdjointRiccati.lean` still refer here.

## Validation

```bash
lake build FinishTanTwoTheta
```

The command above validates the bounded compatibility surface.  It does not
claim the separately importable unbounded research file is proof-complete.
