# Historical design note: rectangular singular values and finite frames

**Status: implemented; this is no longer an active roadmap.**  The original
plan motivated a reusable layer for moving between rectangular maps, their two
Gram operators, singular systems, and finite-frame bounds.  Its old
`ForMathlib/...` paths and R1--R5 TODO state are obsolete.

The maintained implementations now live in `ForTauCeti`, including:

- `ForTauCeti/Analysis/InnerProductSpace/RectangularSingularValues.lean`;
- `ForTauCeti/Analysis/InnerProductSpace/Singular/System.lean`;
- `ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean`;
- `ForTauCeti/Probability/Moments/CenteredScatter.lean`.

Downstream DKPS/Quench code imports the maintained declarations rather than this
plan.  Current reusable-library policy is in `ForTauCeti/README.md`.

## Durable mathematical intent

The design goal was to expose the standard equivalence between three views of
finite-dimensional data:

1. a rectangular synthesis/analysis map;
2. the domain Gram operator `T†T`;
3. the codomain Gram operator `TT†`.

The resulting library supplies the nonzero spectral correspondence, singular
value transport under adjoint, intrinsic singular-system reconstruction,
finite-frame/Gram lower-bound bridges, and centered-scatter update identities
needed by the DKPS applications.

This path remains linked from older planning documents because it records the
reason those abstractions were introduced.  Treat any detailed implementation
sequence in Git history as historical, not as outstanding work.
