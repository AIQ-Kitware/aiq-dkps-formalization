# Completion status

The `FinishTanTwoTheta` aggregate has no remaining proof obligation.  It now
exports the exact theorem scopes already proved and axiom-audited in the
distilled Davis--Kahan/GKMV library.

The following stronger statement is deliberately **not** part of the completed
surface:

> an unrestricted sharp infinite-dimensional ideal estimate for an arbitrary
> contractive unbounded Riccati graph.

The old attempted proof required graph-domain approximate singular vectors.
The needed spectral-band/domain-density assertion is false, and the genuine
unbounded Sylvester equation contains a generally nonzero commutator defect.
Consequently that statement remains an open research problem under the current
hypotheses, not a compiler obligation.

The retained experimental files may still be built explicitly for research,
but their status must not be inferred from `lake build FinishTanTwoTheta`.
