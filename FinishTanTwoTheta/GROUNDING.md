# Grounding

The package distinguishes three theorem layers.

1. The main Davis--Kahan tree already supplies the finite-dimensional Section 7
   theorem and the finite-carrier ambient extension.
2. `paperTanTwoTheta_uiNorm_finite_alternate` duplicates the finite endpoint by
   a different Riccati/approximation-number route and is retained only as a
   regression proof.
3. `paperFaithful_tanTwoTheta_uiNorm` is the actual unrestricted bounded target:
   arbitrary Hilbert space, no finite carrier, a derived quarter-acute branch,
   the canonical ambient tangent, and the sharp source-ideal estimate against
   the full perturbation.

The unrestricted proof attempt is explicit and admission-free.  The branch
argument is in `InfiniteQuarterAcute`; the canonical/graph approximation-number
transport is in `CanonicalTangentBridge`; `PaperFaithful` composes those bridges
with the existing arbitrary-Hilbert post-branch Riccati/Ky-Fan theorem.

This document does **not** claim completion merely because the source is
written.  Grounding requires successful compilation of the three modules and
the aggregate, followed by an axiom audit of
`paperFaithful_tanTwoTheta_uiNorm`.  Until then the status is “complete proof
attempt ready for compiler review,” not “proved.”
