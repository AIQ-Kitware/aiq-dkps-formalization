# Proof obligations

## Already compiled before this proof attempt

- the finite-dimensional Section 7 UI-norm theorem in the main Davis--Kahan
  tree;
- the finite-carrier ambient extension;
- the local approximation-number spectral-selection stack;
- the arbitrary-Hilbert post-quarter Riccati/Ky-Fan/Fan-dominance estimate.

The retained `paperTanTwoTheta_uiNorm_finite_alternate` is a duplicate finite
regression derivation, not an open obligation and not the completion target.

## Exact bounded completion target

`paperFaithful_tanTwoTheta_uiNorm` must compile exactly as stated, with:

- no `FiniteDimensional` or finite-carrier hypothesis;
- quarter-acuteness derived from the original reducing-subspace, ordered-gap,
  and full off-diagonal hypotheses;
- the conclusion phrased for the canonical ambient
  `tanTwoAngleOperatorC U V hquarter`;
- membership and the sharp factor-two gauge inequality against the full
  perturbation `H`;
- no `sorry`, `admit`, or new axiom.

The current proof attempt writes both missing bridges in full:

1. dimension-free branch selection by reflected centered operators, a
   Lyapunov identity, positive square-root similarity, spectral half-plane
   separation, and reflection algebra;
2. canonical-to-graph tangent transport by the graph projection formula,
   source compressions of sine/cosine, modulus identification, zero extension,
   and complete approximation-number preservation.

The immediate remaining obligation is compiler validation and repair of these
written arguments without narrowing the theorem.  After compilation, run the
repository grounding checks and `#print axioms` on the unrestricted theorem.

The unrestricted unbounded sharp ideal theorem remains separate from this
bounded target.
