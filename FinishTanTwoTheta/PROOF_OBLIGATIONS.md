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

## Status: the bounded target is proved

**`paperFaithful_tanTwoTheta_uiNorm` compiles as stated** (2026-07-30,
`FinishTanTwoTheta/DavisKahan/PaperFaithful.lean:408`). The compiler-validation
obligation this document previously described is discharged: both bridges above
were written, repaired, and accepted without narrowing the theorem, and the
library carries **no proof escapes** across its 21 modules.

What remains:

* run `#print axioms` on the unrestricted theorem and record the result here;
* the unrestricted **unbounded** sharp ideal theorem, which is separate work and
  not part of this bounded target.

## This library is not a default build target

`lakefile.toml` does not list `FinishTanTwoTheta` in `defaultTargets`, so a
green `lake build` does **not** compile anything here. The results above are
proved but unguarded: a refactor elsewhere can break them while every gate stays
green. Build it explicitly with `lake build FinishTanTwoTheta`. Adding the
target is tracked as lane `FTT-PROMOTE` in `dev/LANES.md`.
