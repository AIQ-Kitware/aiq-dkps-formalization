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

### Axioms (recorded 2026-07-30, lane CLAIM-DOC)

```
'TauCeti.DavisKahan.FinishTanTwoTheta.paperFaithful_tanTwoTheta_uiNorm'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

The three standard Lean axioms and nothing else — no `sorryAx`, no custom
axiom. This discharges the obligation this document previously listed.

What remains:

* the unrestricted **unbounded** sharp ideal theorem, which is separate work and
  not part of this bounded target.

## This library is not a default build target

`lakefile.toml` does not list `FinishTanTwoTheta` in `defaultTargets`, so a
green `lake build` does **not** compile anything here. The results above are
proved but unguarded: a refactor elsewhere can break them while every gate stays
green. Build it explicitly with `lake build FinishTanTwoTheta`. Adding the
target is tracked as lane `FTT-PROMOTE` in `dev/LANES.md`.

**This is no longer hypothetical.** On 2026-07-30 the library was found broken by
lane CLAIM-DOC: the P-EXP migration retyped the Davis--Kahan ideal-family
interface onto `TauCeti.SymmetricOperatorIdealFamily`, and eight `Experimental`
modules this library depends on still passed the historical
`RectangularSymmetricIdealFamily`. Every default gate was green throughout;
`lake build FinishTanTwoTheta` failed. The modules were retyped and the library
builds again (9204 jobs, 0 errors), but the failure mode this section warns about
occurred exactly as described, roughly a day after it was written down.
