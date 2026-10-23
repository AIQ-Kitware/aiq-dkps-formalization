# Formalizing the Davis--Kahan Perturbation Theorems in Lean

This directory contains a mathematics-first journal manuscript. It reports a
source-level formalization of the 1970 Davis--Kahan paper (28 of 29 identified
results proved at their reviewed scope, Proposition 4.4 refuted as printed),
including the full unbounded sine-theta theorem. The Yu--Wang--Samworth
specialization and its two printed formula corrections are secondary.

## Mathematical additions to Proposition 4.4

The real four-dimensional parameterized counterexample is proved in Lean for
every positive acute principal angle, and hence disproves the printed
short-angle assertion even at arbitrarily small angles. Its complex phase
mechanism already appears in Davis--Kahan Example 4.2; the real example is a
realification of that construction, not a new discovery of trace-norm
nonminimality.

The October 23 source snapshot additionally contains formal proofs of:

- the projection-distance lower bound `N(P_U-P_V) <= N(I-W)` for every
  admissible finite-dimensional real/complex orthogonal/unitary map and
  unitarily invariant seminorm;
- `N(I-R) <= sec(alpha/2) N(P_U-P_V) <= sec(alpha/2) N(I-W)` for
  an acute pair, sharp as a factor uniform over unitarily invariant norms;
- the exact global trace-norm minimum `4 sin(theta)` for the real
  four-dimensional family;
- global complex trace-norm minima for explicit phase-plane models, finite
  direct sums of those models, and their supplied ambient isometric images.

The all-pairs complex trace formula is proved in conventional mathematics but
is **not yet a general Lean theorem**: the formal results require the supplied
principal-plane decomposition. It appears only in an optional red-box working
draft, disabled by default. In `paper.tex`, change
`\includeUnformalizedComplexTracefalse` to
`\includeUnformalizedComplexTracetrue` to inspect that draft. The default
manuscript contains only verified results and precise model-level consequences.

None of these quantitative extensions changes the denominator of the original
29-result source inventory.

## Files and verification

- `paper.tex`: main narrative, sine-theta theorem and selected Lean signature,
  mathematics of the direct-rotation correction, related work and conclusion;
- `counterexample.tex`: detailed real matrices, singular values, the invalid
  Ky Fan step, Q-norm consequence, and 1970--2010 historical context;
- `sharp_displacement.tex`: formalized quantitative bounds, sharpness,
  trace-norm minimizers, and the optional all-pairs complex working draft;
- `appendix_process.tex`: source-result inventory, mathematical correspondence,
  formal ancestry, and targeted proof reproduction;
- `references.bib`: published primary references;
- `PROPOSITION_4_4_LITERATURE_MAP.md`: detailed source/page-level prior-art
  investigation; `submission/LITERATURE_AUDIT.md` is its concise editorial
  summary; `claims_to_evidence.md` maps claims to exact repository declarations.

The source-facing sine-theta theorem is
`TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_whereDefinedUIN_rclike`,
under `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`.
It covers unbounded real/complex operators, the finite-interval/exterior and
ordered half-infinite form-gap alternatives, and where-defined symmetric
operator-ideal norms. The source's positive sine operator equals the modulus
of the rectangular Sylvester block; the two maps have different codomains.

To compile the manuscript:

```bash
make -C papers/dk_formalization_journal paper
```

See `submission/VALIDATION.md` for targeted Lean modules. Run
`lake exe cache get` before Lean builds. Source proof declarations, the
29-result inventory, and manuscript text should be evaluated as separate
claims: Lean compilation establishes the stated formal proposition; the
comparison with the printed source requires independent mathematical review.

The workshop draft under `../dk_formalization_workshop/` studies additional
process questions and does not set this manuscript's scope. Resource
accounting, personal workflow, and downstream application projects are not
part of the journal paper's mathematical contribution.
