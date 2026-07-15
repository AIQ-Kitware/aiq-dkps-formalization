# Davis--Kahan 1970: full-paper formalization goal

## Default objective

The default objective is a skeptical-expert-quality formalization of Chandler
Davis and W. M. Kahan, *The Rotation of Eigenvectors by a Perturbation. III*
(1970), in the scope in which the paper states its results.

The finite-dimensional theory is important and should be preserved. It is not
the terminal definition of success unless a task explicitly asks for a
finite-only result.

## Source-verified ambient scope

The maintained modernized transcription states that:

- the ambient space is a separable Hilbert space;
- the subject throughout the main development is a bounded Hermitian operator
  `A` and a modified Hermitian operator `A + H`;
- the results and proofs also apply to unbounded self-adjoint `A` when the
  domain of `H` contains the domain of `A`, with useful conclusions requiring
  the relevant perturbation or residual to be bounded;
- all four headline theorems apply in infinite as well as finite dimensions;
- all four are stated for arbitrary unitary-invariant norms;
- the complications needed to remove inessential boundedness restrictions are
  concentrated in Theorem 5.2 and the Appendix to Section 6.

The source therefore has three connected scopes:

1. bounded operators on arbitrary Hilbert spaces—the main-body foundation;
2. unitary-invariant norm and ideal statements in that setting;
3. unbounded self-adjoint extensions with explicit domain control.

## Status vocabulary

Use scope-qualified claims:

- **finite specialization complete**: a theorem is proved using finite spectra,
  finite singular-value lists, or finite-dimensional UI norms;
- **bounded Hilbert-space theorem complete**: the theorem is proved for bounded
  self-adjoint operators without a finite-dimensional assumption;
- **source norm scope complete**: the theorem supports the unitary-invariant
  norm scope asserted by the paper, with an honest operator-ideal/domain API in
  infinite dimensions;
- **unbounded extension complete**: the source domain assumptions and limiting
  arguments are formalized;
- **paper theorem complete**: the exact source statement, hypotheses,
  orientation, constants, branch conditions, and norm scope are proved;
- **paper complete**: every numbered theorem, proposition, corollary, lemma,
  direct-rotation result, Section 8 selection result, sharpness/equality claim,
  numerical example claim intended for formalization, and unbounded passage has
  been audited and either formalized or explicitly classified as expository.

Do not abbreviate the first status to “Davis--Kahan complete.”

## Role of the finite theory

`DavisKahan/FiniteDimensional/` is retained because it provides:

- arbitrary rectangular UI norms through finite singular-value lists;
- computational and matrix-facing statements;
- weaker-foundation proofs that do not require the infinite-dimensional
  analytic stack;
- explicit equality models and regression tests;
- applications to DKPS, statistics, Ritz methods, and singular subspaces;
- alternative proofs suitable for cherry-picking.

When finite work is undertaken by default, it should close a named seam needed
by the Hilbert-space theorem or be clearly labeled as an alternative endpoint.

## Canonical roadmap

### Bounded main body

- closed/reducing subspaces and orthogonal projections;
- source-faithful two-subspace geometry and operator angles;
- direct rotation, existence, uniqueness, formulas, and extremality;
- bounded Sylvester theorems in the source separation geometries;
- residual and perturbation `sin Theta`;
- graph/transversality machinery and `tan Theta`;
- reflection theory, `sin 2 Theta`, and `tan 2 Theta`;
- Section 8 continuation, branch selection, canonical spectral subspaces,
  uniqueness, and spectral repulsion.

### Unitary-invariant norm scope

The finite `RectangularUnitarilyInvariantNorm` API cannot simply be reused for
all bounded operators. The infinite-dimensional theory needs honest domains of
finiteness, such as compact/symmetric norm ideals, approximation numbers, Ky
Fan norms, Hilbert--Schmidt and Schatten classes, and the relevant ideal and
unitary-invariance laws.

### Unbounded passages

- densely defined self-adjoint operators and domain-aware compositions;
- spectral cutoffs and convergence;
- Theorem 5.2 in its source scope;
- the Appendix to Section 6;
- bounded residual/perturbation hypotheses and passage from cutoffs to the
  unbounded operator.

## Source audit discipline

The local modernized transcription is the authority for source wording and
numbering. Committed distilled notes are independent mathematical summaries;
they may quote only short anchors and should record:

- source section/theorem/equation;
- ambient operator and space assumptions;
- bounded versus unbounded status;
- norm scope and finiteness conventions;
- residual versus perturbation form;
- directed angle convention;
- branch or transversality conclusion;
- exact current Lean declaration and its narrower or broader scope;
- remaining gap before the source statement is represented.

## Current high-level status

The finite-dimensional library contains a strong and valuable package,
including arbitrary rectangular UI-norm sine and tangent results and stable
double-angle endpoints. The bounded branch contains meaningful operator-norm
foundations. The full Hilbert-space four-theorem package, infinite-dimensional
UI-norm/ideal layer, direct-rotation extremal theory, Section 8 package, and
unbounded source passages remain the controlling completion goals.

### Progress note (2026-07-15, easy-ladder closure session)

Fully proved and axiom-clean: the total resolvent interface with both
resolvent identities and Neumann resolvent-set stability
(`Sylvester/Resolvent`); `graphSubspace` as the closure of the parametrized
graph range with an unconditional projection instance and
`graphSubspace_eq_range` for angular operators (`GraphSubspace`); the bounded
and unbounded block-operator constructions on the Hilbert direct sum with the
unbounded block-graph projection instance (`Riccati/Bounded`,
`Riccati/Unbounded`); the Hermitian dilation and its self-adjointness
(`Ideals/CompactAndSingular`); and the explicit planar extremizer
constructions for the `sin Θ`, `sin 2Θ`, and `tan 2Θ` sharpness models (both
`Sharpness` files).

Structurally assembled on top of documented open black boxes:
`sylvester_unique`, `sinTheta_symmetric`, `existsUnique_angularOperator`,
`continuedProjection_eq_spectralProjection`, `schatten_sinTheta`,
`covariance_subspace_sinTheta`, and `tanTwoTheta_spectralSubspace_le`.

**Statement-soundness finding (2026-07-15).** The infinite-dimensional
separation predicates in `Core/AbstractSpectrum.lean` (`restrictedSpectrum`,
`SpectrumIn`, `SpectraSeparated`, `InternalGap`, `IntervalExteriorSeparated`,
`OrderedSpectraSeparated`) are point-spectrum (eigenvector) based.  In
infinite dimensions a self-adjoint operator can have empty point spectrum
(e.g. multiplication by `t` on `L²(0,1)`), which makes every one of these
hypotheses vacuously true while the conclusions fail.  Concrete
counterexample shape: with `A = B` the multiplication operator, `X = 1`,
`C = 0`, the hypothesis of `norm_sylvester_le_of_generalSeparation` holds
vacuously for any `d > 0` yet `d·‖X‖ ≤ (π/2)·‖C‖` is false; the same defect
falsifies `sylvester_solve`/`sylvester_unique`, `sinTheta_perturbation`,
`sinTheta_symmetric`, `ideal_sinTheta`, `compact_projection_difference`, and
the Riccati gap theorems **as stated**.  These are therefore not merely open:
they are unprovable until the predicates are redefined.  (~94 use sites
across 10 InfDim files.)  Route options, in preference order: (1) redefine
`restrictedSpectrum A U` for a reducing `U` as the Banach-algebra spectrum of
the restriction of `A` to `U` (real part via self-adjointness); (2) state the
gap hypotheses through quadratic-form/numerical-range bounds, matching the
already-proved coercivity forms (`norm_sylvester_le_of_coercive`, the
coercivity `sin Θ`), noting that form bounds capture intervals but not
exterior sets, so the interval/exterior family needs genuine spectrum;
(3) keep the current defs strictly as finite-dimensional compatibility and
fork honest infinite-dimensional statements.  This decision gates most
tier-4/5 items in the ranking and should be made before further InfDim
statement-level work.

Controlling blocker identified for the two-projection calculus at source
scalar generality: an `RCLike`-generic positive operator square root
(`operatorAbsoluteValue`) is unavailable in Mathlib (operator CFC is
`ℂ`-only) and the repo's `IsPositive.sqrt` is finite-dimensional. The whole
`Core/OperatorAngle` ladder (`sinAngleOperator`, `cosAngleOperator`,
`angleOperator`, and their norm identities) waits on a route decision:
norm-preserving complexification transfer versus a direct order-theoretic
construction, or specializing the infinite-dimensional angle calculus to `ℂ`
with a real-scalar bridge afterward. See `dev/sorry-difficulty-ranking.md`
(2026-07-15 header) for the updated 178-item ranking.
