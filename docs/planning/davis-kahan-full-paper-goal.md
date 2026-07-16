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

The source therefore has one canonical theorem family with nested
specializations:

1. unbounded self-adjoint operators with explicit domains and bounded residuals;
2. bounded operators on arbitrary Hilbert spaces as full-domain corollaries;
3. finite-dimensional and matrix forms as further specializations or
   independent weaker-foundation alternatives.

The source exposition may introduce the bounded case first. The formalization
API must not turn that expository order into a loss of theorem generality.

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

### General single-angle root

The first source theorem to own an unqualified API is the generalized
unbounded `sin Theta` theorem. Its dependency ladder is maintained in
`davis-kahan-general-sin-theta-roadmap.md` and consists of:

- densely defined closed self-adjoint operators and domain-aware compositions;
- unbounded spectral projections, cutoffs, and bounded truncations;
- the Section 5 Sylvester estimate for the source gap configurations;
- bounded residual block identities on explicit domains;
- rectangular UI-norm ideals and the Ky Fan dominance passage;
- lower-frame factorization and exact directed-angle identification.

Bounded and finite forms are then derived or retained as scoped alternatives.

### Remaining theorem families

- source-faithful two-subspace geometry and operator angles;
- direct rotation, existence, uniqueness, formulas, and extremality;
- graph/transversality machinery and `tan Theta`;
- reflection theory, `sin 2 Theta`, and `tan 2 Theta`;
- Section 8 continuation, branch selection, canonical spectral subspaces,
  uniqueness, and spectral repulsion;
- unbounded forms of every source result for which the paper supplies them.

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
foundations. Neither is the canonical completion boundary. The immediate
controlling goal is the generalized unbounded single-angle theorem in
`Experimental/InfiniteDimensional/SinTheta/Canonical.lean`; the remaining
four-theorem package, direct-rotation extremal theory, Section 8 package, and
full source audit follow from that foundation.

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

**Statement-soundness repair (2026-07-15).** The former
`Core/AbstractSpectrum.lean` predicates were point-spectrum based and therefore
vacuous for continuous-spectrum self-adjoint operators such as multiplication
by `t` on `L²(0,1)`.  The repaired layer now defines `realSpectrum` by pulling the native
`RCLike` Banach-algebra spectrum back to real scalars and defines
`restrictedSpectrum A U` from `spectrum 𝕜 (A.restrict hU)` for an invariant
subspace.  `SpectrumIn`,
`SpectraSeparated`, `OrderedSpectraSeparated`, and all derived gap predicates
also carry invariance explicitly.  This removes the counterexample that made
the Sylvester, `sin Θ`, ideal, off-diagonal, and Riccati declarations false as
stated.  Those declarations remain open proof obligations: the next analytic
step is to connect these actual restriction spectra to the existing coercive
bounds, using the complex spectral-order bridge first and a real bridge or
complexification transport afterward.

**General sine-theta architecture push (2026-07-15).** The unbounded
closed-operator equation now has an explicit domain-transport field; bounded
operators embed into the same model through `ClosedOperator.ofBounded`; the
unified unbounded Sylvester theorem is assembled by cases from the
interval/exterior and two semibounded orientations; the generalized and
isometric unbounded sine endpoints are reduced to the residual block identity,
Sylvester engine, ideal contraction, lower-frame transport, and exact-angle
identification. `SinTheta/Canonical.lean` now bundles the intended source
problem and reserves the unqualified source role for the generalized unbounded
result. Compiler feedback is expected to drive repair of the newly exposed
seams.

### Progress note (2026-07-16, genuine-spectrum sin Θ session)

The honest layer answering the vacuity finding now exists and its headline is
fully proved (axiom audit: `propext, Classical.choice, Quot.sound` on every
declaration):

- `ForMathlib/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean`: for a
  self-adjoint element of a unital C*-algebra, `‖a‖ ≤ r` when the real
  spectrum lies in `[-r, r]`, and a two-sided inverse of norm at most `r⁻¹`
  when the spectrum avoids `(-r, r)` — both by the isometric continuous
  functional calculus.
- `DavisKahan/Experimental/InfiniteDimensional/Sylvester/GenuineSpectrum.lean`:
  `norm_sylvester_le_of_spectrum_intervalExterior`, the **constant-one
  interval/exterior Sylvester estimate** with genuine Banach-algebra spectra
  (shift-and-invert argument, no splitting, no `π/2` loss), and
  `sinTheta_genuineSpectrum`, the **fully general bounded operator-norm
  Davis--Kahan `sin Θ` theorem**: `U` reducing self-adjoint `A` with
  `spectrum ℝ (A|_U) ⊆ [a, b]`, `V` reducing self-adjoint `B` with
  `spectrum ℝ (B|_{Vᗮ})` outside `(a-d, b+d)` give
  `d · directedGap U V ≤ ‖B - A‖`.  Supporting API: `compressOperator`
  (honest restriction to a reducing subspace), its self-adjointness, the
  cross-block Sylvester equation, and the norm identification of the
  cross-block compression with the directed projection composition.

Scope status: this makes the classical `sin Θ` theorem **bounded
Hilbert-space theorem complete** (complex scalars, operator norm, genuine
spectra).  Remaining for "paper theorem complete": the symmetric/two-sided
form (maximum of the two directed gaps, as in `sinTheta_symmetric`), the
UI-norm/ideal scope, real scalars via complexification, and the unbounded
extension.  Elaboration notes for future waves: statements over
`[CStarAlgebra A]` applied to `E →L[ℂ] E` need
`import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`; the
`...ContinuousFunctionalCalculus.Basic` import is required for the base
`ℂ`/`IsStarNormal` instance; and `norm_nonneg`/`add_le_add_left` underscores
against CLM operator-norm goals can send the unifier into whnf timeouts —
use `ContinuousLinearMap.opNorm_nonneg` and `add_le_add le_rfl` instead.

Controlling blocker identified for the two-projection calculus at source
scalar generality: an `RCLike`-generic positive operator square root
(`operatorAbsoluteValue`) is unavailable in Mathlib (operator CFC is
`ℂ`-only) and the repo's `IsPositive.sqrt` is finite-dimensional. The whole
`Core/OperatorAngle` ladder (`sinAngleOperator`, `cosAngleOperator`,
`angleOperator`, and their norm identities) waits on a route decision:
norm-preserving complexification transfer versus a direct order-theoretic
construction, or specializing the infinite-dimensional angle calculus to `ℂ`
with a real-scalar bridge afterward. See `dev/sorry-difficulty-ranking.md` for the evolving proof-obligation ranking; verify its totals against the source tree before using them in status claims.
