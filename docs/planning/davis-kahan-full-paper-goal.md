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
extension.

### Progress note (2026-07-16, unbounded sin Θ session)

The unbounded extension now has its honest operator-norm layer, fully proved
at `RCLike` generality (axiom audit clean on every declaration) in
`SinTheta/GenuineUnbounded.lean`:

- `ClosedOperator.norm_shift_apply_le_of_form_bounds`: a symmetric closed
  operator with quadratic form in `[β, α]` satisfies
  `‖B y - c y‖ ≤ r ‖y‖` on its domain (`c` center, `r` radius), by
  polarization and density — the unbounded numerical-radius-to-norm bridge.
- `norm_closedSylvester_le_of_intervalExterior` and
  `norm_closedSylvester_le_of_exteriorInterval`: constant-one estimates
  `δ ‖X‖ ≤ ‖C‖` for the domain-aware `ClosedSylvesterEquation`, in both
  orientations, with the exterior block carried by a proof-carrying bounded
  shifted inverse (`LeftShiftedInverseBound` /
  `TwoSidedShiftedInverseBound` — the resolvent reformulation of spectral
  exteriority, to be discharged later by an unbounded spectral theorem).
- `sinTheta_unbounded_opNorm`: **the unbounded Davis--Kahan `sin Θ`
  theorem in operator norm** — for the paper-shaped `UnboundedSinThetaData`
  with the trial block's form in `[β, α]` and the complementary block's
  shifted resolvent bounded by `((α-β)/2 + δ)⁻¹`, the conclusion
  `δ ‖X⋆ ∘ F₁‖ ≤ ‖R⋆ ∘ F₁‖`, through the proved adjoint residual block
  identity.

This lands Davis--Kahan Theorem 5.2 at operator-norm scope with honest
hypotheses.  The paper's full UI-norm scope for 5.2 remains open in
`Sylvester/Unbounded.lean` (Ky Fan cutoff route and the ideal-gauge
interval/exterior route, which additionally needs a gauge-closedness or
Neumann-series argument for ideal membership of the solution).  Elaboration notes for future waves: statements over
`[CStarAlgebra A]` applied to `E →L[ℂ] E` need
`import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`; the
`...ContinuousFunctionalCalculus.Basic` import is required for the base
`ℂ`/`IsStarNormal` instance; and `norm_nonneg`/`add_le_add_left` underscores
against CLM operator-norm goals can send the unifier into whnf timeouts —
use `ContinuousLinearMap.opNorm_nonneg` and `add_le_add le_rfl` instead.

### Progress note (2026-07-16, Spectra activation session)

Three gaps toward "paper theorem complete" closed (axiom audit clean on every
new declaration):

- `sinTheta_genuineSpectrum_symmetric` (`Sylvester/GenuineSpectrum.lean`): the
  **symmetric two-sided genuine-spectrum `sin Θ` theorem** — both directed
  spectral configurations give `d * subspaceGap U V ≤ ‖B - A‖` through the
  max-of-directed-gaps projector identity.
- `sylvester_mem_and_gauge_le_of_unbounded_bound_inverse`
  (`Core/UnboundedSpectral.lean`): the **one-unbounded ideal-gauge Sylvester
  engine**.  The solution is identified as the ideal-gauge limit of the
  Neumann iteration `X = Σ Jⁿ⁺¹ C Bⁿ` (contraction factor `ρ/(ρ+δ) < 1`),
  membership comes from the `gauge_complete` field plus operator-norm limit
  uniqueness, and the estimate `δ · gauge X ≤ gauge C` follows by absorption.
  This is the first fully proved UI-norm-scope Sylvester estimate with an
  unbounded block — the ideal-membership half of Theorem 5.2's
  interval/exterior case at ordinary rectangular-ideal generality.
  (The index universe of `finset_sum_mem`/`gauge_finset_sum_le` in
  `Ideals/Rectangular.lean` was generalized to `Type*` for the ℕ-indexed
  iteration.)
- **Spectra activation and the spectral-theorem discharge**
  (`SpectraBridge/GapResolvent.lean`).  The Stone/spectral-calculus import
  cone of the `external/Spectra` library was repaired for the root
  Lean/Mathlib pin (eight files, mechanical fixes: `map_sub`/`map_add`/
  `map_smul` through subtype mks instead of `convert using 1/2`;
  `convert`-generated instance-path congruence goals closed with `rfl`;
  beta-unreduced `Pi.neg_apply` patterns normalized before `rw`;
  ℂ-coerced scalar measurability in `AEStronglyMeasurable.smul`).  On top of
  it, written Spectra-idiomatically for upstreaming:
  `spectralProjection_eq_zero_of_forall_mem_resolventSet` (pointwise
  resolvent membership kills spectral mass, by second countability),
  `exists_norm_le_two_sided_shifted_inverse_of_spectralProjection_Ioo_eq_zero`
  (the quantitative gap resolvent `‖(A - c)⁻¹‖ ≤ s⁻¹` via the truncated
  symbol and the sharp calculus norm bound), and
  `exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap` for self-adjoint
  `LinearPMap`s.  The DK-side corollaries discharge
  `TwoSidedShiftedInverseBound` from genuine spectrum avoidance
  (`twoSidedShiftedInverseBound_of_spectrum_gap`) and produce
  **`sinTheta_unbounded_opNorm_of_spectrum_gap`: the unbounded `sin Θ`
  theorem whose only spectral hypotheses are the trial block's form bounds
  and genuine (resolvent-set) spectrum avoidance of the complementary
  block** — the resolvent predicate is no longer an undischarged input.
  `SpectraBridge.All` is now registered in the
  `Experimental/InfiniteDimensional` tree.

### Progress note (2026-07-16, UI-norm unbounded sin Θ session)

The paper's unitary-invariant norm scope for the unbounded `sin Θ` theorem
is now proved (`SinTheta/GenuineUnboundedGauge.lean`, all axiom-clean,
`RCLike`-generic):

- `exists_bounded_shift_extension`: a symmetric closed operator with form
  in `[β, α]` has a bounded extension of its centered shift with norm at
  most the radius — `ContinuousLinearMap.extend` along the dense domain
  embedding, with `norm_shift_apply_le_of_form_bounds` as the bound.
- `mem_and_gauge_le_of_boundedLeft_exteriorRight`: the ideal-gauge
  constant-one Sylvester estimate in the `sin Θ` orientation.  The key
  observation: with the interval block realized bounded (`S`) and the
  exterior block carried by a shifted right inverse `J`, the domain-aware
  equation collapses to the everywhere-defined fixed point
  `Y = S Y J - C J`, and the Neumann argument runs entirely on the bounded
  side — no unbounded adjoints, no spectral cutoffs.
- `sinTheta_unbounded_gauge`: `δ · gauge (X⋆F₁) ≤ gauge (R⋆F₁)` with
  ideal membership of `X⋆F₁` — **Davis--Kahan Theorem 5.2's `sin Θ`
  passage at the paper's unitary-invariant norm scope** over any
  `RectangularSymmetricIdealFamily`.
- `SpectraBridge/GapResolvent.lean` adds the genuine-spectrum versions at
  `ℂ`: `sinTheta_unbounded_opNorm_of_spectrum_gap` and
  `sinTheta_unbounded_gauge_of_spectrum_gap`, whose only spectral inputs
  are form bounds and Spectra resolvent-set spectrum avoidance.
- `FullPartIII` aliases: `bounded_sinTheta_genuineSpectrum_symmetric`,
  `unbounded_sinTheta_uiNorm`, `unbounded_sinTheta_opNorm_genuineSpectrum`,
  `unbounded_sinTheta_uiNorm_genuineSpectrum`.

The bounded branch received the same upgrade
(`Sylvester/GenuineSpectrum.lean`):
`mem_and_gauge_sylvester_le_of_spectrum_intervalExterior` (the ideal-gauge
interval/exterior Sylvester estimate with genuine Banach-algebra spectra,
by feeding the CFC shift-and-invert data into the Neumann ideal engine
through `ClosedOperator.ofBounded`), and `sinTheta_genuineSpectrum_gauge`:
**the bounded `sin Θ` theorem at unitary-invariant ideal scope with
genuine spectra** — `B - A` in the family gives
`d · gauge (P_{Vᗮ} P_U) ≤ gauge (B - A)` with membership of the directed
projection composition.  `FullPartIII` aliases:
`bounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`,
`bounded_sinTheta_uiNorm_genuineSpectrum`.

**`sin Θ` scope summary after this session**: genuine spectra + operator
norm + UI norm, at bounded and unbounded scope, directed and (bounded)
symmetric two-sided forms — every combination proved and axiom-clean.

The unbounded interval/exterior Sylvester estimate now also holds at ideal
scope in **both orientations**
(`closedSylvesterEquation_boundedRealization` +
`mem_and_gauge_le_of_exteriorLeft_intervalRight` in
`SinTheta/GenuineUnboundedGauge.lean`): the form-bounded block is realized
bounded through its shift extension, the domain-aware equation extends to
the whole space by density and the closed graph of the exterior block, and
the shifted configuration feeds the Neumann ideal engine.  `FullPartIII`
aliases: `unbounded_sylvester_intervalExterior_uiNorm`,
`unbounded_sylvester_exteriorInterval_uiNorm`.  This is the honest
replacement for the `realSpectrum`-based
`unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap` obligation.

Remaining for "paper theorem complete" on the `sin Θ` family: the Ky Fan
cutoff route for the two semibounded orientations of Theorem 5.2
(`Sylvester/Unbounded.lean`, needs unbounded spectral cutoffs — now within
reach through `spectralProjection`/`spectralCalculus` of the activated
Spectra cone), and real scalars via complexification.  Note the sin Θ
endpoint no longer waits on those: the interval/exterior configuration the
paper uses for the residual bound is fully covered at both operator-norm
and UI-norm scope.

Controlling blocker identified for the two-projection calculus at source
scalar generality: an `RCLike`-generic positive operator square root
(`operatorAbsoluteValue`) is unavailable in Mathlib (operator CFC is
`ℂ`-only) and the repo's `IsPositive.sqrt` is finite-dimensional. The whole
`Core/OperatorAngle` ladder (`sinAngleOperator`, `cosAngleOperator`,
`angleOperator`, and their norm identities) waits on a route decision:
norm-preserving complexification transfer versus a direct order-theoretic
construction, or specializing the infinite-dimensional angle calculus to `ℂ`
with a real-scalar bridge afterward.

**Route decision taken (2026-07-16): specialize to `ℂ`**, consistent with
the genuine-spectrum layer, real bridge by complexification later.  First
rungs proved and axiom-clean:
`ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean` defines
`operatorAbs T = (T⋆T)^(1/2)` via `CFC.sqrt` with the Loewner/StarOrder
instances from `Mathlib.Analysis.InnerProductSpace.StarOrder`, proving
nonnegativity, self-adjointness, the defining square identity, uniqueness,
`‖|T|‖ = ‖T‖`, and the pointwise isometry `‖|T|x‖ = ‖Tx‖`.
`Core/OperatorAngleComplex.lean` then defines
`sinAngleOperatorC U V = |P_U - P_V|` and proves
`‖sinAngleOperatorC U V‖ = subspaceGap U V` — the honest `ℂ` counterparts
of the blocked `sinAngleOperator`/`norm_sinAngleOperator` obligations.
Next rungs: the Halmos two-projection decomposition for
`cosAngleOperatorC`/`sinTwoAngleOperatorC` (`2 sin cos`), then the genuine
`sin 2Θ` theorems. See `dev/sorry-difficulty-ranking.md` for the evolving proof-obligation ranking; verify its totals against the source tree before using them in status claims.
