# Davis--Kahan 1970 full source census

Base commit: `b967c62f`.

This is the public, independently worded theorem-by-theorem ledger for the
full paper. The maintained modernized transcription is used only as a local
comparison source and is intentionally not distributed. The JSON file is
authoritative; this Markdown file is generated from it.

## Status summary

| Status | Count |
| --- | ---: |
| `compiled_exact` | 33 |
| `compiled_specialization` | 11 |
| `compiled_general_infrastructure` | 0 |
| `proof_written` | 0 |
| `candidate_under_repair` | 0 |
| `partial_or_wrapper_missing` | 0 |
| `not_represented` | 0 |
| `not_started` | 0 |
| `resolved_by_modern_development` | 1 |
| `not_a_completion_obligation` | 3 |
| `refuted_as_transcribed` | 1 |

## Status meanings

- **`compiled_exact`** -- An exact source-facing theorem or construction is compiled on the base.
- **`compiled_specialization`** -- A useful compiled specialization exists, but not the full source scope.
- **`compiled_general_infrastructure`** -- The mathematics exists in a general reusable form, though a source-numbered wrapper may be absent.
- **`proof_written`** -- A source-facing proof has been written and statically audited, but compiler certification is still pending.
- **`candidate_under_repair`** -- A statement/candidate exists in the full Part III repair campaign but is not compiler-certified on this base.
- **`partial_or_wrapper_missing`** -- Substantial ingredients exist, but the exact source theorem is not represented or audited.
- **`not_represented`** -- No matching declaration was found.
- **`not_started`** -- The source artifact has no formalization campaign yet.
- **`resolved_by_modern_development`** -- An open source question has a partial or norm-specific modern resolution in the repository.
- **`not_a_completion_obligation`** -- An open question or exposition item should be documented but is not proof debt.
- **`refuted_as_transcribed`** -- The transcribed statement is disproved by a compiled Lean counterexample; the census row records the refutation pending a re-audit of the printed source text.

## Verification summary

`status` above is the mathematical judgement against the printed
source. `verification` below is what the Lean build certifies, and is
checkable: run `python3 scripts/probe_census_declarations.py --verify`
to confirm every row still matches the build. The default build carries
no `sorry` and no `axiom`, so a declaration reachable from
`DavisKahan.All` is genuinely proved.

| Verification | Count |
| --- | ---: |
| `proved_in_build` | 46 |
| `proved_conditional` | 0 |
| `partially_in_build` | 0 |
| `proved_outside_build` | 0 |
| `not_compiling` | 0 |
| `absent` | 0 |
| `not_applicable` | 3 |

## Verification meanings

- **`proved_in_build`** -- Every declaration resolves against DavisKahan.All. The default build carries no sorry and no axiom, so this is a proof, continuously re-checked by CI.
- **`proved_conditional`** -- Declarations resolve against DavisKahan.All and are proved, but the source conclusion is stated relative to a hypothesis record that no value is ever constructed for, so the paper's claim is assumed rather than derived.
- **`partially_in_build`** -- Some declarations resolve against DavisKahan.All and some do not, so the row's source claim is only partly guarded by CI. `declarations_outside_build` lists the unguarded ones.
- **`proved_outside_build`** -- Declarations compile, but only under DavisKahan/Experimental, which no default target builds. The mathematics is done; it is not guarded against regression and is not reachable from the source facade.
- **`not_compiling`** -- Declarations are written but their package does not compile, so nothing is certified.
- **`absent`** -- No declaration exists.
- **`not_applicable`** -- A documented research question or exposition item. No formalization is intended, so the row is not proof debt and must not be counted as a gap.

## Frontier

Every row that still owes work, grouped by the obstruction standing
in front of it. This includes rows that are already
`proved_in_build`: the mathematics can be proved and CI-guarded while
the source-numbered wrapper is still missing. Obstructions marked
`mechanical` need only wiring or a restatement; `hard_math` needs new
mathematics.

### `real-scalar-infinite-dimensional-scope` -- mixed

**Real Hilbert spaces at infinite dimension**

AUDIT FINDING 2026-08-07 (Claude Opus 5), by dumping the elaborated signature of every declaration on every `compiled_exact` row and classifying it on two axes.

The transcription's standing assumption 1 (prose/distilled_literature/DavisKahan1970_part_III.tex, 'Standing assumptions from the transcription') reads: 'H is a separable Hilbert space, REAL OR COMPLEX, with finite dimensionality only a special case.'  Assumption 4 adds that all four headline theorems are stated as applicable in infinite as well as finite dimensions.  The same section warns explicitly that a Lean theorem with a finite-dimensional assumption 'is not the unqualified paper theorem merely because its formula and constant match the displayed source inequality'.

MEASURED: 17 of the 30 rows then marked `compiled_exact` had NO declaration covering a real Hilbert space of infinite dimension.  The coverage splits into two shapes.  (a) Infinite dimension but `InnerProductSpace ℂ` only -- Section 3's direct-rotation propositions, Theorem 5.2, all of Section 6, and the two headline sine rows.  (b) `RCLike` (so real and complex) but `[FiniteDimensional]` -- Section 4's propositions and corollary.  A row whose declarations are one of each is still not covering real-and-infinite.

This is a SCOPE gap, not a correctness gap: nothing recorded is wrong, and the complex infinite-dimensional statements are the mathematically substantial ones.  But `compiled_exact` is defined as 'an exact source-facing theorem ... is compiled', and complex-only is not exact against a source that says real or complex.

ROUTE: the repository already intends a 'qualified complexification/restriction route' (dev/targeted-mathematical-repair-2026-07-21.md) and carries `DavisKahan/SpectralTheory/Complexification/`.  A real wrapper should go through that rather than by reproving over `RCLike`, since several proofs use the complex continuous functional calculus essentially.  Section 4's finite-dimensional restriction is a separate question and may be defensible -- the source itself notes that singular-value lists may need spectral multiplicity language for noncompact operators -- so check the printed statement before treating it as a gap.

**PARTIAL DISCHARGE 2026-08-09 (Claude Opus 5): the three AMBIENT (whole-space) Section 2 conclusions.**  `tanTheta_wholeSpace_paperUINorm_real`, `sinTwoTheta_wholeSpace_paperUINorm_real` and `tanTwoTheta_wholeSpace_paperUINorm_real` (`DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean`) are the printed `delta ||tan Theta|| <= ||H||`, `delta ||sin 2Theta|| <= 2||H||` and `delta ||tan 2Theta|| <= 2||H||` over a REAL Hilbert space of arbitrary dimension, for every source unitarily invariant norm, with no constant lost and with ideal membership concluded rather than assumed.

WHAT MADE THEM POSSIBLE, and what the earlier ROUTE note omitted: the *conclusions* of these theorems are functional calculi of `|P_U - P_V|`, which the complexification route had no way to bring back to the real space -- `DavisKahan/Geometry/Angle/OperatorAngleReal.lean` evaluates them on `RealComplexification E` and says so.  The missing descent is that the canonical conjugation commutes with the operator modulus and with the continuous functional calculus of a fixed self-adjoint operator with NO continuity side condition (`TauCeti.RealComplexification.conjugateOperator_modulus`, `conjugateOperator_cfc`, added to `ForTauCeti/Analysis/InnerProductSpace/Complexification/FunctionalCalculus.lean`).  With those, every paper angle operator of a real pair is the complexification of a real operator, and `DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean` names the five real ones.

TWO OBSTRUCTIONS FOUND, both real and both recorded on the rows they block.  (1) `KyFanDominantIdealFamily` is scalar-fixed and has no `gauge_complexify`, so any endpoint stated over it -- which is every DIRECTED tan-theta and sin-2-theta endpoint -- cannot be transported as stated; it must be re-derived at `PaperUnitaryInvariantNorm` scope from a Ky Fan core.  (2) `spectrum R` of an operator on a subspace of `RealComplexification E` sits on the real-algebra diamond that `Algebra.complexToReal` and `RealComplexification.instModuleReal` create: the two `Module R` structures are propositionally but not definitionally equal, so a `spectrum R` rewrite across the transport fails.  The working spelling is `TauCeti.DavisKahan.Experimental.Foundation.realSpectrum`, which is `spectrum` over the NATIVE scalar field and therefore diamond-free.

**SECTION 6 TRANCHE DISCHARGED 2026-08-09 (Claude Opus 5, M32).  23 rows -> 19.**  Four of the five Section 6 rows are off this blocker.

TWO OF THEM WERE NEVER BLOCKED.  `DK-6.1-thm` and `DK-6.2-thm` carried the blocker in `blocked_by` even though their own notes recorded, on 2026-08-07, that the finding against them was a FALSE POSITIVE and restored their status.  The blocker entry was simply not removed, so this blocker's count overstated itself by two.  Re-measured by elaboration 2026-08-09: `Theorem6_1_real`, `Theorem6_2_real` and their common-domain and common-core variants are `[InnerProductSpace ℝ]`, `[CompleteSpace]`, free of `[FiniteDimensional]`, with membership concluded, all axiom-clean.

TWO WERE CLOSED BY PROOF, AND NEITHER USED THE ROUTE THIS BLOCKER RECOMMENDS AS ITS DEFAULT.  The ROUTE note above says a real wrapper 'should go through' complexification 'rather than by reproving over `RCLike`, since several proofs use the complex continuous functional calculus essentially'.  That is true of the angle-operator conclusions and false of Section 6's tangent and leakage material.
  * `DK-6.3-lem` (Lemma 6.3): the proof uses no functional calculus.  Seven of its eight supporting declarations are scalar generic verbatim; exactly one step, the Pythagorean splitting of the square energy, was complex-only, and only because the column-energy bridge in `Ideals/HilbertSchmidtBasis.lean` is.  `Section6AppendixLeakage.lean` was therefore generalized to `RCLike` and only that one step transported (`Section6AppendixLeakageReal.lean`).
  * `DK-6.3-thm` (Theorem 6.3): half the real content already existed and was recorded only on `S2-tan-theta`.  What was missing was the FINITE-dimensional real trial space, where the prescribed -approximation-number constructor does not apply; the representative is written down instead, as a diagonal operator in an arbitrary orthonormal basis, using the already-`RCLike` `TauCeti.singularValues_diagOp`.

SO THE STANDING GUIDANCE SHOULD BE READ AS: check first whether the argument is already scalar generic and merely uninstantiated at `ℝ`, and transport only the steps that genuinely are not.  Complexification is the fallback, not the default.

`DK-6-appendix` STAYS BLOCKED: its sine half is real, its tangent half is complex only, and the measured entry point for that lift is written out on the row.

**SECTION 3 DIRECT-ROTATION AND SECTION 4 EXTREMAL TRANCHES DISCHARGED 2026-08-09 (Claude Opus 5, M33).  19 rows -> 11.**  Eight rows come off: `DK-3.1-def`, `DK-3.1-prop`, `DK-3.3-prop`, `DK-3.2-cor`, `DK-4.1-prop`, `DK-4.1-cor`, `DK-4.2-prop`, `DK-4.3-prop`.

ONE CONSTRUCTION CLOSED SECTION 3, and it is the complexification route -- correctly, this time, because the objects are polar factors and not gauges.  `DavisKahan/Geometry/Polar/DirectRotationReal.lean` observes that for a complexified pair the canonical intertwiner `S = P_V P_U + P_Vperp P_Uperp` is the complexification of a real operator, hence conjugation-fixed; `RealComplexification.conjugateOperator_modulus` (M31) makes `|S|` conjugation-fixed; in the acute case `|S|` is a unit, so cancelling it in `W |S| = S` makes the polar factor `W` conjugation-fixed, and `complexify_realPartOperator` returns a bounded operator on the real space.  Every clause of Definition 3.1, Proposition 3.1, Proposition 3.3 and Corollary 3.2 is then a rewrite through `complexify_injective`.

SECTION 4 NEEDED NO NEW ANALYSIS AT ALL, AND THIS BLOCKER'S OWN ROWS SAID OTHERWISE.  The `next_action` on `DK-4.1-prop`, `DK-4.1-cor` and `DK-4.3-prop` each read 'Real scalars, through the complexification route rather than a reproof', which reads as machinery still to be written.  MEASURED: `DavisKahan/OperatorIdeal/ComplexificationApproximation.lean` had ALREADY proved that a real operator and its complexification have EQUAL approximation numbers and equal finite Ky Fan approximation gauges (`approximationNumber_complexify`, `kyFanApproximationGauge_complexify`), built for the real Ky Fan ideal work and recorded on no Section 4 row.  The single missing ingredient was a real MINIMIZER, which the Section 3 construction above supplies.  Proposition 4.2 transported even more cheaply: its proof is two Cauchy--Schwarz steps and its termwise bound is evaluated directly on the real copy.

OBSTRUCTION (1) ABOVE IS NARROWER THAN IT READS.  It says any endpoint stated over `KyFanDominantIdealFamily` 'cannot be transported as stated'.  That is a statement about transporting a COMPLEX family's gauge onto real operators.  It does not prevent stating the real endpoint over a REAL `KyFanDominantIdealFamily`: the structure is `RCLike`-generic, and the certificate/bridge pair `RestrictedDisplacementApproximationDominance` / `restrictedDisplacement_idealGauge_le` is `RCLike`-generic too, so a real certificate feeds a real family with nothing transported but the approximation numbers.  Corollary 4.1 over `R` is proved exactly that way.

TWO ROWS OF THE SAME TRANCHE STAY BLOCKED, with named obstructions written on the rows: `DK-3.2-prop`, because it classifies up to isometric equivalence of the crossed defect spaces and that does not descend through complexification -- the same obstruction already excluded for Theorem 3.1 and Corollary 3.1; and `DK-3.5-prop`, because the `Theta`-level commutations it is about have no infinite-dimensional COMPLEX form to transport, only `RCLike` finite-dimensional ones.

**M34, 2026-08-09 (Claude Opus 5): 11 rows -> 9, of which one was never blocked at all.**

* `S2-sin-theta` was a STALE entry.  Its own 2026-08-07 note had already restored `compiled_exact` and recorded "No mathematical gap"; only the `blocked_by` reference was left behind.  Re-verified by elaboration and removed.
* `S2-sin-two-theta` is CLOSED.  The one residual the row had named -- a real unbounded operator-norm statement whose conclusion names a real `sin 2Theta` angle operator -- is proved.  The smallest object that had to descend was the block-to-angle identification, and it descends because the canonical reflected overlap block can be written map-free as `P_U . J_V . P_{U^perp} . J_V` (`sinTwoThetaIdealBlock_eq_comp`, scalar-generic), at which point every factor already had a complexification identity.
* `S2-unbounded-scope` keeps the blocker, but its `scope_gap` text was FALSE and is corrected on the row: `unbounded_sinTheta_opNorm` is `RCLike`-generic, and the real unbounded sine and double-angle-sine families are compiled.  What is genuinely complex-only is the unbounded TANGENT tree, and the fixing there is a convention rather than a mathematical dependency.
* `DK-9-model` keeps the blocker and should keep it: its scalar axis cannot use this route at all, because `Lp C 2 mu` is not presented as `RealComplexification (Lp R 2 mu)` and no such isometry exists locally.

METHOD NOTE, third time this has bitten the census: before recording a real-scalar gap on a row, elaborate candidates from the WHOLE repository, not the declarations already listed on the row.  Two of the four rows examined in M34 carried claims that a repository-wide search refutes.

**M35, 2026-08-09 (Claude Opus 5): 9 rows -> 8, and a correction to how the remaining tangent tree was described.**

`DK-6-appendix` comes off.  Its own `scope_gap` had named the entry point exactly -- "a real `Theorem63TrialData`, its complexification through `complexifySubmoduleEquiv`, and a real `crossed_lower_of_reducing`" -- and that is what was built, except that no duplicate real structures were needed: `Theorem63TrialData`, `UnboundedTrialBlock`, `Theorem63TrialData.ofUnbounded` and `crossed_lower_of_reducing` are bounded data and pure block algebra, so they were restated over `RCLike` in place, verbatim.

`S2-unbounded-scope` KEEPS the blocker, but only for the unbounded `tan 2Theta` operator-norm residual theorem; its single-angle tangent family is now real at arbitrary trial dimension.

THE ROUTE NOTE AT THE TOP OF THIS BLOCKER IS VINDICATED HERE, AND SO IS THE M32 QUALIFICATION.  The tangent tree's DATA layer was scalar-generic and merely uninstantiated at `ℝ` (M32's guidance), while its Appendix passage rests on the ℂ-only bounded projection-valued measure through `TauCeti.BorelCalculus.exists_finiteDimensional_le_almostInvariant` and had to be transported (this blocker's original guidance).  A row that mixes the two should be measured link by link before a route is chosen: a claim that a whole tree is "complex by convention" is worth nothing until the finite-projector selection steps in it have been checked against `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/`.

Gates: S2-unbounded-scope (proved_in_build), DK-3.1-thm (proved_in_build), DK-3.5-prop (proved_in_build), DK-8.1-thm (proved_in_build), DK-8.2-thm (proved_in_build), DK-9-model (proved_in_build)


## Source ledger

### Section 1

#### Section 1, equations (1.1)–(1.8): Two reducing decompositions and the residual

- **Kind:** `construction`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Block decompositions for A and A+H, trial and exact coordinate maps, and R = (A+H)E0 - E0 A0.
- **Current Lean references:** `TauCeti.DavisKahan.residual`, `TauCeti.DavisKahan1970.Equation1_8`, `TauCeti.DavisKahan1970.equation1_8_eq_perturbation_comp`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.residual_eq_comp_subtypeL`, `TauCeti.DavisKahan1970.equation1_8_norm_sq_eq_diagonal_add_offDiagonal`, `TauCeti.DavisKahan1970.equation1_8_norm_offDiagonal_le`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperTheorem61Data`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.UnboundedSinThetaData`
- **Assessment:** The exact notation is distributed across the Section 6 source data records rather than exposed as a Section 1 facade.

**M37, 2026-08-09 (Claude Opus 5).  THE `exact-source-wrappers` BLOCKER IS RETIRED, AND THIS ROW IS WHERE ITS TEXT IS PRESERVED.**

Verbatim, as it stood in the `blockers` table, because the standing observation it makes is still worth reading:

> **Source-numbered wrappers over already-proved general theorems** (kind: mechanical).  The mathematics is in the build in a more general form; what is missing is a statement carrying the paper's numbering, scope and hypotheses, so the facade can cite it.

MEASURED 2026-08-09 by elaborating every declaration on all six of its rows against `DavisKahan.All`: FOUR OF THE SIX HAD NOTHING OUTSTANDING.  `DK-3.1-def`, `DK-3.2-def`, `DK-7-sin2-proof` and `DK-7-tan2-proof` were already `compiled_exact`, and their own notes had recorded -- on 2026-08-06 and 2026-08-07 -- that the requested wrapper existed; only the `blocked_by` reference was left behind.  The blocker's count therefore overstated itself by four, exactly the failure already recorded for `DK-6.1-thm` and `DK-6.2-thm` on the other blocker.  Only `DK-3.4-prop` carried real work, and that work was not mechanical; see its note.

THIS ROW'S OWN PREMISE WAS ALSO PARTLY FALSE.  The `notes` said the Section 1 notation is 'distributed across the Section 6 source data records rather than exposed as a Section 1 facade', and the row listed only those two records.  It missed that equation (1.8) itself is a compiled definition -- `TauCeti.DavisKahan.residual`, `R = (A + H)E₀ - E₀A₀` -- and that the Section 1 remark `R = HE₀` is a compiled theorem, `residual_eq_comp_subtypeL` in `DavisKahan/Frontier/Section8Residual.lean`, where Theorem 8.2's residual branch consumes it.  Both are now listed.

WHAT M37 ADDED: `DavisKahan/Sources/DavisKahan1970/Section1.lean`, the source-numbered facade, in the established `Section5.lean` style -- the two existing results are cited by `:=` (`alias`), not restated, so there is a single source of truth.  The one Section 1 claim that was genuinely not compiled is now proved: `R⋆R = H₀² + B⋆B`, stated as the quadratic form `‖Ru‖² = ‖H₀u‖² + ‖Bu‖²` (over ℂ a self-adjoint operator is determined by its quadratic form, and this spelling needs neither of the paper's coordinate isometries), together with the consequence the paper draws from it -- the residual is smallest exactly when `H₀ = 0`, which is what makes the Rayleigh-quotient choice `A₀ = E₀⋆(A + H)E₀` a good one.  Both axiom-clean.
- **Next action:** Nothing outstanding for equation (1.8) or for either Section 1 claim about it.  The block representations (1.2)--(1.3) are notation, and the way this repository spells them differs from the print; that difference is recorded in `scope_gap` rather than left as proof debt.  One residual clause is compiled in a weaker shape than printed, and is recorded here rather than left implicit: the remark that `‖R‖` is minimized by taking `H₀ = 0` quantifies over choices of the trial operator `A₀`, whereas `equation1_8_norm_offDiagonal_le` fixes `A₀` at the unperturbed compression and compares pointwise, with equality at `u` exactly when the diagonal block kills `u`.  That is the mechanism of the printed remark, not the optimization statement; ranging over `A₀` would make the trial operator a variable of the statement, which `DavisKahan.residual`'s signature does not.

#### Section 1, equations (1.9)–(1.13): Unitary-invariant norms and Fan dominance

- **Kind:** `framework`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Norms determined by singular values, contraction laws, Ky Fan prefix norms, and dominance by all prefixes.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperUnitaryInvariantNorm`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperUnitaryInvariantNorm.prefixGauge_le_of_all_kyFan_le_hetero`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.paperKyFanNorm`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.paperKyFanNorm_gauge`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.paperKyFanNorm_extendedGauge`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.all_kyFan_le_of_every_paperNorm_extendedGauge_le`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.all_mul_kyFan_le_of_every_paperNorm_gauge_le`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.re_sum_inner_map_le_kyFanApproximationGauge`, `TauCeti.DavisKahan1970.equation1_12`, `TauCeti.DavisKahan1970.equation1_12_gauge_comp_starProjection_le`, `TauCeti.DavisKahan1970.equation1_13_compressions`, `TauCeti.DavisKahan1970.equation1_13_reSum`, `TauCeti.DavisKahan1970.equation1_13_gauge_starProjection_comp_le`, `TauCeti.ApproximationNumber.exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner`, `TauCeti.ApproximationNumber.exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner_complex`, `TauCeti.RectangularUnitarilyInvariantSeminorm.exists_orthonormal_re_sum_inner_map_eq_rectangularKyFanSum`, `ContinuousLinearMap.approximationNumber_comp_eq_of_leftInverse`, `ContinuousLinearMap.kyFanGauge_comp_eq_of_leftInverse`, `TauCeti.ApproximationNumber.kyFanApproximationGauge_comp_eq_of_leftInverse`
- **Assessment:** The source norm correspondence is part of the clean Section 6 surface.

**(1.12) AND BOTH FORMS OF (1.13) ARE NOW COMPILED, 2026-08-09 (Claude Opus 5, M38).  THE ROW MOVES TO `compiled_exact`.**  New module `DavisKahan/Sources/DavisKahan1970/Section1UnitaryInvariantNorms.lean`:

* `equation1_12` -- `IsLUB {||K Omega||_nu : Omega a nu-projector on the domain} (||K||_nu)`, the Rayleigh--Ritz principle of (1.12), with the projector written `(Submodule.span C (Set.range v)).starProjection` for an orthonormal nu-tuple `v`;
* `equation1_13_compressions` -- the first form of (1.13), `IsLUB {||Upsilon K Omega||_nu} (||K||_nu)` over pairs of nu-projectors;
* `equation1_13_reSum` -- the second form of (1.13), `IsLUB {Re sum_k <y_k, K x_k>} (||K||_nu)` over pairs of orthonormal nu-tuples.  This is the form the Appendix to Section 6 invokes (transcription L2150);
* `equation1_12_gauge_comp_starProjection_le` and `equation1_13_gauge_starProjection_comp_le` -- the `<=` halves on their own, valid for every orthogonal projector with no dimension hypothesis at all.

**THEY ARE SUPREMA, NOT MAXIMA, AND THAT IS THE MATHEMATICS.**  The mission brief warned that an `exists Omega, ||K Omega||_nu = ||K||_nu` statement would be false in infinite dimensions and the warning is correct: take `K` diagonal with entries `1 - 1/n` on an orthonormal basis.  Every approximation number of that `K` is `1`, so `||K||_nu = nu`; but `||Kx|| < ||x||` for every `x /= 0`, so every nu-dimensional compression is strictly smaller.  `IsLUB` is the correct reading of the printed `sup`, and it is what the Appendix to Section 6 actually consumes -- it invokes (1.13) with an `eta > 0` slack, never with an attained maximum.

TWO NEW GENERAL RESULTS UNDERWRITE THEM, both in `ForTauCeti` and both `RCLike`-generic:

* `RectangularUnitarilyInvariantSeminorm.exists_orthonormal_re_sum_inner_map_eq_rectangularKyFanSum` -- the achievability half of the *rectangular* finite-dimensional Ky Fan variational principle, `(A : E ->l[K] F) (hkE : k <= finrank K E) (hkF : k <= finrank K F)`.  The square case `exists_orthonormal_re_sum_inner_map_eq` reads the codomain family off the polar unitary; a rectangular `A` has no polar unitary, so the codomain family is built by normalizing the images `sigma_i^-1 A v_i` of the directions with `sigma_i /= 0` and completing with `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`.
* `ApproximationNumber.exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner` -- the infinite-dimensional approximate attaining family: for every `eps > 0`, orthonormal `u`, `v` with `kyFanApproximationGauge k K - eps <= re sum_i <u_i, K v_i>`, for arbitrary Hilbert spaces, carrying the min--max localization as the explicit hypothesis `ContinuousLinearMap.HasMinMaxLowerBound`.  The proof pushes each of the `k` approximation numbers onto a finite-dimensional restriction (min--max), joins the `k` witnesses into one finite-dimensional `W`, compresses the codomain, and applies the rectangular principle there.  `..._complex` discharges the hypothesis over `C`.

WHY THE FACADE IS `C`-ONLY.  Not fidelity -- the paper's field is `C` -- but availability: the min--max localization `HasMinMaxLowerBound` is proved in this library for `R` (by complexification) and for `C` (by the functional calculus), and nothing reduces an abstract `RCLike` field to those two.  The `RCLike`-generic statement exists and is the `ForTauCeti` theorem named above; the facade is that theorem instantiated.  The `<=` halves were already `RCLike`-generic and are cited by `:=`, not reproved.

PRIOR WORK ON THIS ROW, RETAINED.  The Ky Fan biconditional (transcription L567) is complete in both directions: `PaperUnitaryInvariantNorm.prefixGauge_le_of_all_kyFan_le_hetero` forward, and `paperKyFanNorm` / `paperKyFanNorm_gauge` / `all_kyFan_le_of_every_paperNorm_extendedGauge_le` / `all_mul_kyFan_le_of_every_paperNorm_gauge_le` converse, all axiom-clean and resolving from `DavisKahan.All`.  Every declaration listed on this row is `[propext, Classical.choice, Quot.sound]`.

STATUS SET TO `compiled_specialization`, NOT `compiled_exact`, ON INTEGRATION 2026-08-09 (Claude Opus 5).  M38 recorded `compiled_exact` with the codomain-room hypothesis on `equation1_12` disclosed in `scope_gap`, and offered the downgrade.  Taking it, because the two room hypotheses are NOT the same kind of thing.  `hE` (an orthonormal `nu`-tuple in the domain) is not a narrowing at all: without it the printed supremum ranges over an empty set of `nu`-dimensional projectors and (1.12) has no content, so the hypothesis is part of the printed claim rather than an addition to it.  `hF` (an orthonormal `nu`-tuple in the CODOMAIN) is a genuine addition.  Printed (1.12) is true without it -- for `K` into a one-dimensional `F` at `nu = 2`, `||K||_2 = ||K||` and every rank-two compression has gauge at most `||K||`, with the supremum equal -- and it excludes a class the paper permits: an operator whose codomain has finite dimension below `nu`.  It enters only through the proof, which needs room on both sides for the rectangular Ky Fan principle.  So the compiled (1.12) is not the full source scope, which is exactly what `compiled_specialization` says.  Everything else on this row is exact: both forms of (1.13) carry both room hypotheses because the printed suprema themselves quantify over `nu`-tuples on both sides, so there they are the printed claim.  The removal route is worked out and recorded in `next_action`; when it lands this row goes to `compiled_exact` with no other change.

**THE (1.12) CODOMAIN-ROOM HYPOTHESIS IS GONE, 2026-08-09 (Claude Opus 5, coordinator integration of a scoped subagent mission).  THE ROW MOVES TO `compiled_exact`.**  `equation1_12` now reads `(K : E ->L[C] F) {nu : N} (hE : exists x : Fin nu -> E, Orthonormal C x)` with the same `IsLUB` conclusion, the same indexing set and the same right-hand side.

**THE ROUTE THIS ROW PREVIOUSLY RECORDED IN `next_action` WAS WRONG.**  It proposed running the attaining argument at `nu' = min nu (finrank W')` on the strength of `rectangularKyFanSum_eq_minFinrank_of_minFinrank_le`.  MEASURED 2026-08-09: that lemma sits in the finite-dimensional singular-value layer of `ForTauCeti/Analysis/InnerProductSpace/SchattenNorm.lean` under section instances `[FiniteDimensional K E]` AND `[FiniteDimensional K F]`, and is about `rectangularKyFanSum` of an `A : E ->l[K] F`.  It cannot speak about `kyFanApproximationGauge` of a bounded `K : E ->L[C] F` on possibly infinite-dimensional spaces.  The same false route was recorded in mission A of `dev/davis-kahan-1970-completion-handoff.md`, which has been corrected.  The route also needed an orthonormal extension from `Fin nu'` to `Fin nu` inside a possibly infinite-dimensional domain, which was never proved.

**WHAT WORKED: PAD THE CODOMAIN.**  `hF` was an artifact of the attaining engine `exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner_complex`, which returns an orthonormal `nu`-tuple in EACH space and therefore cannot run when `dim F < nu`.  The conclusion of (1.12) never mentions the codomain, so replace `F` by the L2 sum `WithLp 2 (F x EuclideanSpace C (Fin nu))` along the inclusion `iota` of `F` as the first summand.  The projection back is a left inverse and both maps are contractions, so every Ky Fan gauge is blind to the substitution and the epsilon-bound proved in the padded space is a bound in `F`.  No case split on `dim F`, no finrank arithmetic, no orthonormal extension.

THREE NEW REUSABLE DECLARATIONS underwrite it, each grounding the next by `:=`, and all three are now listed on this row: `ContinuousLinearMap.approximationNumber_comp_eq_of_leftInverse` (`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean`) -- over an arbitrary nontrivially normed field, with NO inner product, completeness or dimension hypothesis: if `||iota|| <= 1`, `||pi|| <= 1` and `pi . iota = id` then `(iota .L T).approximationNumber n = T.approximationNumber n`; `ContinuousLinearMap.kyFanGauge_comp_eq_of_leftInverse` (`.../KyFan.lean`), the same summed over the prefix; and `TauCeti.ApproximationNumber.kyFanApproximationGauge_comp_eq_of_leftInverse` (`.../Core.lean`), the spelling the source facade speaks.
- **Next action:** Nothing outstanding.  (1.9)--(1.11), the Ky Fan biconditional, (1.12) and both forms of (1.13) are compiled, axiom-clean, and carry no unprinted hypothesis.

### Section 2

#### Section 2, sin theta theorem: Single-angle sine theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Interval/exterior spectral separation gives delta times the directed sine norm bounded by the residual norm for every source unitary-invariant norm.
- **Current Lean references:** `TauCeti.DavisKahan1970.sinTheta`, `TauCeti.DavisKahan1970.generalizedSinTheta`, `TauCeti.DavisKahan1970.sinTheta_real_exactPaper`, `TauCeti.DavisKahan1970.generalizedSinTheta_real_exactPaper`
- **Assessment:** The definitive source form is Theorem 6.1; real, complex, bounded, unbounded, and arbitrary-representative forms are present.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  FALSE POSITIVE, restored to `compiled_exact`.  `sinTheta_real_exactPaper` and `generalizedSinTheta_real_exactPaper` elaborate over `[InnerProductSpace ℝ]` with `[CompleteSpace]` and NO `[FiniteDimensional]`, i.e. a real Hilbert space of arbitrary dimension.  Their `PaperRealIsometricTheoremData` / `PaperRealTheorem61Data` parameters were checked field by field against the conclusion-as-hypothesis failure mode: every field is a printed hypothesis (self-adjointness of the ambient/trial/complement operators, orthogonal exact decomposition, `0 < gap`, lower frame bound, `FormBoundedSylvesterGap`).  `PaperSinThetaRepresentativeAcross` carries only `operator` plus `SameApproximationSingularSequence operator canonical`, which is the paper's own freedom in naming `sin Theta_0`, and `.canonical` inhabits it with the canonical block, so it generalizes the conclusion rather than assuming it.

**BLOCKER REMOVED 2026-08-09 (Claude Opus 5, M34): `real-scalar-infinite-dimensional-scope` was a STALE entry on this row.**  The 2026-08-07 correction recorded directly above had already restored the status to `compiled_exact` and set `next_action` to "No mathematical gap", but the `blocked_by` reference was never dropped with it, so for two days the row reported a scalar gap that its own notes said it did not have.  RE-VERIFIED by elaboration at this HEAD, not by reading the note: `sinTheta_real_exactPaper` and `generalizedSinTheta_real_exactPaper` carry `[NormedAddCommGroup _] [InnerProductSpace R _] [CompleteSpace _]` on every one of `E`, `F`, `G`, `H`, `E_0`, `F_0`, with NO `[FiniteDimensional]` anywhere, and conclude `N.Mem S.operator AND P.gap * N.gauge S.operator <= N.gauge P.data.residual` for an arbitrary `PaperUnitaryInvariantNorm`, with ideal membership CONCLUDED.  That is a real Hilbert space of arbitrary dimension at every source unitarily invariant norm, which is exactly what the blocker asks for.
- **Next action:** No mathematical gap. Keep the source audit synchronized.

#### Section 2, tan theta theorem: Single-angle tangent theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** One-sided spectral separation plus the Rayleigh–Ritz/off-diagonal condition gives residual and perturbation tangent bounds in every unitary-invariant norm.
- **Current Lean references:** `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`, `TauCeti.DavisKahanExt.tanTheta_spectrum`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_of_formBounds_equalRank`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_equalRank_spectral`, `TauCeti.DavisKahan.Experimental.MathAhead.Section2.theorem63Residual_eq_neg_of_invariant`, `TauCeti.DavisKahan.Experimental.MathAhead.Section2.theorem6_3_perturbation_equalRank`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_infiniteTrial_spectral_exists`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_infiniteTrial_of_formBounds_exists`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_all_kyFan_core_infiniteTrial`, `TauCeti.DavisKahan.Experimental.MathAhead.Section2.theorem6_3_perturbation_infiniteTrial`, `TauCeti.DavisKahanExt.paperTanAngleOperatorC`, `TauCeti.DavisKahanExt.paperCos_mul_paperTan`, `TauCeti.ApproximationNumber.approximationNumber_le_of_gramResolvent`, `TauCeti.DavisKahan1970.twoProjection_anticommutator`, `TauCeti.DavisKahan1970.offDiagonal_sq`, `TauCeti.DavisKahan1970.paperProjectorDifference`, `TauCeti.DavisKahan1970.paperSecantSquared`, `TauCeti.DavisKahan1970.paperTanBlockRepresentative`, `TauCeti.DavisKahan1970.paperTanBlockRepresentative_mul_self`, `TauCeti.DavisKahan1970.paperTanAngleOperatorC_eq_modulus_blockRepresentative`, `TauCeti.DavisKahan1970.gramOperator_lowerCorner_moebius`, `TauCeti.DavisKahan1970.approximationNumber_lowerCorner_le`, `TauCeti.DavisKahan1970.corner_all_kyFan`, `TauCeti.DavisKahan1970.tanTheta_wholeSpace_all_kyFan`, `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm`, `TauCeti.DavisKahanExt.paperTanAngleOperatorR`, `TauCeti.DavisKahanExt.complexify_paperTanAngleOperatorR`, `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real`, `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_infinite`, `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteTrial_real`, `TauCeti.DavisKahan1970.theorem63DirectedSineBlockReal`, `TauCeti.DavisKahan1970.theorem63ResidualReal`, `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real`, `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`, `TauCeti.DavisKahan1970.tanTheta_wholeSpace_all_kyFan_of_crossedDefectsEquivalent`, `TauCeti.DavisKahan1970.norm_sinAngleOperatorC_lt_one_of_crossedDefectsEquivalent`, `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_spectral`, `TauCeti.DavisKahan1970.tanTheta_directed_perturbation_paperUINorm_real`, `TauCeti.DavisKahan1970.theorem63ResidualReal_eq_neg_of_invariant`, `TauCeti.DavisKahan1970.approximationSingularValue_theorem63ResidualReal_le_of_invariant`
- **Assessment:** Finite arbitrary-UI-norm and Hilbert-space operator-norm forms are compiled. The source Hilbert-space arbitrary-UI-norm residual and perturbation statements remain open.

**2026-08-05: the Theorem 6.3 core this row is told to reuse is now unconditional.** It had been stated relative to a tangent representative that nothing constructed; `ExactTanTheta.theorem63DirectedTangent` is now that representative and `theorem6_3_all_kyFan_core_directedTangent` needs no hypothesis beyond the printed ones.  See DK-6.3-thm for the details.  What remains for this row is unchanged: the source Hilbert-space arbitrary-UI-norm residual and perturbation statements at EQUAL rank -- Theorem 6.3 assumes `rank Z < rank V`, and the strict inequality is genuinely used only to make the directed reading meaningful, so the equal-rank statement needs its own argument, not a specialisation.

**THE RESIDUAL HALF IS DONE AT SOURCE SCOPE, 2026-08-05.** `theorem6_3_generalizedTanTheta_equalRank_spectral` (default build, axiom-clean, aliased as `theorem6_3_equalRank_tanTheta_ideal`): arbitrary complete complex Hilbert space, finite-dimensional trial space, arbitrary Fan-dominant unitarily invariant ideal gauge, spectral separation in the source's `[beta,alpha]` / `[alpha+delta,inf)` form, **and no comparison of the ranks of `Z` and `V`** -- which is what made it inapplicable to Section 2 before, since Section 2's pair has equal rank.

WHY THE RANK HYPOTHESIS COULD SIMPLY GO.  Davis and Kahan's `dim X(E_0) < dim X(F_0)` does one job in the printed argument: under the paper's global separability convention it forces the trial coordinate space to be finite-dimensional, because every infinite-dimensional closed subspace of a separable space has the same Hilbert dimension.  In the formalisation finite-dimensionality of `Z` is an explicit instance, so the comparison is redundant -- and Lean had been recording that for some time, binding it as `_hStrictDimension` in `theorem6_3_generalizedTanTheta_of_formBounds` and never using it.  Nothing had to be reproved; the hypothesis had to be *noticed*.

This half also depends on the tangent representative built the same day (see DK-6.3-thm), so it is unconditional in both senses: no assumed representative and no dimension comparison.

**THE PERTURBATION COMPANION IS DONE, 2026-08-05, and it needed no new estimate.** `theorem6_3_perturbation_equalRank` (`Sources/DavisKahan1970/Section2TanThetaPerturbation.lean`, default build, axiom-clean): if the finite-dimensional trial space `Z` is invariant for the perturbed operator `T + E`, and `T` reduces `V` with the source gap, then `delta * N(tan Theta_0) <= N(E restricted to Z)` for every Fan-dominant unitarily invariant ideal gauge, in an arbitrary complete complex Hilbert space, with no rank comparison and no assumed tangent representative.

THE BRIDGE IS ONE LINE OF ALGEBRA.  `residual(T,Z) = P_Zperp T|_Z = P_Zperp (T+E)|_Z - P_Zperp E|_Z = - P_Zperp E|_Z`, because invariance of `Z` under `T+E` kills the middle term (`theorem63Residual_eq_neg_of_invariant`).  So the residual is a contraction applied to the restricted perturbation; approximation numbers dominate termwise, and Fan dominance carries that to the ideal gauge.  No part of the tangent estimate had to be redone.

WHY THE RIGHT-HAND SIDE IS `E` RESTRICTED TO `Z`, not `E`: the two live in different spaces (`Z -> H` versus `H -> H`), so an ideal gauge cannot compare them at all, and the restriction is both what the estimate controls and the sharper statement.

**THE EQUAL-DIMENSIONAL INFINITE/NONCOMPACT CASE IS DONE, 2026-08-05 (second session).** The Appendix finite-projector cutoff/Ky-Fan limiting passage is formalized in DavisKahan/TanTheta/Theorem63InfiniteTrial.lean: `theorem6_3_all_kyFan_core_infiniteTrial` proves the prefix Ky Fan tangent inequalities with NO dimension hypothesis on the trial subspace, and the ideal-gauge endpoints `theorem6_3_infiniteTrial_spectral_exists` / `_of_formBounds_exists` exhibit a tangent representative with the paper approximation numbers (finite trial spaces reuse the diagonal representative; infinite ones realise the prescribed antitone sequence through ForTauCeti PrescribedSequence).  The perturbation companion `theorem6_3_perturbation_infiniteTrial` follows by the same one-line bridge.  HOW THE LIMIT IS TAKEN: min-max localization beats every strict lower bound of each sine value on a finite subspace of the trial space; the almost-invariant enlargement (ForTauCeti BorelCalculus/AlmostInvariant, spectral-band slicing through boundedPVM) makes one finite subspace nearly attain all k sine values while the compression leaks at most epsilon; the finite Ky Fan core plus the leakage comparison kyFan_k(residual F) <= kyFan_k(residual Z) + k*epsilon then squeezes.  The pole at sine = 1 never occurs: a sine value at one would push the tangent bound past every threshold (`approximationSingularValue_sineBlock_lt_one_infiniteTrial`).

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  FALSE NEGATIVE in the other direction: this row was left `compiled_exact` with no `scope_gap` at all, because the earlier pass flagged a row only when it noticed the omission, and it never checked the tan family.  The corrected repo-wide search finds no real endpoint, so the row is downgraded here -- on the strength of a whole-repo search, not of the row's declaration list.  Closing it should go through the existing complexification machinery (`DavisKahan/SpectralTheory/Complexification/`, `ForTauCeti/Analysis/InnerProductSpace/Complexification/`, `approximationNumber_complexify`, `kyFanApproximationGauge_complexify`) rather than re-proving anything.

**SHARED ADAPTER LANDED 2026-08-07 (Claude Opus 5).**  `complexifySubmoduleEquiv (Z : Submodule ℝ E) : RealComplexification ↥Z ≃ₗᵢ[ℂ] ↥(complexifySubmodule Z)` (`DavisKahan/SpectralTheory/Complexification/SubmoduleEquiv.lean`, axiom-clean, in the default build) removes the first load-bearing obstruction to the real lift on this row.  The problem it solves: a real configuration carries an operator on `↥Z`, complexifying lands on `RealComplexification ↥Z`, and every complex theorem here speaks about `↥(complexifySubmodule Z)`.  Canonically the same space, NOT definitionally equal.  `re`/`im` are preserved on the nose, so conjugating a compression or residual through it is mechanical.  It is deliberately an isometric equivalence rather than a definitional identification, because the ideal/norm layer only needs equality of approximation singular values and unitary conjugation gives exactly that.  For Theorem 6.3 the remaining steps are: conjugate `theorem63Compression` and `theorem63Residual` of the complexified data through this equivalence, transport the spectral/form hypotheses, apply the existing complex cores (`theorem6_3_all_kyFan_core_infiniteTrial`, `theorem6_3_perturbation_infiniteTrial`) at each Ky Fan level, and finish with the RCLike-generic `PaperUnitaryInvariantNorm.mul_gauge_le_of_all_mul_kyFan_le` plus `gauge_complexify`.  Do NOT transport a scalar-specific `KyFanDominantIdealFamily`.

**THE AMBIENT `Theta` HALF IS STILL OPEN, and this row had not been recording it, 2026-08-08 (Claude Opus 5).**  The printed theorem has TWO conclusions -- `delta ||tan Theta_0|| <= ||R||` AND `delta ||tan Theta|| <= ||H||` (transcription lines 738-747).  Everything listed above, and every claim of completeness in the notes above, is about the DIRECTED `Theta_0` half.  The ambient `Theta` half is not proved, in any scalar field or dimension.

What landed towards it this session: the ambient object itself, `TauCeti.DavisKahanExt.paperTanAngleOperatorC := cfc Real.tan (paperAngleOperatorC U V)` (`DavisKahan/Geometry/Angle/PaperTanAngle.lean`, default build, `[propext, Classical.choice, Quot.sound]`), with `paperTanAngleOperatorC_nonneg` and `paperCos_mul_paperTan` (`cos Theta . tan Theta = sin Theta` under uniform transversality `||sin Theta|| < 1`), which is what makes it the tangent rather than an arbitrary functional calculus.

Also landed, as the foundation the ambient half needs: `TauCeti.modulus_comp_left_cfc` and its polar instance `TauCeti.modulus_polarPartial_comp_cfc_modulus` (`ForTauCeti/Analysis/InnerProductSpace/PrincipalAngles/Equisingular.lean`), the identity `|J f(Theta)| = |f(Theta)|` for `f` vanishing at the origin.  This is the step that lets the paper's off-diagonal representative `[[0, -J_0* f(Theta_1)],[J_0 f(Theta_0), 0]]` be substituted for the block-diagonal `f(Theta)` inside ANY unitarily invariant norm, not merely with the same singular-value list.  It is an operator identity (equal Gram operators), so it survives noncompactness.

**THE AMBIENT `Theta` HALF IS PROVED, 2026-08-09 (Claude Opus 5), at arbitrary Hilbert-space dimension and every unitarily invariant norm.**  `DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean` (default build through `DavisKahan.Sources.DavisKahan1970.All`, every new declaration `[propext, Classical.choice, Quot.sound]`).

`tanTheta_wholeSpace_all_kyFan`: for `T` symmetric with `T.Reduces V`, `A` self-adjoint with `U` invariant for `A`, the Theorem 6.3 form gap (`re <compression of T to U> <= alpha` and `(alpha + delta) ||y||^2 <= re <T y, y>` on `V-perp`), and uniform transversality `||sinAngleOperatorC U V|| < 1`, one has `delta * kyFan_k (paperTanAngleOperatorC U V) <= kyFan_k (T - A)` for every `k`.  `tanTheta_wholeSpace_paperUINorm` is the source form `delta * N (tan Theta) <= N (H)` for every `PaperUnitaryInvariantNorm`, with the membership conclusion `N.Mem (tan Theta)` supplied rather than assumed.  Arbitrary complete complex Hilbert space; no dimension, compactness, or separability hypothesis anywhere; the trial subspace `U` is arbitrary.

CORRECTION TO THE PARAGRAPH THIS REPLACES (which said the ambient half was blocked until `theorem63DirectedTangent` was identified with a functional calculus of the paper angle).  That diagnosis was wrong twice over.

(a) The identification did land -- `theorem63DirectedTangent_eq_subtype_comp_cfcTan_sourceDirectedAngle` (`DavisKahan/TanTheta/Theorem63DirectedAngleBridge.lean`, commit `16a8efcc`) -- but it carries `[FiniteDimensional C Z]` on the trial space, exactly as `theorem63DirectedTangent` itself does.  It therefore could not have unblocked the Section 2 ambient claim, which is asserted at arbitrary dimension.  It is a genuine and useful result about the finite-dimensional trial case; it is not the missing step, and the completed proof does not use it.

(b) The equisingularity identity `TauCeti.modulus_comp_left_cfc` / `modulus_polarPartial_comp_cfc_modulus` is likewise not used.  The proof builds the off-diagonal representative EXPLICITLY instead of factoring the paper's `J_0 tan Theta_0` through a polar partial isometry.  With `p = P_U`, `D = P_V - P_U` and `s = D^2` (`= sin^2 Theta`), `paperTanBlockRepresentative U V = ((1-p) D p + p D (1-p)) (1 - s)^{-1}`, and `paperTanAngleOperatorC_eq_modulus_blockRepresentative` proves `|paperTanBlockRepresentative U V| = tan Theta` -- equality of MODULI, not of singular-value lists, so the substitution is legitimate inside every unitarily invariant norm.  The only geometric input is the two-projection relation `D p + p D + D^2 = D` (`twoProjection_anticommutator`), from which `offDiagonal_sq` gives `((1-p) D p + p D (1-p))^2 = D^2 - D^4 = sin^2 Theta cos^2 Theta`.

WHAT THE MISSING STEP ACTUALLY WAS.  Theorem 6.3's Ky Fan core (`theorem6_3_all_kyFan_core_infiniteTrial`) bounds the SCALARS `sum_{n<k} tan (arcsin s_n)` of the directed sine block, not the approximation numbers of any tangent operator.  Feeding it into Lemma 6.1 requires transferring approximation numbers through the monotone map `u |-> u/(1-u)`, i.e. `a_n(f(A)) <= f(a_n(A))` for increasing `f` -- and that is NOT a consequence of any pointwise estimate, because a subspace on which `||A x|| <= t ||x||` says nothing about `f(A)` there unless the subspace is invariant.  The new ForTauCeti lemma `TauCeti.ApproximationNumber.approximationNumber_le_of_gramResolvent` (`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/GramResolvent.lean`) supplies it by a Gram spectral cut, in the same style as `approximationNumber_gramOperator_le_sq`: if `T = Q + Q T` with `Q = X*X` and `||X|| < 1`, then `a_n(T) <= a_n(X)^2 / (1 - a_n(X)^2) = tan(arcsin a_n(X))^2`.  Applied with `X = P_{V-perp} P_U` this is exactly `a_n(corner of tan Theta) <= tan (arcsin s_n)`.

WHERE THE PROOF IS SHORTER THAN THE PAPER'S.  Davis and Kahan bound the two corners separately and need `||J_0 tan Theta_0|| = ||J_0* tan Theta_1|| = ||tan Theta_0||`, i.e. that `Theta_0` and `Theta_1` have the same nonzero spectrum.  Here `D` is self-adjoint and commutes with `(1-s)^{-1}`, so the two corners of the representative are literally adjoints of one another (`upperCorner_eq_adjoint_lowerCorner`), as are the two corners of the self-adjoint perturbation `H`; the second estimate is the adjoint of the first and `Theta_1` never appears.  Likewise the printed final step `||[[0,B*],[B,0]]|| <= ||[[0,B*],[B,H_1]]|| = ||H||` uses `H_0 = 0` only to identify the middle matrix with `H`.  Applying the Lemma 6.2 pinch (`paperDiagonalPair_all_kyFan_le`) to `H` itself with the two decompositions crossed goes straight from `H` to its off-diagonal part, so `H_0 = 0` is not needed at that step.  It is absorbed elsewhere: the Lean hypotheses are `U` invariant for `A` (which makes the Ritz residual of `U` equal to the lower corner of `H`) plus the Theorem 6.3 form bound on the compression of the PERTURBED operator, both of which the paper's `H_0 = 0` and `spectrum A_0 subset [beta, alpha]` imply.

WHY TRANSVERSALITY IS A HYPOTHESIS AND NOT A DEFECT.  `Real.tan` is total in Mathlib, so `cfc Real.tan (paperAngleOperatorC U V)` exists unconditionally, but it is the paper's tangent only where the angle stays below `pi/2`.  `||sin Theta|| < 1` is exactly that condition, and exactly the condition under which the printed right-hand side can be finite.  It is not a compactness or dimension hypothesis and is not implied by the directed gap: the directed bound only controls `||P_{V-perp} P_U||`, while `||P_U - P_V|| = max(||P_{V-perp} P_U||, ||P_{U-perp} P_V||)`.

WHAT REMAINS ON THIS ROW.  Real scalars.  Both halves are stated for `InnerProductSpace C`; the real-scalar lift is the `scope_gap` recorded below and is unchanged by this work.

**THE AMBIENT HALF NOW HAS A REAL-SCALAR ENDPOINT, 2026-08-09 (Claude Opus 5).  THE DIRECTED HALF DOES NOT.**  `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real` (`DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean`, default build, `[propext, Classical.choice, Quot.sound]`) is the second printed conclusion `delta ||tan Theta|| <= ||H||` over a REAL Hilbert space of arbitrary dimension, for every `PaperUnitaryInvariantNorm`, with the membership conclusion supplied rather than assumed and with no constant lost.

It is a genuine real statement, not a complex statement with a real hypothesis: `E` is `[InnerProductSpace R E]`, the operators are `E ->L[R] E`, the subspaces are `Submodule R E`, and the conclusion is about `TauCeti.DavisKahanExt.paperTanAngleOperatorR U V : E ->L[R] E`.  That object is the real restriction of the complex `tan Theta` of the complexified pair (`complexify_paperTanAngleOperatorR`), which is legitimate because every operator in the chain `|P_U - P_V| -> arcsin -> tan` is a continuous functional calculus of a complexified real operator and therefore lies in the fixed-point algebra of the canonical conjugation (`ForTauCeti` `conjugateOperator_modulus`, `conjugateOperator_cfc`); the real content of the objects is pinned down independently by `paperSinAngleOperatorR_mul_self` (`sin Theta . sin Theta = (P_U - P_V)^2`), `paperSinAngleOperatorR_nonneg` and `norm_paperSinAngleOperatorR`.

The DIRECTED half is still complex-only, and the census's own recipe for it (see `next_action`) understates one step: the complex directed endpoints `theorem6_3_infiniteTrial_of_formBounds{,_exists}` are stated for `KyFanDominantIdealFamily (C)`, whose gauge has no complexification transport, so the real directed statement has to be reassembled from `theorem6_3_all_kyFan_core_infiniteTrial` at `PaperUnitaryInvariantNorm` scope.  Beyond that reassembly, the `_exists` form additionally needs a REAL tangent representative, and `TauCeti.ApproximationNumber.exists_approximationNumber_eq_of_antitone` (`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/PrescribedSequence.lean`) is stated over `C` only.  Generalising that file to `RCLike` is the prerequisite; nothing else in the route is scalar-specific.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 18 is UPHELD: the row recorded only
the real-scalar axis and did not record that the ambient half `tanTheta_wholeSpace_paperUINorm` carries
`||sinAngleOperatorC U V|| < 1` as a hypothesis, where the printed theorem derives transversality from
the spectral placement.  It is now the second axis in `scope_gap`, and it is the same asymmetry as on
`DK-8.2-thm`: a Section 3 standing assumption the formalization replaces with a stronger explicit
one.

**THE AMBIENT TRANSVERSALITY HYPOTHESIS IS GONE, 2026-08-10 (Claude Opus 5, coordinator-verified).**  `||sin Theta|| < 1` is NO LONGER A HYPOTHESIS of the ambient `tan Theta` endpoints: `tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent` and `tanTheta_wholeSpace_all_kyFan_of_crossedDefectsEquivalent` derive it, with real twins in `DirectedReal.lean`.  This closes the audit finding at `dev/davis-kahan-1970-final-audit-2026-08-09.md:516-517`.

**HANDOFF SECTION C.4'S RECIPE FOR THIS IS WRONG AND SHOULD BE CORRECTED.**  It names `isTransverse_of_tanThetaIntervalGap` and (1.5); NEITHER is used or usable.  (i) `isTransverse_of_tanThetaIntervalGap` (`FiniteDimensional/TanTheta/RitzResidual.lean:54`) fails twice: it genuinely binds `[FiniteDimensional]` on BOTH spaces, with no `omit`, going through `LinearMap.adjoint` and the finite spectral theorem; and its conclusion `IsTransverse` is the QUALITATIVE `U inf Vperp = bot`, whereas the ambient theorem needs the QUANTITATIVE `||sinAngleOperatorC U V|| < 1`.  The qualitative-to-quantitative bridge `projectionGap_lt_one_of_isAcute` is itself finite-dimensional, and the repository documents that it FAILS in infinite dimension.  (ii) `isAcute_of_projectionGap_lt_one` is dimension-free but points BACKWARDS -- it CONSUMES `projectionGap < 1`, which is precisely the ambient theorem's input, so it cannot appear in any working path.  (iii) **(1.5) IS NOT NEEDED AT ALL**; the directed bound is unconditional, so only (3.5) does work.

WHAT ACTUALLY WORKED, needing NO new mathematics: `approximationSingularValue_sineBlock_lt_one_infiniteTrial` (`DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:378`) already bounds the directed sine block below one from the tangent theorem's OWN form bounds, dimension-free.  Chain: directed estimate at index 0, then `approximationNumber_index_zero`, giving `||paperDirectedSineAmbient U V|| < 1` which IS `directedGap U V < 1` by definition, then the (3.5) geometry `subspaceGap_eq_directedGap_of_crossedDefectsEquivalent`, then `norm_sinAngleOperatorC`.

UNEXAMINED AND LIKELY THE SAME: whether the whole-space `tan 2Theta` and `sin 2Theta` endpoints carry the same removable hypothesis.  Candidates measured 2026-08-10: `tanTwoTheta_wholeSpace_all_kyFan` and `tanTheta_wholeSpace_paperUINorm` (`TanTwoThetaWholeSpace.lean:1426, :1495`), `sinTwoTheta_wholeSpace_all_kyFan` and `sinTwoTheta_wholeSpace_paperUINorm` (`SinTwoThetaWholeSpace.lean:350, :372`), and the branch-free pair in `TanTwoThetaAmbientBranchFree.lean:206, :259`.  If the same wiring applies it would close hypotheses on further rows.

**THIS ROW CONTRADICTED ITSELF, AND THE CONTRADICTION COST A MISSION'S FRAMING.  Recorded so the pattern is visible.**  On 2026-08-10 the coordinator scoped a mission from this row's `next_action`, which read `REAL SCALARS, DIRECTED HALF ONLY`.  The same row's `scope_gap` already said, in capitals, `THE REAL-SCALAR AXIS IS NOW CLOSED FOR BOTH HALVES`, and named `tanTheta_directed_paperUINorm_real` (`DirectedReal.lean:418`) as the closing declaration.  The coordinator had even cited that declaration in the brief as background while framing the endpoint as missing.  LESSON, general: these fields go stale INDEPENDENTLY, nothing cross-checks them, and NO GATE READS ANY OF THEM -- `probe_census_declarations.py` only checks the declarations a row NAMES.  Read `status`, `blocked_by`, `scope_gap`, `next_action` AND the tail of `notes` together before scoping from a row; when they disagree the newest dated statement wins and the others are the bug.

The mission was salvaged rather than wasted: it landed the two orientations that genuinely did NOT exist -- the real SPECTRAL orientation (`tanTheta_directed_paperUINorm_real_spectral`, the real twin of `tanTheta_directed_paperUINorm_spectral`, with the spectral-to-form conversion done NATIVELY over `R` by `SpectralOrder.Real.upperFormBoundOn_top_of_spectrum_subset_Iic` and `lowerFormBoundOn_of_restriction_spectrum_subset_Ici`, so NO complexification was needed) and the real PERTURBATION companion, which existed at no scope.  The conjugation route the `next_action` prescribed was never needed: it had already been done by an earlier session and sits in `DirectedReal.lean:82-182`.

The `next_action` prerequisite `first generalise PrescribedSequence.lean from C to RCLike` was ALSO already discharged -- that file's variable block at line 40 is `{K : Type*} [RCLike K]` -- caught by the coordinator before dispatch.
- **Next action:** Nothing outstanding.

#### Section 2, sin 2 theta theorem: Double-angle sine theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** Off-diagonal or fully separated perturbations give residual and perturbation sin(2 Theta) bounds with factor two.  ONE PRINTED CLAIM IS OUTSTANDING ON THIS ROW: the unequal-dimension extension dim X(E0) < dim X(F0) asserted in the closing sentence of Section 8, which is stated nowhere.  The directed half over real scalars at every source UI norm was DELIVERED 2026-08-09 and is no longer outstanding.
- **Current Lean references:** `TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm`, `TauCeti.DavisKahan.Experimental.sinTwoTheta_addBounded_of_spectrum_gap`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_real`, `TauCeti.DavisKahan1970.sinTwoTheta_addBounded_paperUINorm_real`, `TauCeti.DavisKahan1970.sinTwoTheta_reflectionResidual_paperUINorm_real`, `TauCeti.DavisKahan.Experimental.sinTwoTheta_addBounded_gauge_real`, `TauCeti.DavisKahan.Experimental.sinTwoTheta_reflectionResidual_gauge_real`, `TauCeti.DavisKahanExt.sinTwoTheta_perturbation`, `TauCeti.DavisKahanExt.sinTwoTheta_generalSeparation`, `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm`, `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`, `TauCeti.DavisKahanExt.paperSinTwoAngleOperatorR`, `TauCeti.DavisKahanExt.complexify_paperSinTwoAngleOperatorR`, `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_all_kyFan`, `TauCeti.DavisKahan1970.symmetric_sinTheta_spectrum_all_kyFan`, `TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC_eq_modulus_starProjection_sub`, `TauCeti.DavisKahan.Experimental.norm_sinTwoThetaIdealBlock_real`, `TauCeti.DavisKahan.Experimental.sinTwoThetaIdealBlock_eq_comp`, `TauCeti.DavisKahan.Experimental.complexify_sinTwoThetaIdealBlock`, `TauCeti.DavisKahanExt.norm_paperSinTwoAngleOperatorC_eq_norm_sinTwoAngleOperatorC`, `TauCeti.DavisKahan1970.norm_sinTwoThetaBlock_real`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_opNorm_real`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_reflectionResidual_opNorm_real`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_unequalDimension`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real_unequalDimension`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_real_unequalDimension`
- **Assessment:** Finite arbitrary-UI-norm forms are compiled; general Hilbert-space source forms are under repair.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The UI-norm Part III double-angle theorem is compiled and axiom-clean; the source-general residual and perturbation forms are not yet certified (see next_action).

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**ROW WAS STALE; CORRECTED 2026-08-05.**  The next_action asked to "certify source-general residual and perturbation forms".  Both already existed, and had since 2026-07-22 (commit 46d545a5), in `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean`, already inside `namespace TauCeti.DavisKahan1970`:

* `unbounded_sinTwoTheta_uiNorm_representative` -- the PERTURBATION form, `delta * N(sin 2Theta_0) <= 2 * N(E)`, sharp factor two;
* `unbounded_sinTwoTheta_residual_uiNorm_representative` -- the RESIDUAL form, `delta * N(sin 2Theta_0) <= N(R)`, constant one.

Both are at the source-general scope this row was waiting for: arbitrary complete complex Hilbert space, unbounded closed self-adjoint `A`, arbitrary `KyFanDominantIdealFamily`, and an arbitrary `sin 2Theta_0` representative rather than a fixed codomain realization -- the paper does not fix one either.  The spectral-gap hypotheses (`hBlow`, `hBhigh`, `hBcomplSpec`) are the printed separation between the two exact blocks.

VERIFIED 2026-08-05 by the elaborator: both names resolve from `DavisKahan.All` alone -- so they are in the DEFAULT build, not merely in `Experimental` -- and `#print axioms` on each gives exactly `[propext, Classical.choice, Quot.sound]`.  No new mathematics was needed to close this row; the declarations were simply never added to it.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**THIRD-PASS AUDIT CORRECTION 2026-08-07 (Claude Opus 5).**  This row was downgraded on the strength of its four listed declarations.  Two more exist that the list omitted, and both are scalar-generic and dimension-free.  This is the same failure mode twice over: a census row's declaration list is a lower bound on coverage, never a measurement of it.  Recording it here because the row was downgraded by me on 2026-08-07 and the downgrade was only half right.

**SHARED ADAPTER LANDED 2026-08-07 (Claude Opus 5).**  `complexifySubmoduleEquiv (Z : Submodule ℝ E) : RealComplexification ↥Z ≃ₗᵢ[ℂ] ↥(complexifySubmodule Z)` (`DavisKahan/SpectralTheory/Complexification/SubmoduleEquiv.lean`, axiom-clean, in the default build) removes the first load-bearing obstruction to the real lift on this row.  The problem it solves: a real configuration carries an operator on `↥Z`, complexifying lands on `RealComplexification ↥Z`, and every complex theorem here speaks about `↥(complexifySubmodule Z)`.  Canonically the same space, NOT definitionally equal.  `re`/`im` are preserved on the nose, so conjugating a compression or residual through it is mechanical.  It is deliberately an isometric equivalence rather than a definitional identification, because the ideal/norm layer only needs equality of approximation singular values and unitary conjugation gives exactly that.

**A PRINTED CLAIM ABOUT THIS THEOREM LIVES AT THE END OF SECTION 8, recorded here 2026-08-07 (Claude Opus 5) during the Section 8 close-out.**  The last sentence of Section 8 reads: "The sin 2theta theorem can be extended to the case dim X(E_0) < dim X(F_0), similarly to Theorems 6.1 and 6.3.  No corresponding extension of the tan 2theta theorem is known."  The first half is an unequal-dimension extension of THIS theorem, asserted without proof ("similarly to"); the second half is an open question and not proof debt.  It is filed against this row rather than against a Section 8 row because it is a claim about the sin 2theta theorem, not about Theorem 8.1 or 8.2.  It is one of the reasons this row is `compiled_specialization` rather than `compiled_exact`, and it is not a Section 8 obligation.

**SUB-PROBLEM C (unequal dimensions), PARTIAL DELIVERY 2026-08-08 (Claude Opus 5).  STATUS DELIBERATELY UNCHANGED.**  The *geometric* content of the announced extension is now compiled; the theorem itself is not, so this row stays `compiled_specialization`.

What landed, in `ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/Gram.lean` (all `[propext, Classical.choice, Quot.sound]`):

* `TauCeti.gram_comp_of_gram_eq_id_sub` -- if `C*C = 1 - T T*` then `(C T)*(C T) = M - M^2` for `M = T*T`.  Three independent coordinate spaces; no direct rotation, no dimension comparison.
* `TauCeti.gram_two_smul_comp` -- hence the Gram operator of `2 (C T)` is `4 (M - M^2)`.
* `TauCeti.gram_two_smul_comp_apply_of_eigenvector` -- on an eigenvector of `M` for `s^2` that Gram operator acts by `sin(2 arcsin s)^2`, i.e. the matching singular value of `2 (C T)` is `sin 2theta` for `s = sin theta`.
* `TauCeti.gram_isometryBlock_eq_id_sub` -- the paper's blocks satisfy the hypothesis: `(F_0* E_0)*(F_0* E_0) = 1 - (E_0* F_1)(E_0* F_1)*`, from `F_0F_0* + F_1F_1* = 1` and `E_0` isometric.
* `TauCeti.adjoint_comp_isometryBlock_eq_zero` -- `F_0* F_1 = 0`.
* `TauCeti.adjoint_reflection_comp_isometryBlock` -- the Section 7 display `(X F_0)* F_1 = 2 (F_0* E_0)(E_0* F_1)` for `X = 2 E_0E_0* - 1`.
* `TauCeti.gram_adjoint_reflection_comp_isometryBlock` -- the two combined: the reflected cross block has exactly `sin 2Theta_0` singular data, with NO hypothesis relating `dim X(E_0)` to `dim X(F_0)`.
* `TauCeti.gram_sinTwoAngleOperator` -- the same fact in ambient projector form: `sinTwoAngleOperator U V` has Gram `4 (M - M^2)` for `M` the Gram of `cosThetaMap U V`, for arbitrary `U, V`.

This is what the paper leaves implicit when it says "extended ... similarly to Theorems 6.1 and 6.3": the only step of the Section 7 argument that names `Theta_0` is the cross block `(X F_0)* F_1`, and the lemmas above show that block is rectangular and its singular data is `2 s sqrt(1 - s^2)` for `s` a singular value of `E_0* F_1` -- the same one-sided sine data Theorems 6.1 and 6.3 use.  The rest of the Section 7 argument (`A + XHX = X(A+H)X`; the `Q_-` blocks of `A + XHX` are the same `Lambda_0, Lambda_1`) never compares dimensions, and `X` is unitary so the pair `(Q_-, Q)` has matching dimensions however `P` and `Q` differ.

WHAT IS STILL MISSING for the theorem, and why it was not attempted here: the estimate produced by that route is `delta N(sin 2Theta) <= 2 N(B)` for the *ambient* `(Q_-, Q)` sine, and turning it into a statement about `sin 2Theta_0` is exactly the `Theta_0`/`Theta` bridge recorded as **sub-problem B above, which is open in the EQUAL-dimension case too**.  So sub-problem C is not independently blocked -- it is downstream of B.  Anyone attacking C should close B first; the geometry it needs is now available.

NO `tan 2theta` ANALOGUE WAS INVENTED, and none should be.  The structural obstruction is documented in the module docstring of `DoubleAngle/Gram.lean`: the `sin 2theta` proof reduces to an ordinary sine theorem for `(Q_-, Q)`, a pair that is automatically equidimensional because `X` is unitary; the `tan 2theta` proof instead imitates the single-angle tangent argument, whose load-bearing identity (7.6) is a 2x2 rotation-block system in matched `C_0, C_1, S_0` blocks of the DIRECT ROTATION `P -> Q`, and with unequal dimensions there is no direct rotation and hence no such system.  The rectangular repair that rescues Theorem 6.3 gives only `C_1*C_1 = 1 - S_0S_0*` -- enough for a `cos theta` denominator, not enough to reproduce the coupled `C_0/C_1` identity that produces the signed `cos 2theta`.  This is an obstruction to the method, not a claim of falsity.

TWO DECOY NAMES, recorded so the next reader is not misled again.  `TauCeti.DavisKahanTheory.sinTwoTheta_perturbation_le_unequalFinrank` (`DavisKahan/FiniteDimensional/DoubleAngle/SinTheta.lean:646`) and `TauCeti.DavisKahanTheory.generalizedSinTwoTheta_unequalFinrank` (`DavisKahan/FiniteDimensional/Generalized.lean:163`) are named for a hypothesis they do not have.  Each is statement-identical to the theorem it delegates to (`sinTwoTheta_perturbation_le` and `sinTwoTheta_residual_le_of_orderedGap` respectively) -- no `finrank` or `Module.rank` hypothesis occurs in either signature.  Neither is coverage for the Section 8 sentence.  Neither is referenced by any Lean source, `comparator/*.json`, or `Challenge/` module, so removing them is safe; recommendation is to delete rather than rename, since a rename would preserve a pure forwarding duplicate.

TRANSCRIPTION DEFECT FOUND 2026-08-08, NOT YET FIXED.  `non-distributable/davis-kahan-1970-modernized-transcription.tex` lines 2330-2343 drop a factor two in the residual step of the Section 7 `sin 2theta` proof.  The displayed inequality at 2331-2339 reads `delta ||[[0, -sin2Theta_0 J_0*],[J_0 sin2Theta_0, 0]]|| <= ||[[0, B*],[B, 0]]||` and the conclusion at 2342 reads `delta ||sin 2Theta_0|| <= ||B|| <= ||R||`.  But the "first inequality" being rewritten is (7.5), `delta ||sin 2Theta|| <= ||H - XHX||`, and `H - XHX = [[0, 2B*],[2B, 0]]`, whose norm is `2 ||[[0,B*],[B,0]]||`.  The right-hand sides should therefore be `2 ||[[0,B*],[B,0]]||` and `delta ||sin 2Theta_0|| <= 2 ||B|| <= 2 ||R||`, which is what the Section 2 statement of the theorem prints (`delta ||sin 2Theta_0|| <= 2 ||R||`, transcription line 758).  Do not propagate the factor-one line.

**SUB-PROBLEM B IS CLOSED AT COMPLEX SCALARS, 2026-08-08 (Claude Opus 5).  STATUS DELIBERATELY UNCHANGED: sub-problem A (real scalars) is what still holds this row at `compiled_specialization`.**

The printed theorem's SECOND conclusion -- `delta ||sin 2Theta|| <= 2||H||`, the ambient `Theta` half, equation (7.5) -- is now proved for every source unitarily invariant norm, on an arbitrary complete complex Hilbert space, with no dimension or compactness hypothesis:

* `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm` and its Ky Fan core `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_all_kyFan` (`DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean`, default build, `[propext, Classical.choice, Quot.sound]`).

The bridge that was missing was NOT a singular-value comparison between the directed and the ambient objects.  It is an *operator identity*: with `J_V` the reflection through `V`,

  `sin 2Theta = |P_{J_V U} - P_U|`,

where `sin 2Theta := cfc (fun t => sin (2t)) (paperAngleOperatorC U V)` is the paper's literal ambient object.  Proved as `TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC_eq_modulus_starProjection_sub` (`DavisKahan/Geometry/Angle/PaperDoubleAngle.lean`).  Only the OPERATOR NORM version of this identification existed before (`subspaceGap_map_reflection_eq_norm_sinTwoAngle`), and an operator-norm identity says nothing about any other unitarily invariant norm -- that is precisely why the row could not be closed by the existing reflection machinery.

WHY IT IS AN IDENTITY AND NOT AN ESTIMATE.  For orthogonal projections `P, Q` and `X = 2Q - 1`, `XPX - P = 2 X (PQ - QP)`, and `X` is a self-adjoint unitary, so `|XPX - P| = 2|[P,Q]|`.  The commutator's Gram operator is computed by a purely algebraic identity in the ring generated by two idempotents, `(QP - PQ)^2 = D^4 - D^2` for `D = P - Q` (`TauCeti.commutator_mul_self_of_isIdempotentElem`, `ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/Reflection.lean`), so `|2[P,Q]|^2 = 4(D^2 - D^4) = 4 sin^2 Theta cos^2 Theta`.  Uniqueness of the positive square root then gives equality with `cfc (sin 2.) Theta`.  Nothing here is finite-dimensional or compact.

THE CONSTANT IS THE PAPER'S 2, NOT 4.  The reflected pair is fed to a NEW sharp symmetric sine estimate, `TauCeti.DavisKahan1970.symmetric_sinTheta_spectrum_all_kyFan`, which couples the two directed cross blocks by Lemma 6.1 and contracts them by Lemma 6.2 -- the argument of Proposition 6.1 -- instead of by the triangle inequality.  The pre-existing `sinTheta_spectrum_gauge_symmetric` uses a triangle inequality and therefore carries a spurious factor 2; composing it with the reflection would have produced 4.  The block-level input Lemma 6.1 needs is exposed as `TauCeti.DavisKahan1970.sinTheta_spectrum_block_gauge`, which is `sinTheta_spectrum_gauge` stopped one step earlier (before the projected perturbation block is contracted to the whole perturbation).

CONVENTION, recorded so the statement is not misread: like the rest of the repository's `sin 2Theta` development, the internal spectral gap is carried by `A` at its reducing subspace `U` and `V` reduces `B`; the printed theorem carries the gap on `A + H` at `QH`.  The two readings exchange the roles of the two operators, under which `||H||` is unchanged.

WHAT REMAINS ON THIS ROW: sub-problem A (real scalars for every UI norm, blocker `real-scalar-infinite-dimensional-scope`) and sub-problem C (the unequal-dimension extension announced at the end of Section 8).  C was recorded as downstream of B; with B closed at complex scalars, C is now unblocked in the equal-scalar case, but it needs its own statement -- the identity above is stated for a pair of subspaces of one space, and the Section 8 sentence is about `dim X(E_0) < dim X(F_0)`.

**A DECOY THAT LOOKS LIKE THIS ROW'S MISSING REAL-SCALAR ENDPOINT IS NOT PROVED -- RECORDED 2026-08-09 (Claude Opus 5) SO NOBODY COUNTS IT.**

`TauCeti.DavisKahanExt.ideal_sinTwoTheta` (`DavisKahan/Experimental/InfiniteDimensional/SinTheta/IdealIntervalExterior.lean:146`) reads exactly like sub-problem A of this row: `{K} [RCLike K]` -- so real AND complex -- arbitrary `SymmetricNormIdeal`, arbitrary complete inner product space, no dimension hypothesis, and the conclusion `d * I.gauge (sinTwoAngleOperator U V) <= 2 * I.gauge (B - A)` with the paper's constant.  It is NOT coverage.  `#print axioms` gives `[propext, sorryAx, Classical.choice, Quot.sound]` -- it is an unfinished proof.  The same is true of its two siblings in that module, `ideal_sinTheta` and `projectionDifference_ideal_intervalExterior`.  The module is outside every default target, so `lake build` never touches it and the axiom audit is the only way to see this.

A second reason it is not the endpoint even if it were finished: it carries `[Algebra R (E ->L[K] E)]`, `[IsScalarTower R K (E ->L[K] E)]` and `[ContinuousFunctionalCalculus R (E ->L[K] E) IsSelfAdjoint]` as HYPOTHESES (twice over -- the binders are duplicated between the section variables and the statement), so instantiating it at real scalars requires supplying a real continuous functional calculus instance rather than finding one.  The complexification route recorded in this row's `next_action` remains the plan.

**THE TWO DECOY `unequalFinrank` NAMES ARE CONFIRMED, BY ELABORATION, 2026-08-09 (Claude Opus 5).**  Both signatures were dumped and compared against the theorems they forward to, and they are character-for-character identical apart from the name: `sinTwoTheta_perturbation_le_unequalFinrank` versus `sinTwoTheta_perturbation_le` (`{K} [RCLike K] {E} ... [FiniteDimensional K E] (N : UnitarilyInvariantSeminorm K E) {A B : E ->l[K] E} ... (b - a) * N.toFun (sinTwoAngleOperator U V) <= 2 * N.toFun (B - A)`), and `generalizedSinTwoTheta_unequalFinrank` versus `sinTwoTheta_residual_le_of_orderedGap`.  Neither contains `finrank` or `Module.rank` anywhere, and both carry `[FiniteDimensional]` on every space.  The recommendation above stands: delete rather than rename, as a separate reviewed change.

**SUB-PROBLEM A IS CLOSED, 2026-08-09 (Claude Opus 5).  BOTH printed conclusions of the Section 2 `sin 2theta` theorem now exist over a REAL Hilbert space, for every source unitarily invariant norm.  STATUS DELIBERATELY UNCHANGED: sub-problem C is what now holds this row at `compiled_specialization`.**

The DIRECTED half `delta ||sin 2Theta_0|| <= 2||R||` (perturbation form) and `delta ||sin 2Theta_0|| <= ||R||` (reflection-residual form) are proved for an UNBOUNDED self-adjoint closed operator on an arbitrary complete REAL Hilbert space and its genuine real spectral subspaces, with no dimension and no compactness hypothesis, and with ideal membership CONCLUDED:

* `TauCeti.DavisKahan1970.sinTwoTheta_addBounded_paperUINorm_real` and `TauCeti.DavisKahan1970.sinTwoTheta_reflectionResidual_paperUINorm_real` -- at `PaperUnitaryInvariantNorm`, the SAME norm class as the real ambient half `sinTwoTheta_wholeSpace_paperUINorm_real`;
* `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real` and `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_real` -- the literal-source forms with the paper's `sin 2Theta_0` REPRESENTATIVE freedom, at `KyFanDominantIdealFamily (R)`, the exact scalar mirror of the two complex literal-source theorems listed above;
* `TauCeti.DavisKahan.Experimental.sinTwoTheta_addBounded_gauge_real` and `TauCeti.DavisKahan.Experimental.sinTwoTheta_reflectionResidual_gauge_real` (`DavisKahan/DoubleAngle/RealUnboundedIdeal.lean`) -- the cores.

All six are in the DEFAULT build (`DavisKahan.All`) and all give exactly `[propext, Classical.choice, Quot.sound]`.

THE ROUTE WAS NOT THE ONE THIS ROW'S `next_action` PRESCRIBED, and the reason is recorded because the prescribed route is genuinely blocked.  `next_action` said: complexify the configuration, instantiate the complex theorem at each finite Ky Fan family, finish with `PaperUnitaryInvariantNorm.mul_gauge_le_of_all_mul_kyFan_le`.  That works for a BOUNDED configuration (it is how `S2-tan-two-theta` closed), but the directed `sin 2theta` endpoints take an UNBOUNDED `DKClosedOperator` and its spectral subspaces, and transporting THOSE needs, on top of the subspace adapter, (i) an identification of `selfAdjointSpectralRestriction (complexify A)` with a unitary conjugate of `complexify (realSelfAdjointSpectralRestriction A)` as CLOSED operators, and (ii) a transport of the spectral-separation hypotheses, which are stated over `TauCeti.LinearPMap.spectrum` and hence exist only over `C`.  Neither is available.

WHAT WAS DONE INSTEAD: the Section 7 argument was run natively over `R`.  Everything it needs is scalar-generic or already real, once three modules are generalised from `C` to `RCLike` (`boundedUnitaryConjugate`, `starProjection_map_unitary`, `reflectionPerturbation` and its two estimates in `SpectralTheory/ReflectionRestriction.lean`; `sinTwoThetaIdealBlock`, the overlap-block ideal lemma and `reflectionPerturbation_mem_and_gauge_le` in `DoubleAngle/UnboundedIdeal.lean`; `addBounded_isSelfAdjoint` and `boundedPerturbationSinThetaData` in `SinTheta/BoundedPerturbation.lean` -- all three generalisations are verbatim, no proof changed).  The real unbounded `sin Theta` theorem `sinTheta_unbounded_real` and the real spectral descent `DavisKahan/SpectralTheory/Real/SpectralRestriction.lean` already existed and supply the analysis.

ONE STEP OF THE COMPLEX PROOF WAS REMOVED RATHER THAN MIRRORED, and this is an improvement worth reusing.  The complex proof conjugates the complementary spectral restriction onto the reflected subspace `J_V(U-perp)` with `unitaryConjugate`, purely so that the block map is a submodule inclusion; that conjugation is what drags in `unitaryConjugate_spectrum_eq` and hence `C`.  It is unnecessary: feed the isometric embedding `J_V . (U-perp).subtypeL` directly.  The ambient-projection step was generalised to accept any isometric `Y` with `Y Y* = P_W` (`projectionProduct_mem_and_gauge_le_isometric`), and `projectionProduct_mem_and_gauge_le_overlap` is now a two-line corollary of it.

HOW THE SEPARATION IS SPELLED, stated plainly because it is NOT a translation of the complex hypotheses.  The real theorems take `FormBoundedSylvesterGap` between the two real spectral restrictions.  That predicate covers the source's interval/exterior configuration (over `realSpectrum`) and both ordered half-line configurations (as operator-form bounds), and `DavisKahan/Sylvester/Gap.lean` records it as the weaker of this tree's two spellings.  The complex statements instead take `SemiboundedBelow`/`SemiboundedAbove` on the exact block together with resolvent-set avoidance for the complementary block, and that pair simply cannot be written over `R`.

THE ONE REAL-SCALAR SPELLING STILL ABSENT, recorded so it is not counted as present: there is no real unbounded OPERATOR-NORM directed statement in the shape of `sinTwoTheta_addBounded_of_spectrum_gap`, i.e. one whose conclusion names a real `sin 2Theta` angle operator rather than the block `sinTwoThetaIdealBlock`.  The estimate itself is available -- read `sinTwoTheta_addBounded_gauge_real` at `KyFanDominantIdealFamily.kyFan 1` -- but converting the block to an angle operator needs the real counterpart of `norm_sinTwoThetaIdealBlock`, which rests on `sinTwoAngleOperatorC`.  This is a naming/geometry step, not analysis.

**THE SCALAR AXIS IS NOW CLOSED WITHOUT RESIDUAL, 2026-08-09 (Claude Opus 5, M34); `real-scalar-infinite-dimensional-scope` REMOVED from this row.**  The single item for which the blocker reference was deliberately retained above -- "no real unbounded OPERATOR-NORM statement whose conclusion names a real `sin 2Theta` angle operator exists, because the block-to-angle identification `norm_sinTwoThetaIdealBlock` is stated over `sinTwoAngleOperatorC`" -- is discharged.  The missing geometric renaming is `norm_sinTwoThetaIdealBlock_real` (`DavisKahan/DoubleAngle/RealAngleIdentification.lean`): `||sinTwoThetaIdealBlock U V|| = ||paperSinTwoAngleOperatorR U V||` for a pair of closed subspaces of an arbitrary real Hilbert space.

HOW IT DESCENDS, and why no `Submodule.map` complexification was needed.  `sinTwoThetaIdealBlock_eq_comp` rewrites the canonical block `P_U . P_{J_V U^perp}` as the map-free composition `P_U . J_V . P_{U^perp} . J_V`, SCALAR-GENERICALLY over `RCLike`, using `starProjection_map_unitary` (already generic) and `Submodule.reflection_symm`.  Every factor of that composition already had a complexification identity -- `starProjection_complexifySubmodule`, `starProjection_complexifySubmodule_orthogonal`, and the pre-existing `complexify_reflectionOperator` of `DavisKahan/Geometry/Polar/DirectRotationReal.lean`, which was found only after a duplicate of it collided in `DavisKahan.All` -- so `complexify_sinTwoThetaIdealBlock` is immediate.  The remaining step is purely complex: `norm_paperSinTwoAngleOperatorC_eq_norm_sinTwoAngleOperatorC` shows that the two complex spellings of `sin 2Theta` (the product form `2 sinTheta cosTheta` behind `sinTwoAngleOperatorC`, and the functional calculus `sin(2 .)` of the operator angle behind `paperSinTwoAngleOperatorC`) have the same NORM, because each equals the projection gap between `U` and its reflection through `V`: the second by `paperSinTwoAngleOperatorC_eq_modulus_starProjection_sub` with `ContinuousLinearMap.norm_modulus`, the first by `subspaceGap_map_reflection_eq_norm_sinTwoAngle`.

The two printed operator-norm conclusions over a real Hilbert space follow by reading the real Ky-Fan-dominant theorems at the first Ky Fan family (`KyFanDominantIdealFamily.kyFan 1`, whose gauge is `kyFanApproximationGauge 1 = ||.||`) and renaming the block.  `unbounded_sinTwoTheta_opNorm_real` is `delta ||sin 2Theta|| <= 2||E||` and `unbounded_sinTwoTheta_reflectionResidual_opNorm_real` is `delta ||sin 2Theta|| <= ||R||`, both for an unbounded self-adjoint closed operator on a real Hilbert space of arbitrary dimension with genuine real spectral subspaces and the scalar-generic `FormBoundedSylvesterGap` separation.  All seven new declarations are axiom-clean `[propext, Classical.choice, Quot.sound]` and reached from `DavisKahan.All`.

WHAT KEEPS THIS ROW AT `compiled_specialization` IS NOW SUB-PROBLEM C ALONE (with sub-problem B upstream of it).  That is a scope axis, not a scalar axis, and it is unaffected by this session.

**ASSESSMENT OF THE `_unequalDimension` DECLARATIONS THAT ARRIVED IN COMMIT d0cac626 (2026-08-11, Claude Opus 5, coordinator-measured).  THEY DO NOT CLOSE SUB-PROBLEM C, AND THE ROW SHOULD NOT BE READ AS IF THEY DO.**

MEASURED: `unbounded_sinTwoTheta_residual_uiNorm_representative_unequalDimension` is the SAME STATEMENT as `unbounded_sinTwoTheta_residual_uiNorm_representative` plus ONE EXTRA HYPOTHESIS, and its entire proof is `exact` applied to that sibling.  The extra hypothesis is bound as `_hStrictDimension` -- AN UNDERSCORE BINDER, hence UNUSED.  So the wrapper is strictly WEAKER than its base (more hypotheses, identical conclusion).

WHAT IT ACTUALLY ESTABLISHES, and this IS worth recording: the base theorem carries NO dimension hypothesis of any kind -- coordinator-verified, zero occurrences of `rank`, `finrank` or `Dimension` in its binders.  It was therefore ALREADY valid at unequal dimensions, and the wrapper documents that fact for a reader rather than extending anything.  That is a legitimate documentation contribution and a misleading name: this is now the THIRD decoy on this axis, after the two `unequalFinrank` names the 2026-08-09 audit found carrying equal-dimensional signatures.

**WHY THE ROW DOES NOT MOVE.**  This row's own notes already record the answer: the directed estimate is not the obstruction.  Sub-problem C is DOWNSTREAM OF SUB-PROBLEM B -- the `Theta_0`-to-`Theta` bridge -- which is OPEN IN THE EQUAL-DIMENSION CASE TOO.  A dimension-free DIRECTED theorem does not yield the AMBIENT statement the source sentence is about.  Anyone attacking C must close B first.

The three `_unequalDimension` declarations are listed above so the row names what exists; all three are axiom-clean and in the default build (coordinator-probed).
- **Next action:** STALE TEXT CORRECTED 2026-08-10.  This field said `REAL SCALARS ... FOR THE DIRECTED HALF ONLY`, contradicting this row's own `scope_gap` and the tail of its `notes`, both of which record that THE SCALAR AXIS WAS CLOSED 2026-08-09 (M34) and that `real-scalar-infinite-dimensional-scope` no longer appears in `blocked_by` -- which it does not.  WHAT ACTUALLY KEEPS THIS ROW AT `compiled_specialization` IS SUB-PROBLEM C ALONE: the unequal-dimension extension of the last sentence of Section 8, `dim X(E_0) < dim X(F_0)`, with sub-problem B (the `Theta_0`-to-`Theta` bridge) upstream of it.  That is a SCOPE axis, not a scalar axis.

ROUTE, from the handoff and this row's notes: prefer the actual rectangular crossed block and Gram identities -- the Section 7 block algebra is already dimension-blind -- over padding dimensions to reuse an equal-rank theorem.  TRAPS: (i) the old `duplicated ambient multiplicity` counterexample was WRONG; `sinTwoAngleOperatorC` is built from the directed sine geometry and its range lies in the relevant source subspace.  (ii) A proposed bridge `SameApproximationSingularSequence (sinTwoThetaIdealBlock U V) (sinTwoAngleOperatorC U V)` appears to be FALSE as posed (measured 2026-08-07 by a weakest-instance check in C^2); do not spend time on it before re-checking.  (iii) Inspect any theorem whose name contains `unequalFinrank`: two such were decoys with equal-dimensional signatures.

#### Section 2, tan 2 theta theorem: Double-angle tangent theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Fully off-diagonal perturbations across an ordered gap give residual and perturbation tan(2 Theta) bounds with factor two.
- **Current Lean references:** `TauCeti.DavisKahanTheory.partIII_tanTwoTheta_opNorm`, `TauCeti.DavisKahanExt.tanTwoTheta_offDiagonalC_of_weighted_sine`, `TauCeti.DavisKahan.sharp_paperUnitaryInvariantNorm`, `TauCeti.DavisKahan.sharp_paperUnitaryInvariantNorm_selectedBranch`, `TauCeti.DavisKahan.paperFaithful_tanTwoTheta_uiNorm_real`, `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm`, `TauCeti.DavisKahanTheory.paired_singularVector_gap_inequality`, `TauCeti.DavisKahanTheory.singularValue_ne_one`, `TauCeti.DavisKahanTheory.absDoubleAngleTangent_scalar`, `TauCeti.DavisKahanTheory.sum_absDoubleAngleTangent_le`, `TauCeti.DavisKahanTheory.absTanTwoTheta0_offDiagonal_le`, `TauCeti.DavisKahanTheory.sum_absDoubleAngleTangent_le_of_finiteDimensional_invariantSubspace`, `TauCeti.DavisKahanTheory.kyFan_absTanTwoTheta_le_of_finiteDimensional_invariantSubspace`, `TauCeti.DavisKahanTheory.absTanTwoTheta_offDiagonal_mem_and_gauge_le_of_finiteDimensional_invariantSubspace`, `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm_arbitrarySubspace`, `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm_real`, `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_kyFan_arbitrarySubspace`, `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_prefix_arbitrarySubspace`, `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_uiIdeal_arbitrarySubspace`, `TauCeti.DavisKahan1970.tanTwoTheta_equation_7_6_approximate`, `TauCeti.DavisKahan1970.tanTwoTheta_cos_ne_zero_approximate`, `TauCeti.DavisKahan1970.tanTwoTheta_pole_separation`, `TauCeti.DavisKahanExt.paperTanTwoAngleOperatorC`, `TauCeti.DavisKahanExt.spectrum_paperAngleOperatorC_lt_pi_div_four`, `TauCeti.DavisKahanExt.paperTanTwoAngleOperatorC_nonneg`, `TauCeti.DavisKahan1970.paperDoubleSecant`, `TauCeti.DavisKahan1970.paperTanTwoBlockRepresentative`, `TauCeti.DavisKahan1970.paperTanTwoAngleOperatorC_eq_modulus_blockRepresentative`, `TauCeti.DavisKahan1970.paperTanTwoBlockRepresentative_lowerBlock`, `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_all_kyFan`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_all_kyFan`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm`, `TauCeti.DavisKahanExt.paperTanTwoAngleOperatorR`, `TauCeti.DavisKahanExt.complexify_paperTanTwoAngleOperatorR`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real`, `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC`, `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC_nonneg`, `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC_eq_paperTanTwoAngleOperatorC`, `TauCeti.DavisKahan1970.isUnit_one_sub_two_mul_paperProjectorDifference_sq_of_cos_two_ne_zero`, `TauCeti.DavisKahan1970.paperAbsTanTwo_sq_mul_cos_two_sq`, `TauCeti.DavisKahan1970.paperAbsTanTwoAngleOperatorC_eq_modulus_blockRepresentative`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_all_kyFan_of_corner`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_of_corner`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_all_kyFan_branchFree`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_branchFree`
- **Assessment:** The finite operator-norm theorem is compiled. The source arbitrary-UI-norm Hilbert-space endpoint and branch selection are not yet certified.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_specialization`. The operator-norm double-angle tangent theorem is compiled and axiom-clean; the paper's general UI-norm scope and the selected acute branch are not.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**BOTH RECORDED GAPS CLOSED 2026-08-05, and one of them was already closed before I got there.**

(a) THE ARBITRARY-UI-NORM HILBERT ENDPOINT WAS ALREADY IN THE BUILD.  `sharp_paperUnitaryInvariantNorm` (`Sources/DavisKahan1970/SharpIdeal.lean`) gives `d * N(tan 2Theta) <= 2 * N(B01)` for an arbitrary `PaperUnitaryInvariantNorm` -- a normalised zero-padded symmetric gauge family, i.e. the paper's notion of unitarily invariant norm -- over arbitrary complete complex Hilbert spaces `E0`, `E1`.  Default build, axiom-clean.  The note claiming it was uncertified was stale; the operator-norm remark described a *different*, finite-dimensional theorem.

(b) BRANCH SELECTION IS NOW COMPOSED IN.  What was genuinely true is that the endpoint took the contractive Riccati solution `X` as data, while Davis and Kahan's Section 8 *selects* it.  The selection also already existed in the default build (`canonicalContractiveRiccatiSolution`, with an existence-and-uniqueness theorem), so the two compose.  `sharp_paperUnitaryInvariantNorm_selectedBranch` is the composite: spectral separation (`spectrum A0 subset [left,0]`, `spectrum A1 subset [d,inf)`) plus smallness (`2 * norm B01 < d`) yields a contractive Riccati solution -- unique among contractive solutions -- and the arbitrary-UI-norm `tan 2Theta` bound for it, with **no branch supplied by the caller**.  Default build, axiom-clean.

The form bounds the endpoint runs on are read off from the spectral containments by `SpectralOrder.Complex.re_inner_le_of_spectrum_subset_Iic` and `le_re_inner_of_spectrum_subset_Ici`; the interval/exterior shape the Riccati selection wants is the same data reassociated.  No new mathematics was needed -- the two halves had never been put next to each other.

**BLOCKER CLEARED 2026-08-06.**  This row carried `exact-source-wrappers`, but its own `next_action` records that nothing remains for the bounded arbitrary-UI-norm theorem with selected branch -- that is `sharp_paperUnitaryInvariantNorm_selectedBranch` -- and that the residue is tracked on S2-unbounded-scope and on the Section 8 rows.  Both are now discharged: S2-unbounded-scope is `compiled_exact` / `proved_in_build` with no blockers, and DK-8.1-thm and DK-8.2-thm are guarded by `lake build`.  So the wrapper blocker on this row pointed at work that has since been done elsewhere, and is removed.

**REAL SCALAR SCOPE CLOSED 2026-08-07 (Claude Opus 5).**  `paperFaithful_tanTwoTheta_uiNorm_real` is the tan 2Theta theorem over a REAL Hilbert space of arbitrary dimension, for every source unitarily-invariant norm, with the sharp constant `b - a`.  Elaborated: `[InnerProductSpace ℝ E] [CompleteSpace E]`, operators `E →L[ℝ] E`, subspaces `Submodule ℝ E`, no `[FiniteDimensional]`.  Quarter-acuteness is CONCLUDED (`∃ hquarter : IsQuarterAcute U V`), not assumed.  Axiom-clean: [propext, Classical.choice, Quot.sound].

No perturbation theory was repeated.  The proof complexifies the configuration, applies `paperFaithful_tanTwoTheta_uiNorm` verbatim, and transports back.  Two new reusable layers make that mechanical and are the reason the other real lifts should now be cheap:
* `DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/ComplexificationGauge.lean` -- `PaperUnitaryInvariantNorm.{approximationPrefix,prefixGauge,extendedGauge}_complexify`, `mem_complexify_iff` and `gauge_complexify`.  `N.gauge (complexify T) = N.gauge T` for EVERY source UI norm at once, because an operator only enters a `PaperUnitaryInvariantNorm` through its approximation singular values and `approximationSingularValue_complexify` preserves those exactly.
* `DavisKahan/SpectralTheory/Complexification/FormTransport.lean` -- `re_inner_complexify` (which is `rfl`), `re_inner_le_of_mem_complexifySubmodule`, `le_re_inner_of_mem_complexifySubmodule`, `mapsTo_complexifySubmodule`, `mapsTo_orthogonal_complexifySubmodule`, `mapsTo_of_mem_orthogonal_complexifySubmodule`.  Form constants are preserved EXACTLY, which matters because these feed ordered-gap hypotheses where a lossy transport would not close the gap.

The conclusion names `tanTwoAngleOperatorRC U V`, which is by definition `tanTwoAngleOperatorC` of the two complexified subspaces.  That is faithful rather than a workaround: the source bounds a unitarily-invariant norm, such a norm sees only approximation singular values, and those are preserved.  A literally `E →L[ℝ] E`-typed angle operator is extractable via `complexify_realPartOperator` and would have the same singular values, hence the same value under every `N`.

**OVER-CLAIM CORRECTED 2026-08-07 (Claude Opus 5).**  Earlier the same day I upgraded this row to `compiled_exact` on the strength of `paperFaithful_tanTwoTheta_uiNorm_real`.  That was wrong, and the row is restored to `compiled_specialization`.  The real lift is genuine and is retained -- it closes the SCALAR axis -- but it inherits the branch restriction of its complex donor `paperFaithful_tanTwoTheta_uiNorm`, so closing the scalar axis did not close the row.

The paper is explicit that the restriction is a real difference, at the head of Section 8: "The double-angle conclusions also allow angles close to pi/2. ... The explanation is that the double-angle theorems imposed no special choice of the reducing subspace QH of A+H."  `Theta < pi/4` is Theorem 8.1's conclusion, earned from the extra hypothesis that `P` and `Q` are the spectral projectors of `A` and `A + H` for the same interval.  A CLEAN census must not be read as evidence that branch-free tan 2Theta is done.

WHERE THE BRANCH-FREE THEOREM STANDS: `DavisKahan/DoubleAngle/TanTwoThetaKyFan.lean` is close to the printed Section 7 argument, but its graph-coordinate theorem assumes `hT1 : T.singularValues 0 < 1`, i.e. the strict quarter-acute branch, which the printed theorem does not.  The printed proof instead chooses a sign according to `cos 2 theta_j` and derives `2 Re(y_j* B x_j) >= delta * |tan 2 theta_j|`, so the branch-free statement needs an `|tan 2Theta|` representation.  Follow printed equation (7.6); do NOT try to infer the unrestricted theorem from the quarter-acute Riccati API, and do not route it through Theorem 8.1, which selects one particular `Q`.

`paperFaithful_tanTwoTheta_uiNorm_real` and its complex donor are now documented as selected-branch in their module docstrings and in `Sources/DavisKahan1970/TanTwoTheta.lean`, whose 'Audited source scope' section had itself asserted that the source conclusion includes `Theta < pi/4`.  It does not.

**THE BRANCH-FREE THEOREM IS PROVED 2026-08-07 (Claude Opus 5), at every source unitarily invariant norm, for real and complex scalars, on an arbitrary Hilbert space with a finite-dimensional trial subspace.**  The row stays `compiled_specialization`, and the reason is now a DIFFERENT and much smaller one: only `[FiniteDimensional 𝕜 U]` remains.  The branch axis, which was the conceptual gap, is closed.

The endpoint is `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm` (`DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean`): `N.Mem H -> N.Mem (tan 2Theta) /\ (b - a) * N.gauge (tan 2Theta) <= 2 * N.gauge H` for an arbitrary `PaperUnitaryInvariantNorm`, `[RCLike k]`, `[CompleteSpace E]`, no `[FiniteDimensional k E]`.  Axiom-clean: [propext, Classical.choice, Quot.sound].  Checked at the elaborator, not by grep.

WHAT IS ABSENT FROM ITS HYPOTHESES, and this is the point: no `T.singularValues 0 < 1`, no `IsQuarterAcute`, no `hVhigh`/`hVperpLow` spectral placement on the blocks of `A + H`.  The perturbed subspace is an arbitrary invariant graph over `U` and may make angles arbitrarily close to `pi/2`.  The conclusion does not assert `Theta < pi/4`.  Contrast `paperFaithful_tanTwoTheta_uiNorm`, which assumes the four ordered form bounds -- two of them on `A + H` -- and concludes `IsQuarterAcute`: that is the Theorem 8.1 configuration.

HOW THE BRANCH WAS REMOVED, following printed equation (7.6) rather than the Riccati API:

1. `paired_singularVector_gap_inequality` is (7.6) in CLEARED form, `(b - a) t_j <= (1 - t_j^2) Re<v_j, H u_j>`.  Multiplied through by `1 - tan^2 theta_j` instead of divided by it, it needs no hypothesis on which side of the quarter turn the angle lies.  The old `doubleAngleTangent_scalar` is now derived from it, so the selected branch is visibly the LAST step of that proof and nothing earlier.

2. `singularValue_ne_one` is the paper's `cos 2 theta_j != 0`: `t_j = 1` makes (7.6) read `b - a <= 0`, contradicting the gap.  So no principal angle is exactly `pi/4` even though no branch was chosen.

3. The sign choice.  Dividing by `|1 - t_j^2|` and using `(1 - t_j^2) c <= |1 - t_j^2| |c|` gives `(b - a) |tan 2 theta_j| <= 2 |Re<v_j, H u_j>|` with `absDoubleAngleTangent t = 2t/|1 - t^2|`.  The Ky Fan passage then needs the MAGNITUDE form of the variational bound, `TauCeti.RectangularUnitarilyInvariantSeminorm.sum_abs_le_rectangularKyFanSum_of_orthonormal` (new, ForTauCeti), which rephases each left singular vector by the sign of `cos 2 theta_j`.  That rephasing IS the paper's "choose the sign according to `cos 2 theta_j`".

WHY THE CONCLUSION IS UP TO A REARRANGEMENT, and why that is not a weakening.  `t -> 2t/|1 - t^2|` increases on `[0,1)` and decreases on `(1,inf)`, so along the antitone graph-coordinate singular values the branch-free tangents are NOT antitone, while approximation numbers always are.  The Ky Fan root is therefore proved for an ARBITRARY finite index set (`sum_absDoubleAngleTangent_le`), which is strictly stronger than a prefix statement, and the representative hypothesis is `approximationSingularValue (pi n) tanTwoTheta = absDoubleAngleTangent (approximationSingularValue n T)` for a rearrangement `pi : N =~ N`.  A unitarily invariant norm sees only the multiset of singular values; this is the paper's own `tan 2Theta_0` representative freedom.

REAL SCALARS CAME FREE.  The whole chain is `[RCLike k]`-generic, so unlike `paperFaithful_tanTwoTheta_uiNorm_real` no complexification transport was needed at this scope.

ONE COMPRESSION, NOT TWO.  `kyFan_doubleAngleTangent_offDiagonal_le_of_finiteDimensional_invariantSubspace` is now DERIVED from the branch-free carrier theorem (`absDoubleAngleTangent = doubleAngleTangent` on the acute quarter, plus a trivial no-gap case), so the finite-carrier compression proof exists once.

**THE FINITE-DIMENSIONAL TRIAL SUBSPACE IS REMOVED 2026-08-08 (Claude Opus 5).  `compiled_specialization` -> `compiled_exact`.**  The one recorded axis is closed, for real and complex scalars alike:

* `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm_arbitrarySubspace` -- ℂ;
* `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm_real` -- ℝ.

Both elaborate with `[U.HasOrthogonalProjection]` (the formal encoding of the paper's *closed* subspace) and NO `[FiniteDimensional]` on `U` or on `E`.  Checked at the elaborator, not by grep.  Axiom-clean throughout: [propext, Classical.choice, Quot.sound].

**WHERE THE FINITE DIMENSION ACTUALLY WAS.**  Not in the carrier compression.  Tracing back from the capstone, the restriction entered exactly once, at `sum_absDoubleAngleTangent_le` (DoubleAngle/TanTwoThetaBranchFree.lean), which diagonalizes the graph coordinate and consumes `T.singularValues` / `leftSingularVector` / `rightSingularBasis`.  The carrier `M := U ⊔ T''U` inherited the restriction only because it had to land there.  Shrinking `U` cannot rescue the compression: for any split `M = M0 ⊕ M1` with `M0 ≤ U` and `M1 ≤ Uᗮ`, all three off-diagonality conditions and both form bounds compress automatically, but `hinv` breaks, because it needs `M0` to be `(A+H)`-graph-invariant.  So the singular-basis argument is what had to go.

**WHAT REPLACED IT.**  Approximate singular pairs, not finite carriers.  The input is a unit `u ∈ U`, a unit `v ∈ Uᗮ` and `t ≥ 0` with `‖T u - t v‖ ≤ ε` and `‖T* v - t u‖ ≤ ε` -- the per-index content of `ApproximateLeadingSingularFamily`, which exists for EVERY bounded operator with no compactness assumption.  The family is taken for the graph coordinate read BETWEEN THE BLOCKS, `blockGraphCoordinate T U : U →L Uᗮ`, so the right vectors lie in `U` and the left vectors in `Uᗮ` by typing rather than approximately; its approximation numbers are the ambient ones by the existing `sameApproximationSingularValues_ambientSubspaceBlock`.  New layers:
* `DavisKahan/DoubleAngle/TanTwoThetaApproximatePair.lean` -- `RCLike`-generic, dimension-free: `paired_approximate_gap_inequality` (equation (7.6) cleared, with explicit error `(‖A‖+‖H‖)(2+‖T‖+t)ε`), `absDoubleAngleTangent_approximate_scalar`, `sum_absDoubleAngleTangent_le_of_approximatePairs`;
* `DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFreeInfinite.lean` -- the family, the split at its cutoff, and the `ε → 0` passage;
* `DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFreeInfiniteReal.lean` -- the real case by complexification.

This is the LIMITING ARCHITECTURE of `sharp_transformed_prefix`, reused; only the per-pair estimate differs.  Nothing divides by `I - X*X`, asks for a contraction, or routes through Theorem 8.1, so the branch-free meaning is preserved: there is still no `approximationSingularValue 0 T < 1`, no `IsQuarterAcute`, and no spectral placement on the blocks of `A + H`.

**THE pi/4 POLE, WITHOUT ASSUMING UNIFORM SEPARATION.**  This was the real mathematical risk and it is handled, not sidestepped.  Pointwise `cos 2θⱼ ≠ 0` does NOT give a uniform bound in infinite dimension.  What does is equation (7.6) itself: it forces `d t - err ≤ |1 - t²| |Re⟪v, H u⟫| ≤ |1 - t²| ‖H‖`, so for `t > 1/2` and `err ≤ d/4` the left side is at least `d/4 > 0`, which forces `‖H‖ > 0` and `|1 - t²| ≥ d/(4‖H‖)`; for `t ≤ 1/2` the pole is simply far away.  See `penalty_le_of_paired_approximate` (quantitative, `O(ε)` penalty) and `abs_one_sub_sq_pos_of_paired_approximate` (the qualitative `cos 2θ ≠ 0`, proved division-free so it holds even when `H = 0`).  The tail indices of the family, where the approximation number is at most `ε`, are far from the pole for trivial reasons.  Both contributions are `O(ε)` and both vanish in the limit.

**ARBITRARY INDEX SET, NOT A PREFIX.**  `t ↦ 2t/|1 - t²|` is not monotone across the quarter turn, so a `tan 2Θ` representative carries the branch-free tangents as a multiset.  The core theorem therefore quantifies over an arbitrary `S : Finset ℕ`, with the family taken at `k = S.sup id + 1`.  The representative hypothesis is unchanged from the finite-dimensional row: `approximationSingularValue (π n) tanTwoTheta = absDoubleAngleTangent (approximationSingularValue n T)` for a rearrangement `π`.

**REUSABLE API ADDED** (roadmap owner `OperatorTheory.Majorization`): `sum_abs_le_kyFanApproximationGauge_of_orthonormal` and `orthonormal_signFlip` in DoubleAngle/KyFanOrthonormal.lean -- the approximation-number counterpart of the finite `sum_abs_le_rectangularKyFanSum_of_orthonormal`.  The rephasing it performs IS the paper's "choose the sign according to `cos 2θⱼ`".  Stated generically, no paper-facing names.

**ONE THING A LATER AUDITOR SHOULD KNOW, NOT A NEW GAP.**  Like every declaration already on this row, the new endpoints are the PERTURBATION form `2 · N(H)`, not the residual form `2 · N(R)` of the printed (DK-tan2).  That was already true of `tanTwoTheta_branchFree_paperUINorm`, and the 2026-08-07 audit recorded the finite-dimensional trial subspace as the row's ONLY remaining axis, so closing it closes the row on the recorded evidence.  If a future audit wants the residual form as a separate axis, it should be opened as its own scope note rather than folded in here.

Validation: full `lake build` green (9490 jobs); `lake build FinishTanTwoTheta Challenge` green (9038 jobs); census checker, `probe_census_declarations.py --verify`, `check_declaration_name_drift.py` and `export_for_tauceti.py --check` all clean.

**STATUS CORRECTED 2026-08-09 (Claude Opus 5), FROM `compiled_exact`.  THE ROW WAS OVER-CLAIMED: THE PRINTED THEOREM HAS TWO CONCLUSIONS AND THE AMBIENT ONE IS ABSENT ENTIRELY.**

The printed tan 2theta theorem (transcription L765-773) asserts BOTH

    delta ||tan 2Theta_0|| <= 2||R||        (directed, residual)
    delta ||tan 2Theta||   <= 2||H||        (ambient)

Verified by elaboration, not by grep.  `tanTwoTheta_uiNorm` concludes
`(b - a) * N tanTwoTheta0 <= 2 * N H` under `[FiniteDimensional k E]`, and
`tanTwoTheta_uiIdeal_infinite` concludes the same gauge inequality under
`[FiniteDimensional k U]`.  Both bound the DIRECTED `tan 2Theta_0` by `2||H||`,
which is weaker than the printed directed conclusion (`2||R||`, and
`||R|| = ||B|| <= ||H||`) and is not the ambient conclusion at all.

THERE IS NO AMBIENT `tan 2Theta` OBJECT IN THE REPOSITORY.  Searched: no
`paperTanTwoAngle*`, no `cfc (tan . 2*)` on the whole-space angle operator.
`tanTwoAngleOperatorC` is built on `sinTwoAngleOperatorC := 2 . (|P_Vperp P_U| . |P_V P_U|)`,
whose range lies in `U`, so it is a directed object by construction.  The ambient
object carries each `tan 2theta_k` twice, so it is not a relabelling of the
directed one.

The previous `next_action` -- "No mathematical gap and no recorded scope gap.
The branch axis and the finite-dimensional trial-subspace axis are both closed"
-- was wrong on all three counts: there is a mathematical gap (the ambient half),
there is a scope gap (both endpoints still require finite-dimensionality), and
the printed residual half exists only in selected-branch form.

THIS IS THE THIRD OCCURRENCE OF THE SAME FAILURE MODE in this campaign.  The
Section 2 `sin 2theta` and `tan theta` theorems each assert two conclusions, and
each row read as complete while only the directed half existed; both were closed
during this campaign (`sinTwoTheta_wholeSpace_paperUINorm` 2026-08-08,
`tanTheta_wholeSpace_paperUINorm` 2026-08-09).  When a census row covers a
theorem with more than one printed conclusion, check EACH conclusion separately
before recording any status.

**THE AMBIENT HALF IS PROVED 2026-08-09 (Claude Opus 5), in the quarter-acute
branch.  `partial_or_wrapper_missing` -> `compiled_specialization`.**

New module `DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean`; the
ambient object itself is added to `DavisKahan/Geometry/Angle/PaperTanAngle.lean`.
Every new declaration is axiom-clean -- [propext, Classical.choice, Quot.sound] --
checked at the elaborator, not by grep.

THE OBJECT.  `TauCeti.DavisKahanExt.paperTanTwoAngleOperatorC U V :=
cfc (fun t => Real.tan (2 * t)) (paperAngleOperatorC U V)`: the literal ambient
`tan 2Theta`, which carries every principal angle TWICE.  It did not exist
before, exactly as the 2026-08-09 correction above recorded.

THE REPRESENTATIVE.  `paperTanTwoBlockRepresentative U V :=
paperDiagonalPair Uperp U (2 * (D * (1 - 2 D^2)^{-1}))` with `D = P_V - P_U`, and
`paperTanTwoAngleOperatorC_eq_modulus_blockRepresentative` proves
`tan 2Theta = |Xi|` as an OPERATOR identity -- not equality of norms, not
equality of singular-value lists -- so the substitution is legitimate inside
every unitarily invariant norm.  Inputs: the two-projection identity
`((1-p)Dp + pD(1-p))^2 = D^2 - D^4` (reused verbatim from `TanThetaWholeSpace.lean`)
and the scalar identity `tan(2 arcsin s)^2 (1 - 2 s^2)^2 = 4 s^2 (1 - s^2)`.  The
direct-rotation polar factor `J_0` and the complementary angle `Theta_1` never
appear, as in the two sibling whole-space modules.

ENDPOINTS.
* `tanTwoTheta_wholeSpace_all_kyFan`:
  `(b - a) * kyFan_k (paperTanTwoAngleOperatorC U V) <= 2 * kyFan_k H`, every `k`.
* `tanTwoTheta_wholeSpace_paperUINorm`:
  `N.Mem H -> N.Mem (tan 2Theta) /\ (b - a) * N.gauge (tan 2Theta) <= 2 * N.gauge H`
  for every `PaperUnitaryInvariantNorm`.  Boundedness of `tan 2Theta` is
  CONCLUDED, not hypothesised -- the theorem is what forces it.

SCOPE.  Arbitrary complete COMPLEX Hilbert space, `[U.HasOrthogonalProjection]`,
NO `[FiniteDimensional]` on `E` or on `U`, no compactness.  `IsQuarterAcute U V`
is CONCLUDED from the paper's four ordered form bounds via
`isQuarterAcute_of_paper_form_gap_infinite`, not assumed.  Real scalars are not
covered on the ambient half; the complexification transport used for
`paperFaithful_tanTwoTheta_uiNorm_real` should apply unchanged but was not run.

**THE PRINTED RESIDUAL FORM OF THE DIRECTED HALF IS PROVED TOO, AND THE AMBIENT
HALF REQUIRES IT.  THIS CORRECTS THE 2026-08-08 NOTE ABOVE.**

`tanTwoTheta_directedCorner_residual_all_kyFan`:
`(b - a) * kyFan_k (lower corner of Xi) <= 2 * kyFan_k (P_U H P_Uperp)` -- the
printed `2||R||`, not `2||H||`.

The 2026-08-08 note said the residual form, if wanted, "should be opened as its
own scope note rather than folded in here", i.e. treated as an axis independent
of the ambient half.  That is wrong, and it is worth stating why.  `H` is fully
off-diagonal, so its singular values are those of `R` taken twice and
`kyFan_{2m}(H) = 2 kyFan_m(R)`; the factor two is attained.  Lemma 6.1 turns
corner estimates into the ambient estimate, so a corner estimate against
`2 kyFan(H)` yields the ambient bound only with the constant `4`.  The printed
ambient constant `2` therefore FORCES the residual form of the directed half.

It is obtained without new perturbation theory: `sharp_doubleAngleTangentOperator_kyFan`
already has `B01` (the residual) on its right-hand side, and the new operator
identity `paperTanTwoBlockRepresentative_lowerBlock` says the lower corner of the
ambient representative IS the ambient graph tangent `2 Y (1 - Y*Y)^{-1}`, hence
has the approximation numbers of the rectangular coordinate tangent
`2 X (1 - X*X)^{-1}`.  The graph geometry is a ring computation off the
normal-equation projection formula `Q = (p + Y)(1 + Y*Y)^{-1}(p + Y*)`:
`(1-p) Q p = Y (1 + Y*Y)^{-1} p` and `D^2 p = (1 - (1 + Y*Y)^{-1}) p`, whence
`(1 - 2 D^2)^{-1} p = (1 + Y*Y)(1 - Y*Y)^{-1} p` and the two resolvents cancel.
`ambient_doubleAngleTangent_eq_extendCoordinate` in
`InfiniteDimensional/TanTwoTheta/CanonicalTangentBridge.lean` was made public for
this (it was `private`); nothing else in that file changed.

**WHAT REMAINS -- THE BRANCH-FREE AMBIENT HALF -- AND WHY IT IS NOT A ROUTINE
LIFT.**  The branch-free directed endpoints already on this row do NOT compose
into an ambient statement, and the obstruction is specific enough to record so
that it is not retried.

Those endpoints are stated for an arbitrary operator whose approximation numbers
are a REARRANGEMENT of `absDoubleAngleTangent (approximationSingularValue n T)`.
The honest corner of the ambient representative has Gram operator
`psi(G) = 4 G (1 - G)^{-2}` with `G = X*X`, and `psi` is NOT monotone across
`G = 1`.  In infinite dimension the required multiset relation then fails:
let `G` be positive with an isolated eigenvalue `1 + eta` of multiplicity one and
essential spectrum `{100}`.  Approximation numbers see only the essential norm,
so `a_n(G) = 100` for EVERY `n` and every `absDoubleAngleTangent (sqrt (a_n G))`
is about `0.2`, while `a_0 (psi G) = psi (1 + eta)` is arbitrarily large.  No
bijection of `N` can match those multisets.  The pointwise equation (7.6) still
controls each angle, so the theorem is not false -- what fails is the TRANSFER
through the approximation numbers of `X`.  A branch-free ambient proof therefore
needs per-approximate-pair estimates for the corner itself.

Validation: full `lake build` green by exit code, 9553 jobs.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 1 of that audit says this
row reads `compiled_exact` with "No mathematical gap and no recorded scope gap", and that the
printed ambient conclusion `delta ||tan 2Theta|| <= 2||H||` is absent from the repository in any
form.  BOTH HALVES OF THAT ARE NOW STALE, and the audit says so itself: it was measured at
`10bafe30`.  The over-claim was corrected at `763fb842` (status -> `compiled_specialization`) and
the ambient object and its estimate landed at `fae110c7`
(`paperTanTwoAngleOperatorC`, `tanTwoTheta_wholeSpace_all_kyFan`,
`tanTwoTheta_wholeSpace_paperUINorm`), with the real form at `b967c62f`.  Re-verified here by
elaboration: `tanTwoTheta_wholeSpace_paperUINorm` concludes
`(b - a) * N.gauge (paperTanTwoAngleOperatorC U V) <= 2 * N.gauge H` for every
`PaperUnitaryInvariantNorm`, on an arbitrary complete complex Hilbert space, with NO
`IsQuarterAcute` among its hypotheses (it is concluded from the four ordered form bounds) and
`[propext, Classical.choice, Quot.sound]`.  The recorded remaining axes -- branch-free ambient,
and the residual constant on the directed half -- are the two the audit asked for, and they are
already in `scope_gap` and `next_action`.  No change to this row.

**THE GEOMETRY OF THE AMBIENT HALF IS BRANCH-FREE 2026-08-09 (Claude Opus 5).
THE BRANCH NOW SITS IN EXACTLY ONE HYPOTHESIS, AND IT IS NAMED.**  The row stays
`compiled_specialization`: the branch-free ambient ESTIMATE is still open.

The question asked was where `IsQuarterAcute` actually enters the ambient proof, and
whether the operator identities need it.  The answer is now certified rather than
asserted: the identities do NOT need it, and neither does anything else between the
directed corner estimate and the ambient conclusion.

WHAT THE BRANCH WAS DOING, in three places, only one of them real:
(1) invertibility of `1 - 2 sin^2 Theta` (which is `cos 2Theta`), obtained from
    `||sin Theta|| < sqrt 2 / 2` by a Neumann series;
(2) continuity of `t -> tan (2t)` on the spectrum of `Theta`, and the pointwise scalar
    identity behind `tan^2 2Theta * cos^2 2Theta = sin^2 2Theta`;
(3) NONNEGATIVITY of `tan 2Theta`, which the modulus identity `|Xi| = tan 2Theta` needs.
(1) and (2) follow from the PAPER'S OWN `cos 2theta != 0` -- pointwise nonvanishing on the
angle spectrum, which is compact, so the pointwise condition is automatically the uniform
separation invertibility wants.  (3) does not: past `pi/4` the tangent is negative.  (3)
disappears once the ambient object is `|tan 2Theta|`, which no unitarily invariant norm
can tell from `tan 2Theta`.

NEW DECLARATIONS, all axiom-clean -- [propext, Classical.choice, Quot.sound], checked at
the elaborator, not by grep:
* `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC` (`Geometry/Angle/PaperTanAngle.lean`)
  -- `cfc (fun t => |tan (2t)|) Theta`.  Nonnegative with NO hypothesis at all, and equal
  to `paperTanTwoAngleOperatorC` on the quarter-acute branch.
* `TauCeti.DavisKahan1970.isUnit_one_sub_two_mul_paperProjectorDifference_sq_of_cos_two_ne_zero`
  -- `cos 2Theta` is invertible from `cos 2theta != 0` alone.
* `TauCeti.DavisKahan1970.paperAbsTanTwo_sq_mul_cos_two_sq` and
  `TauCeti.DavisKahan1970.paperAbsTanTwoAngleOperatorC_eq_modulus_blockRepresentative` --
  `|Xi| = |tan 2Theta|` as an OPERATOR identity, branch-free.
* `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_all_kyFan_of_corner` and
  `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_of_corner` -- THE REDUCTION.
  Given only `cos 2theta != 0` and the printed residual estimate on the directed corner,
  `delta * N (|tan 2Theta|) <= 2 * N H` for every `PaperUnitaryInvariantNorm`, on an
  arbitrary complete complex Hilbert space with `[U.HasOrthogonalProjection]`, membership
  CONCLUDED.  There is no `IsQuarterAcute`, no contraction bound on the graph coordinate,
  and no spectral placement on the blocks of `A + H`.

No statement already on this row changed.  `tanTwoTheta_wholeSpace_all_kyFan` and
`tanTwoTheta_wholeSpace_paperUINorm` are now DERIVED from the reduction, and the private
`Modulus` lemmas were re-parameterised from `||sin Theta|| < sqrt 2 / 2` to
`IsUnit (1 - 2 D^2)`, which is all they ever used.

**THE REMAINING OBLIGATION IS NOW EXACTLY ONE INEQUALITY**, the `hcorner` hypothesis of
the reduction:
`(b - a) * kyFan_k (P_Uperp . 2 D (1 - 2 D^2)^{-1} . P_U) <= 2 * kyFan_k (P_Uperp H P_U)`,
allowing principal angles past `pi/4`.

**THE RECORDED MULTISET COUNTEREXAMPLE IS CORRECT, AND IT DOES NOT DEPEND ON THE POLE.**
Re-derived here.  With `G = X*X` positive, essential spectrum `{100}` and an isolated
eigenvalue at `4`: `a_n(G) = 100` for every `n`, so every
`absDoubleAngleTangent (sqrt (a_n G))` is `20/99`, while the corner has the isolated
singular value `2*2/|1-4| = 4/3`.  No bijection matches those multisets.  Note this
version stays FAR from `x = 1` and keeps every `|tan 2theta|` under `2||H||/delta`, so it
is not excluded by the pole separation the gap supplies -- the earlier note's `1 + eta`
version was, since its `|tan 2theta| ~ 2/eta` violates the very bound being proved.  The
real content is that `t -> 2t/|1 - t^2|` is NOT MONOTONE, so a singular value of `X` lying
BELOW its essential norm can be sent ABOVE it; approximation numbers are blind to the
first and see the second.

**THE FAILURE IS NOT ONLY IN THE SORTING: IT IS ALREADY AT THE LEVEL OF SINGLE PAIRS.**
This is new, and it closes off the route the previous `next_action` proposed.  Take
principal angles `theta' = pi/8` and `theta'' = 3pi/8`, so `tan 2theta' = 1 = -tan 2theta''`,
with unit principal vectors `u', u''` in `U` and `v', v''` in `Uperp`.  Then
`u = (u' + u'')/sqrt 2`, `v = (v' - v'')/sqrt 2` is an EXACT singular pair of the corner
with singular value `1` -- and the sign flip in `v` is precisely the paper's "choose the
sign according to `cos 2theta_j`".  But it is not even an approximate singular pair of the
graph coordinate `X`, whose two components carry the UNEQUAL positive values
`tan(pi/8) = 0.414` and `tan(3pi/8) = 2.414`; the best `t >= 0` leaves an error of about
`1.73`.  So a per-pair estimate for the corner cannot be transported from a per-pair
estimate for `X`, however the family is chosen.

**WHAT A BRANCH-FREE CORNER ESTIMATE WILL HAVE TO USE**, worked out on paper and NOT yet
formalised.  Write `p = P_U`, `q = P_V`, `G = (1-p) q p`, `sigma = D^2 = sin^2 Theta`,
`R = (1-p) H p`.  Then `sigma` commutes with `p` and with `q`, hence with `(1 - 2 sigma)^{-1}`
and with the corner, and the corner is `2 G (1 - 2 sigma)^{-1}`.  Invariance of `V` under
`A + H` plus off-diagonality of `H` give the branch-free, dimension-free SYLVESTER EQUATION
`A_1 G - G A_0 = sigma R + R sigma - R`.
Pairing it against an approximate singular pair `(u, v, s)` of the corner reproduces the
`b` and `a` form bounds correctly but leaves the term
`s * (Re <sigma u, A u> - Re <A v, sigma v>)`,
which the ordered form bounds do NOT control, because `sigma` and `A` do not commute.
Closing that term -- or finding a pairing that avoids it -- is the open point.

**M30 CLOSED 2026-08-09 (GPT-5.6 Sol): THE BRANCH-FREE AMBIENT HALF IS NOW THE INTEGRATED SOURCE PATH.**  `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean` supplies the missing directed-corner estimate directly from the Section 7 reflection equation, using approximate leading singular families of the actual tangent corner, signed-cosine polar isometries, the corrected Gram identities, and the magnitude Ky Fan variational theorem.  The public chain is `tanTwoTheta_directedCorner_residual_all_kyFan_branchFree`, `..._upper`, `tanTwoTheta_wholeSpace_all_kyFan_branchFree`, and `tanTwoTheta_wholeSpace_paperUINorm_branchFree`.  The lower-to-upper residual transport is only adjoint/Ky-Fan invariance, so it introduces no second factor two: the sharp factor `2` still comes exactly once from the two residual pairings in equation (7.6).  The whole-space endpoint reuses `tanTwoTheta_wholeSpace_*_of_corner`; no ambient Lemma-6.1 machinery is duplicated.  No `IsQuarterAcute` hypothesis or graph-coordinate spectral rearrangement is used.  The module is imported by `DavisKahan.Sources.DavisKahan1970.All`, so these declarations are now part of `DavisKahan.All` and are compiler-probed by this row.

DECLARATION LIST COMPLETED 2026-08-09 (Claude Opus 5, integrating M30).  The M30 upgrade to `compiled_exact` is substantively justified -- the branch-free ambient endpoints carry no finite-dimensionality hypothesis, and the off-diagonal conditions `hHU`/`hHUperp` on `H` are the paper's own Section 7 residual form and predate M30 throughout `TanTwoThetaWholeSpace.lean` -- but it was recorded WITHOUT NAMING THE TWO DECLARATIONS THAT JUSTIFY IT.  The row already listed the branch-carrying and `_of_corner` whole-space endpoints; what it did not list were `tanTwoTheta_wholeSpace_all_kyFan_branchFree` and `tanTwoTheta_wholeSpace_paperUINorm_branchFree`, which are precisely the ones that close the gap the previous `scope_gap` named.  The census gate therefore had nothing to disagree with -- the omitted-declaration failure documented in the header of `scripts/probe_census_declarations.py`, whose own example is an earlier instance on this same row.  Both are now listed; both resolve from `DavisKahan.All` and are `[propext, Classical.choice, Quot.sound]`, as are the two directed corner endpoints M30 rewrote.
- **Next action:** Nothing outstanding at this bounded Section 2 source scope.  The branch-free ambient reflection path is integrated and compiler-probed.  The distinct unbounded tan(2 Theta) ideal-gauge extension remains tracked on `S2-unbounded-scope` / `DK-6-appendix`, not on this row.

#### Section 2, paragraph after four theorems: Best constants and simultaneous equality

- **Kind:** `source_claim`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** All four constants are optimal in two dimensions, and finite direct sums realize equality simultaneously for all unitary-invariant norms.
- **Current Lean references:** `TauCeti.DavisKahanTheory.sinTheta_constant_optimal`, `TauCeti.DavisKahanTheory.sinTwoTheta_constant_optimal`, `TauCeti.DavisKahanTheory.single_double_sine_tangent_ratios_tendsto_one`, `TauCeti.DavisKahanTheory.sinTheta_model_equality`, `TauCeti.DavisKahanTheory.tanTheta_model_equality`, `TauCeti.DavisKahanTheory.tanTwoTheta_model_equality`, `TauCeti.DavisKahanTheory.sinTwoTheta_model_operatorNorm_equality`, `TauCeti.DavisKahanTheory.sinTwoTheta_model_equality`, `TauCeti.DavisKahanTheory.sinTwoTheta_model_equality_fails_beyond_operatorNorm`, `TauCeti.DavisKahanTheory.norm_sinTwoAngle_model_eq_norm_sinAngle_doubled`, `TauCeti.DavisKahanTheory.model_all_four_equalities`, `TauCeti.DavisKahanTheory.sinTheta_directSum_model_equality`, `TauCeti.DavisKahanTheory.tanTheta_directSum_model_equality`, `TauCeti.DavisKahanTheory.sinTwoTheta_directSum_model_equality`, `TauCeti.DavisKahanTheory.tanTwoTheta_directSum_model_equality`, `TauCeti.DavisKahanTheory.directSum_model_all_four_equalities`, `TauCeti.RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum_linearIsometryEquiv`, `TauCeti.RectangularUnitarilyInvariantSeminorm.singularValues_orthogonalBlockSum_congr`, `TauCeti.RectangularUnitarilyInvariantSeminorm.apply_orthogonalBlockSum_eq_of_singularValues_smul_eq`, `TauCeti.DavisKahanTheory.sinTheta_model_isAdmissiblePair`, `TauCeti.DavisKahanTheory.sinTheta_perturbation_le_model_equality`, `TauCeti.DavisKahanTheory.tanTheta_model_isAdmissiblePair`, `TauCeti.DavisKahanTheory.tanTheta_perturbation_le_model_equality`, `TauCeti.DavisKahanTheory.sinTwoTheta_model_isAdmissiblePair`, `TauCeti.DavisKahanTheory.sinTwoTheta_perturbation_le_model_operatorNorm_equality`, `TauCeti.DavisKahanTheory.sinTwoTheta_model_equality_of_admissiblePair`, `TauCeti.DavisKahanTheory.tanTwoTheta_model_isAdmissiblePair`, `TauCeti.DavisKahanTheory.tanTwoTheta_perturbation_le_model_equality`, `TauCeti.DavisKahanTheory.projection_orthogonalBlockSumSubmodule`, `TauCeti.RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule`, `TauCeti.RectangularUnitarilyInvariantSeminorm.mem_orthogonalBlockSumSubmodule`, `TauCeti.RectangularUnitarilyInvariantSeminorm.starProjection_orthogonalBlockSumSubmodule`
- **Assessment:** Sine sharpness and finite multiplicity are compiled; full quartet simultaneous equality remains in the Part III campaign.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_exact`. The three optimality/ratio witnesses are compiled, axiom-clean, and resolve against the default build. The earlier next_action instruction to "promote them into the build" is discharged -- they already resolve there.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 2 -- the row was internally
contradictory (`compiled_exact` and `next_action: "Proved"` over notes that say "full quartet
simultaneous equality remains") -- is UPHELD, and the notes were the accurate half.

**STATUS LOWERED `compiled_exact` -> `compiled_specialization`.**  What was over-claimed: the
printed sentence is that the constants in ALL FOUR theorems are best possible and that equality is
attained SIMULTANEOUSLY FOR ALL unitarily invariant norms by direct sums of two-dimensional
examples.  Measured by elaboration, four plane models are compiled and were all missing from this
row's declaration list:

* `sinTheta_model_equality`, `tanTheta_model_equality`, `tanTwoTheta_model_equality` --
  equality for EVERY `UnitarilyInvariantSeminorm` on the plane, `RCLike`-generic;
* `sinTwoTheta_model_operatorNorm_equality` -- OPERATOR NORM ONLY.

So three of the four families reach the printed "all unitarily invariant norms"; the `sin 2theta`
family does not.  And the direct-sum construction that turns the plane models into simultaneous
attainment in higher dimension is not formalized at all.  The old `next_action` ("promote them
into the build") was also stale: all seven declarations now on this row resolve against
`DavisKahan.All`.

**BOTH PREVIOUSLY-RECORDED OBLIGATIONS ARE DISCHARGED, 2026-08-10 (Claude Opus 5, coordinator-verified) -- BUT ONE OF THEM WAS MIS-STATED IN THIS ROW AND THE OTHER WAS FALSE AS POSED.**

**OBLIGATION (1) AS POSED IS FALSE, AND THE REFUTATION IS COMPILED.**  This row asked for the `sin 2theta` model equality `at EVERY unitarily invariant seminorm, matching` the three siblings.  No such generalization of `sinTwoTheta_model_operatorNorm_equality` exists, because THE TWO SIDES ARE NOT RANK-MATCHED: `sinTwoAngleOperator U V = 2 P_Uperp P_V P_U` is ONE-SIDED, supported on `U`, with singular values `(sin 2theta, 0)` in the plane, whereas `modelSinTwoThetaPerturbation` is a full-rank symmetric off-diagonal block with singular value `((b-a)/2) sin 2theta` TWICE.  The lists are not proportional, so no gauge-level argument can work.  `sinTwoTheta_model_equality_fails_beyond_operatorNorm` proves it: Ky Fan 2 separates the two sides by exactly the factor the rank mismatch carries.  NOTE: `Sharpness.lean` had ALREADY recorded this in its note on the removed `directSum_models_simultaneous_equality`; that note was right and this row contradicted it.

THE RANK-MATCHED REPLACEMENT, `sinTwoTheta_model_equality`, measures the double angle by the SYMMETRIC sine of the DOUBLED angle -- the sine of the angle to the subspace reflected through the rotated line, which in this model is `rotatedModelSubspace (2*theta)`.  Both sides then carry `(b-a) sin 2theta` twice and the proof mirrors `tanTwoTheta_model_equality`.  **THIS IS A CHANGE OF NORMALIZATION, NOT A NARROWING OF HYPOTHESES**, and the two endpoints coexist: `sinTwoTheta_model_operatorNorm_equality` is retained and `norm_sinTwoAngle_model_eq_norm_sinAngle_doubled` proves it is exactly the operator-norm shadow of the new theorem, the one-sided map and the doubled-angle sine having equal operator norm.

**OBLIGATION (2) WAS AN OVER-READING OF THE SOURCE, AND THIS ROW PROPAGATED IT.**  The field asked for `a pair in which ALL FOUR conclusions attain equality simultaneously ... which is what the source asserts`.  IT IS NOT.  Transcription L777, quoted: `Furthermore, one sees by taking a direct sum of 2-dimensional examples that, IN ANY ONE OF THE THEOREMS, equality in the conclusion can be attained simultaneously for all unitary-invariant norms.`  `Simultaneously` qualifies THE NORMS; `in any one of the theorems` explicitly scopes it to ONE theorem at a time.  COORDINATOR-VERIFIED by reading L777 and by checking that a single pair COULD NOT do it anyway: the four extremal residual sizes `(b-a) sin theta`, `(b-a) tan theta`, `((b-a)/2) sin 2theta`, `((b-a)/2) tan 2theta` are PAIRWISE DISTINCT throughout `(0, pi/4)`.

What landed for (2) is therefore the correct statement and more: per-theorem direct-sum equalities at every unitarily invariant seminorm, for INDEPENDENT angles in the two blocks, plus `model_all_four_equalities` and `directSum_model_all_four_equalities` recording the four configurations together.

EXISTING MACHINERY WAS REUSED, NOT REBUILT: `orthogonalBlockSum` and `singularValues_orthogonalBlockSum_self` already existed in `ForTauCeti/.../RectangularUnitarilyInvariantSeminorm/BlockSum.lean`, as did the infinite-dimensional Ky Fan merge formula in `DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean`.  What was missing is the CONGRUENCE form, which is what the extremal construction needs and which AVOIDS the merge formula entirely (equal blockwise singular values imply the blocks differ by unitaries, and block sums of unitaries are unitaries).  Added to the EXISTING module, so no new `ForTauCeti` module and no ladder or readiness ratchet movement.

**ALL FOUR MODELS ARE ADMISSIBLE, 2026-08-11 (Claude Opus 5, coordinator-verified).**  `sin Theta`: `A = modelGappedOperator a b`, `B = modelRotatedOperator a b theta`, and `B - A` is LITERALLY `modelSinThetaPerturbation`.  `tan Theta`: base `modelGappedOperator a (a + (b-a)(1 + tan^2 theta))` with the residual off-diagonal in the ROTATED frame.  `sin 2Theta`: base `modelGappedOperator b a` -- note the ORDER, the orientation `TwoBlockFormGap` requires -- plus a rotated off-diagonal.  `tan 2Theta`: `B = A - modelTanTwoThetaPerturbation`, a SIGN correction.  In each case the admissible residual has the same singular values as the stated model matrix, hence equality at every UI seminorm.

**THE COORDINATOR'S TANGENT HINT WAS HALF WRONG.**  `tan 2Theta` was already admissible -- the Riccati law does produce the entry and the internal gap is exactly `b - a`.  `tan Theta` WAS NOT: with `A` diagonal and `B = A + modelTanThetaPerturbation`, Riccati forces the internal gap `(b-a)(1 - tan^2 theta)`, that configuration does not attain equality, and the coordinate-frame matrix VIOLATES the tangent theorem's Galerkin hypothesis, since `<H u_theta, u_theta> = (b-a) tan theta sin 2theta != 0`.  Verified symbolically and numerically before the corrected pair was built.

**A SHARPER FORM OF THE FIDELITY PROBLEM THAN THIS ROW HAD RECORDED.**  THREE of the four `*_model_equality` theorems were ARITHMETIC TAUTOLOGIES BY CONSTRUCTION: `modelTanThetaPerturbation`, `modelSinTwoThetaPerturbation` and `modelTanTwoThetaPerturbation` are DEFINED with exactly the entries `(b-a) tan theta`, `((a-b)/2) sin 2theta`, `((b-a)/2) tan 2theta` that make both sides carry the same singular pair.  Only `modelSinThetaPerturbation` was derived from anything -- it is exactly `R A R^T - A`.  So the `*_model_equality` set carried NO THEOREM CONTENT until the admissible pairs landed.

AUDIT, corrected in place: `modelTanTwoThetaPerturbation`'s docstring stated the Riccati law with the WRONG SIGN (`tan 2theta = 2h/(b-a)`; correct is `2h/(a-b)`), under which the reducing line sits at `-theta`.  The DEFINITION was left alone -- its singular values, and hence `tanTwoTheta_model_equality` and `singularValues_modelTanTwoThetaPerturbation`, are unaffected.
- **Next action:** Supply canonical-form residual bounds for `tanAngleOperator` and `tanTwoAngleOperator` so the two tangent equalities become `:=`-grounded on compiled repository inequalities rather than equality against the source statement.  Then the two mechanical wirings in `scope_gap`.

#### Section 2, final paragraphs: Unbounded self-adjoint scope

- **Kind:** `scope_claim`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** The four theorem families extend to unbounded self-adjoint operators under bounded perturbation or residual assumptions, with analytic work concentrated in Theorem 5.2 and the Section 6 appendix.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.canonical_generalizedSinTheta`, `TauCeti.DavisKahan1970.unbounded_sinTheta_opNorm`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_ideal_directedTangent_of_reducing`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_ideal_of_reducing`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.crossed_lower_of_reducing`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_ideal_directedTangent`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_ideal`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.Theorem63TrialData.all_kyFan_core_of_formBounds`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`, `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_residual_opNorm`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.sinTheta_unbounded_real`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_unbounded_real`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.sinTheta_unbounded_real_spectralSubspace`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_unbounded_real_spectralSubspace`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_opNorm_real`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_reflectionResidual_opNorm_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_real`, `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteData_real`
- **Assessment:** The sine family is complete in source scope. Tangent has an operator-norm graph-coordinate companion, but the paper claims arbitrary-UI-norm unbounded scope and the cutoff/Ky-Fan passage is not yet formalized.

**THE ARBITRARY-UI-NORM UNBOUNDED TANGENT THEOREM IS DONE, 2026-08-06.** The sine family was already complete in source scope; the tangent family had only an operator-norm graph-angle companion, and the census warned not to credit it as the scope claim. `theorem6_3_unbounded_ideal_directedTangent` (DavisKahan/TanTheta/Theorem63Unbounded.lean, default build, axiom-clean) is the scope claim: closed unbounded self-adjoint ambient operator, arbitrary Fan-dominant unitarily invariant ideal gauge, tangent representative constructed rather than assumed.

HOW THE UNBOUNDED CASE REUSES THE BOUNDED CHAIN. `Theorem63TrialData` records what the tangent argument actually consumes -- a bounded action, compression and residual tied by the block identity -- and `all_kyFan_core_of_formBounds` proves the Ky Fan root from the two printed form bounds alone, with no bounded ambient operator in sight. The crossed action is not extra data: it is P_Vperp o action. For an unbounded operator that is A(P_Vperp z), which is DEFINED because spectral projections preserve the domain (selfAdjointSpectralProjection_mem_domain) and commute with the operator there (selfAdjoint_apply_spectralProjection). Those are the only vectors at which the argument ever evaluates the quadratic form.

WHY THE ARGUMENT GOES THROUGH A THRESHOLD c < alpha+delta RATHER THAN APPLYING THE ENERGY BOUND ONCE: the gap is the OPEN interval, so the endpoint alpha+delta is allowed to carry spectrum and P_{Iic (alpha+delta)} y need not vanish. It does vanish on Iic c for every c < alpha+delta, and the constant follows by taking c up to the endpoint.

**PRINTED FIDELITY RESTORED 2026-08-08 (Claude Opus 5).**  The compiled unbounded tangent theorem was strictly narrower than the printed one.  Theorem 6.3 as printed (transcription L2060--2073; Section 2 tan-theta hypotheses at L1958--1963) assumes a CHOSEN pair of complementary reducing subspaces `Range F_0` / `Range F_1`, with `A_0 <= alpha` on the trial compression and `alpha + delta <= Lambda_1 = F_1^* (A+H) F_1`; the compression `Lambda_0` to the chosen subspace is entirely unconstrained.  `theorem6_3_unbounded_ideal(_directedTangent)` instead fixed `V := selfAdjointSpectralSubspace A hA (Iic alpha)` -- `V` was not a variable -- and demanded `specProjection hA (Ioo alpha (alpha+delta)) = 0`, a spectrum-free interval for the WHOLE operator.

That is strictly stronger.  Counterexample: `spec A = {0,5,10}`, `alpha = 1`, `delta = 9`, trial `Z = span{e_0}`, chosen `V = specSubspace (Iic 5)`.  Then `spec Lambda_1 = {10}` lies in `[alpha+delta, inf) = [10, inf)`, so every printed hypothesis holds, while the compiled hypothesis fails because `5` is in `spec A` and in `(1, 10)`.

The printed statements are now `theorem6_3_unbounded_ideal_of_reducing` and `theorem6_3_unbounded_ideal_directedTangent_of_reducing` (same module, default build, axiom-clean): `V` is a variable; its reducing property is `hVdom` (the projection onto `V perp` preserves the domain) and `hVcomm` (it commutes with the operator there); and the printed `alpha + delta <= Lambda_1` is the form lower bound `hUnwanted` on `V perp`.  The decoupling is `crossed_lower_of_reducing`, and the spectral-gap statements `crossed_lower_of_spectralGap` / `theorem6_3_unbounded_ideal(_directedTangent)` are now derived from it at `V = specSubspace (Iic alpha)`, unchanged for their consumers (`beamTanTheta_le` among them).

THE NARROWING WAS NOT COSMETIC: Section 9's direct one-vector estimates (the paragraph after (9.8)) are unreachable from the spectral-gap form, because at `alpha = ritzLow eps` the required interval `(ritzLow eps, 500)` contains the upper Ritz level's spectrum.  They are now proved -- see DK-9.8.

**THE FINITE-DIMENSIONAL TRIAL SPACE IS GONE, 2026-08-09 (Claude Opus 5, auditing external commit `fd91e376`).**

Every unbounded tangent endpoint recorded above carries `[FiniteDimensional C Z]` -- verified by elaborating `theorem6_3_unbounded_ideal_directedTangent_of_reducing`, which has it.  The Appendix removes exactly that hypothesis ("allow for noncompact `Theta`"), so the scope claim was not fully delivered.  It is now: `theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing` proves the printed reducing-subspace form for an ARBITRARY complete trial subspace, at every Fan-dominant unitarily invariant ideal gauge, with the tangent representative exhibited.  Axiom-clean, in the default build.

**STATUS LOWERED 2026-08-09 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`.  THIS IS A CORRECTION OF AN OVERSTATEMENT, NOT A REGRESSION.**

The printed scope claim (transcription L782--786) is about ALL FOUR theorems: "The theorems above contain references to a finite interval `[beta,alpha]`; they remain valid after this interval is extended to `]-inf,alpha]` ... As long as the spectra of `A_i` and `Lambda_i` satisfy their respective hypotheses concerning the gap `delta`, they may be otherwise unbounded without invalidating the theorems."  "The theorems above" are the `sin Theta`, `sin 2Theta`, `tan Theta` and `tan 2Theta` theorems of Section 2, each stated for arbitrary unitary-invariant norms.  Measured against that:

* `sin Theta` -- DONE at unbounded x arbitrary Fan-dominant ideal gauge (`canonical_generalizedSinTheta`).
* `sin 2Theta` -- DONE at unbounded x arbitrary Fan-dominant ideal gauge (`unbounded_sinTwoTheta_uiNorm_representative`, closed self-adjoint `A`, arbitrary representative).
* `tan Theta` -- DONE, and since this session also at arbitrary trial dimension.
* `tan 2Theta` -- **NOT done.**  The only unbounded declaration is `tanTwoTheta_unbounded_residual_opNorm` (with `_div`), which is the OPERATOR NORM (Ky Fan prefix `nu = 1`) and the RESIDUAL form only (`B` fully off-diagonal, i.e. `H_0 = H_1 = 0`).  The Ky Fan `nu >= 2` case is open and the perturbation form `delta N(tan 2Theta) <= 2 N(H)` is open; the obstruction -- the bounded argument's error coefficient is proportional to `||A||`, and the cutoff device that controls the `A_0` side has no counterpart on the `A_1` side -- is written out in full on DK-6-appendix.

Three of the four families at full source scope and the fourth at one norm is precisely `compiled_specialization`: "a useful compiled specialization exists, but not the full source scope".  The earlier `compiled_exact` was set when the tangent family landed and reasoned only about the sine and tangent families; the double-angle tangent was never checked against this row.

SCALAR SCOPE, measured the same day by elaborating each listed declaration: `canonical_generalizedSinTheta`, `unbounded_sinTwoTheta_uiNorm_representative`, all five unbounded tangent endpoints and `tanTwoTheta_unbounded_residual_opNorm` are `InnerProductSpace C` without exception.  So this row also carries the standing real-scalar gap, now recorded in `blocked_by` and `scope_gap`.

**SCOPE_GAP CORRECTED 2026-08-09 (Claude Opus 5, M34).**  See `scope_gap` for the measurement.  In one line: the claim that no unbounded-scope theorem over a real Hilbert space exists anywhere in the repository was false, `unbounded_sinTheta_opNorm` is `RCLike`-generic rather than complex-only, and the real unbounded sine and double-angle-sine families are compiled and are now listed on this row.  The blocker stays because the unbounded TANGENT endpoints -- the five `theorem6_3_unbounded_*` and `tanTwoTheta_unbounded_residual_opNorm` -- and the ~3800-line tree beneath them are complex-only.  That fixing is a convention rather than a mathematical dependency, and two routes to remove it are named in `scope_gap`.

**THE REAL UNBOUNDED TANGENT FAMILY IS DONE, 2026-08-09 (Claude Opus 5, M35).**

The scalar gap recorded above for the tangent side is closed, at the PRINTED Theorem 6.3 hypothesis and at arbitrary trial dimension.  `theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real` (`DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean`, default build, axiom-clean) is: a REAL Hilbert space of arbitrary dimension; a closed unbounded REAL operator (`ClosedOperator (𝕜 := ℝ)`); an arbitrary complete REAL trial subspace with no dimension hypothesis; an arbitrary CHOSEN reducing subspace `V` under the printed `hVdom` / `hVcomm` / `hUnwanted` and nothing more; an arbitrary REAL Fan-dominant unitarily invariant ideal gauge; the tangent representative constructed over the real trial space and exhibited; and its ideal membership CONCLUDED.  `..._ideal_of_reducing_real` is the caller-supplied-representative form.  `..._ideal_exists_real` and `..._ideal_real` are the spectral-gap specializations at `V = realSelfAdjointSpectralSubspace A hA (Set.Iic α)`, whose reducing hypotheses come from `DavisKahan/SpectralTheory/Real/SpectralRestriction.lean` and whose form bound `α + δ ≤ Λ₁` comes from a real spectral gap.

Because none of the real endpoints carries a finite-dimensionality hypothesis on the trial space, they cover the real-scalar analogue of the complex entries `theorem6_3_unbounded_ideal{,_directedTangent}{,_of_reducing}` (all `[FiniteDimensional ℂ Z]`) as well.

WHAT ACTUALLY HAD TO DESCEND, AND IT IS ONE LINK, NOT THE TREE.  `UnboundedTrialBlock`, `Theorem63TrialData`, `Theorem63TrialData.ofUnbounded` and `crossed_lower_of_reducing` are now stated over `RCLike 𝕜` in their own modules -- structure definitions and proofs verbatim, no mathematics changed, no duplicate real structure introduced.  So `crossed_lower_of_reducing` is real already.  The single link that is genuinely complex is `Theorem63TrialData.all_kyFan_core_of_formBounds_infinite`; it is transported by `theorem6_3_all_kyFan_core_infiniteData_real` through `complexifyTrialData`, at the finite Ky Fan level where complexification preserves approximation numbers on the nose, exactly as `Sources/DavisKahan1970/DirectedReal.lean` transports the bounded tangent.  No ideal family is compared across scalar fields: the real endpoint is stated over a REAL `KyFanDominantIdealFamily`, which is legitimate for the reason already recorded on the blocker (the structure is `RCLike`-generic).

SUPPORTING REFACTOR: the spectral-gap form bound was extracted from the body of `crossed_lower_of_spectralGap` as the standalone `le_re_inner_of_mem_orthogonal_selfAdjointSpectralSubspace_of_gap` (`DavisKahan/TanTheta/Theorem63Unbounded.lean`), so that the real side can transport the statement rather than re-run the threshold argument.  `crossed_lower_of_spectralGap` is now a one-line corollary of it and of `crossed_lower_of_reducing`.

CORRECTION TO THE MEASUREMENT THIS ROW RECORDED IN `scope_gap`.  The claim that the roughly 3800-line tangent tree is complex "by convention, not by mathematics" is HALF FALSE, and the false half is the half that mattered for choosing a route.  It holds for `Theorem63FiniteSource`'s data layer, for `Theorem63TrialData` and for `Theorem63Unbounded`'s reassembly.  It FAILS for the Appendix passage: `Theorem63InfiniteTrial.lean` and `Theorem63UnboundedInfiniteTrial.lean` (about 1470 of those lines) reach `TauCeti.BorelCalculus.exists_finiteDimensional_le_almostInvariant`, whose only tool for producing a finite-dimensional almost-invariant subspace is `boundedPVM` / `borelCalculus` -- the ℂ-only bounded projection-valued measure of `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/`, the same ℂ-only foundation recorded on the Section 3 tranche.  Route (a) of `scope_gap`, "generalize the tangent tree to `RCLike`", is therefore BLOCKED, not merely large.  Route (b), transport, is the correct one and is the one taken.

**MAJOR RESCOPE 2026-08-10 (Claude Opus 5, coordinator-verified).  THE UNBOUNDED KY FAN CHAIN IS ALREADY BUILT, AND THE COMPLETION HANDOFF DOES NOT SAY WHERE.**

`FinishTanTwoTheta/FinishTanTwoTheta/DavisKahan/Unbounded.lean` (597 lines) already contains the whole chain: the per-pair estimate, the finite summation, the epsilon-removal, Ky Fan at EVERY prefix, and the arbitrary-UI-norm endpoint `sharp_unbounded_standardSymmetricIdeal_scaled` -- all already free of `||A0||` and `||A1||`.  Handoff section 5.F, which is this row's recorded route, does not mention the file.

**IT REDUCES TO EXACTLY ONE OPEN SEAM**, `exists_unboundedApproximateLeadingSingularFamily` -- the only `sorry` in the package.  As of today the ANALYTIC half of that seam is discharged: `unboundedApproximateLeadingSingularFamily_of_bandBound` (AXIOM-CLEAN, coordinator-probed) supplies the family from domain-valued orthonormal approximants carrying band bounds `||A0 (right i)|| <= tau` and `||A1 (left i)|| <= tau`, under `eps0 <= eps` and `tau * eps0 <= eps`.  `sharp_unbounded_doubleAngleTangentOperator_kyFan_of_selection` is now also AXIOM-CLEAN, the first time any part of this chain has been shown `sorry`-free; the remaining obligation is an explicit hypothesis in the statement rather than buried mid-proof.

**WHAT REMAINS IS GEOMETRIC, NOT ANALYTIC.**  Not Gram control, not the pole bound, not the variational step -- all three are proved.  It is: produce orthonormal approximate singular vectors of `S.X` lying INSIDE `A0.domain`/`A1.domain` with the band bounds.  Density gives Hilbert-norm approximation only; the band bounds must come from spectral cutoffs, and repairing orthonormality after projecting into a band is where a quantitative Gram-Schmidt argument is finally needed.

**THREE RECORDED ROUTE ITEMS ARE WRONG OR MOOT, measured today.**  (i) The `y_k := S x_k / ||S x_k||` construction NEVER APPEARS in the repository; `||A0||`/`||A1||` were removed a different way, recorded 2026-07-29 in the structure's own docstring, by weakening the residual fields to PAIRINGS, with the note that graph-norm control was `strictly stronger than anything used, and provably too strong`.  (ii) The `eps^(1/3)` threshold was not used and could not be reproduced: the residual fields are absolute, so both error channels vanish for ANY `eps << theta << 1` and `sqrt(eps)` is the balance point.  UNFORMALIZED, and moot, since the seam is not the Gram-orthonormalization problem.  (iii) `Fixed spectral cutoff tau` is not the axis this divides on -- the proved chain is unconditional in `tau`.

**BUILD HAZARD, and the reason this was invisible:** `FinishTanTwoTheta` is a `lean_lib` but is NOT in `defaultTargets`, so the green 9580-job build compiles NONE of it.  Verify with an explicit `lake build FinishTanTwoTheta` (3533 jobs, EXIT=0 today).  The lakefile documents the exclusion as deliberate -- a `mathematics-first completion workspace` whose open extensions are `not glob-built as completed theorems` -- and NEITHER the census NOR the frontier names any `sharp_unbounded_*`, so nothing is overstated in the record.  But the names do read as delivered endpoints, so do not cite them as such until the seam closes.

**THE REMAINING SEAM IS NOW CHARACTERIZED, AND IT NEEDS NEW MATHEMATICS RATHER THAN PLUMBING.  MEASURED 2026-08-10 (Claude Opus 5, coordinator-verified).  DO NOT RE-DISPATCH AS A ROUTINE MISSION.**

HALF THE GEOMETRIC PROBLEM IS GONE.  `norm_A1_apply_le_of_band` (AXIOM-CLEAN) derives from the strong Riccati equation that banding the RIGHT vectors automatically bands the LEFT ones taken along the image `y` proportional to `X x`, at a cost of `||X x||`, which `selected_large` already holds above the retention threshold.  So a selection argument only has to band one side.

**THE OBSTRUCTION IS NOT WHERE ANY RECORDED ROUTE SAID.**  (i) NOT the band projection: `TauCeti.spectralCutoff` builds a working `BoundedCutoff` -- projection, range inside `dom A`, `||A(Pv)|| <= tau ||Pv||`, range `A`-invariant -- and `tendsto_specProjection_Icc` gives strong convergence.  (ii) NOT the orthonormality repair, which the coordinator's brief wrongly named as the crux: BAND RANGES ARE SUBSPACES, so Gram-Schmidt is a linear recombination that stays inside the band and preserves the band bound exactly.  No quantitative Gram-Schmidt is needed anywhere.  (iii) IT IS THE RESIDUAL-LEVEL COUPLING: no admissible `(tau, eps0)` pair exists by any argument resting on strong convergence.

THE MECHANISM, exactly.  Writing `P` for the `A0`-band at radius `tau`, the surviving pairing evaluates EXACTLY to `(||P X x|| - a) * <A1 y, y>` -- the leakage term is ANNIHILATED because `y` lies in the band and the band projection commutes with `A1`.  So the pairing is (residual) times (band radius), and closing it needs band vectors reproducing the leading singular values to accuracy `eps / tau`.  Band projections converge only STRONGLY, and `approximationSingularValue_comp_strongProjection_tendsto_complex` likewise gives convergence WITHOUT A RATE, so `tau * (displacement at radius tau)` need not tend to zero.  Choosing the ambient family first fixes its level before `tau` is known; choosing `tau` first does not bound the displacement.

A SECOND, INDEPENDENT MISMATCH: the ambient selection places its vectors in spectral bands of the GRAM operator `X* X` (a local step inside `exists_gramSpectralBandModel`, never exported), whereas the band required here is one of `A0`.  Those do not commute in general, so the existing selection CANNOT be re-aimed by plumbing alone, contrary to what the selection primitives suggest at first look.

**NEITHER OBSERVATION REFUTES THE STATEMENT.**  Both say that no argument resting only on strong convergence of spectral cutoffs will establish it.  UNTRIED ROUTE, recorded so it is not lost: the two pairings are just TWO REAL SCALARS, and `dom A0` is dense with many free directions, so tuning them directly -- an INTERMEDIATE-VALUE argument rather than a limiting one -- is not ruled out.

CORRECTION TO AN EARLIER CORRECTION ON THIS ROW: the handoff's `y_k := S x_k / ||S x_k||` idea is mis-aimed for removing `||A||` from the Ky Fan estimate, which was already done differently -- but it is EXACTLY RIGHT for the SELECTION problem, and it is the content of `norm_A1_apply_le_of_band`.  Right idea, wrong target.

MINOR PLUMBING, not a blocker: `spectralCutoff` is packaged only for a half-line trial subspace (`specRange hA (Iic c)`, band `Icc (-T) c`).  `UnboundedBlockData` has no cut point, so the two-sided `specProjection hA (Icc (-T) T)` is what is needed; it exists but is not packaged as a `BoundedCutoff`.
- **Next action:** One theorem family is missing at this row's own scope: the unbounded `tan 2Theta` theorem beyond the operator norm.  `tanTwoTheta_unbounded_residual_opNorm` is the `nu = 1` residual case; the Ky Fan `nu >= 2` case, the arbitrary-unitarily-invariant-norm endpoint, and the perturbation form `delta N(tan 2Theta) <= 2 N(H)` are all open, and the obstruction and its proposed repair are recorded on DK-6-appendix.  Nothing is outstanding for the sine, double-angle sine or tangent families at complex scalars, at the printed hypothesis, and now at arbitrary trial dimension.  The real-scalar lift of all four is the separate standing gap.  The operator-norm graph-angle companion `theorem6_3_unbounded_graphAngle_opNorm_companion` is retained and must still not be quoted as the scope claim.  REAL-SCALAR STATUS 2026-08-09 (M35): the unbounded sine, double-angle sine and single-angle TANGENT families are now all compiled over real Hilbert spaces of arbitrary dimension and arbitrary trial dimension; the only real-scalar item still outstanding on this row is a real counterpart of `tanTwoTheta_unbounded_residual_opNorm`, and it should wait for the complex `tan 2Theta` work named above.

### Section 3

#### Definition 3.1: Direct rotation

- **Kind:** `definition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** A unitary intertwining the two projections whose diagonal cosine blocks are positive and whose off-diagonal sine blocks are adjoints.
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation`, `TauCeti.DavisKahan.Experimental.spectraCanonicalIntertwiner`, `TauCeti.DavisKahan.Experimental.Frontier.IsPaperDirectRotation`, `TauCeti.DavisKahanTheory.angleComplexStructure`, `TauCeti.DavisKahanTheory.directRotation_eq_cos_add_J_sin`, `TauCeti.DavisKahanTheory.directRotationCosine_eq_half_smul_add`, `TauCeti.DavisKahanTheory.directRotation_sub_cosine_eq_half_smul_sub`, `TauCeti.DavisKahanTheory.directRotation_sub_cosine_comp_self`, `TauCeti.DavisKahanTheory.angleComplexStructure_comp_self`, `TauCeti.DavisKahanTheory.angleComplexStructure_comp_angleOperator_comp_self`, `TauCeti.DavisKahanTheory.directRotationCosine_eq_calculus`, `TauCeti.DavisKahanTheory.sinAngleOperator_eigenvalues_mem_Icc`, `TauCeti.DavisKahanTheory.directRotation_eq_exp_angleComplexStructure_comp_angleOperator`, `TauCeti.DavisKahan1970.real_directRotation`, `TauCeti.DavisKahan1970.real_directRotation_orthogonal`, `TauCeti.DavisKahan1970.real_directRotation_intertwines`, `TauCeti.DavisKahan1970.real_directRotation_diagonalBlock`, `TauCeti.DavisKahan1970.real_directRotation_complementaryDiagonalBlock`, `TauCeti.DavisKahan.Experimental.canonicalAbsoluteValueR`, `TauCeti.DavisKahan.Experimental.complexify_directRotationR`
- **Assessment:** Acute complex and finite constructions exist; exact nonacute source scope is not yet unified.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The direct-rotation construction is compiled and axiom-clean; a source-facing definition covering the paper's existence regimes is still absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

ROW WAS STALE; RESOLVED 2026-08-06.  The requested "source-facing definition" already exists and is guarded: `TauCeti.DavisKahan.Experimental.Frontier.IsPaperDirectRotation` (`DavisKahan/Geometry/Halmos/GenericRotationPredicates.lean`, reached from `DavisKahan.All`) is the paper's definition of a direct rotation for an ARBITRARY pair -- unitary, intertwines the projections, nonnegative diagonal compressions, skew-adjoint crossed blocks -- with no acuteness.  The "source existence regimes" the next action asked to cover are theorems on the numbered rows built on this definition: acute existence/uniqueness/characterisation on DK-3.1-prop (`complex_directRotation`, `complex_directRotation_iff_diagonalBlocks`), the nonacute existence criterion on DK-3.2-prop (`(∃ T, IsPaperDirectRotation U V T) ↔ ...`), and the principal-square-root characterisation on DK-3.3-prop, whose forward-of-nonneg-blocks form consumes exactly this predicate.  Axiom-clean [propext, Classical.choice, Quot.sound].

**M19, 2026-08-09 (Claude Opus 5).**  The Section 3 narrative between Proposition 3.4 and Theorem 3.1 introduces the intertwiner `J` from the polar resolution `S_0 = J_0 sin Theta_0` and writes the direct rotation as `U = cos Theta + J sin Theta = exp(J Theta)` (transcription L1060--1081).  Everything except the exponential form is represented, in finite dimension over any `RCLike` field: `angleComplexStructure` is `J`, `directRotation_eq_cos_add_J_sin` is the first equation, and `directRotation_sub_cosine_eq_half_smul_sub` identifies `J sin Theta` with the skew-Hermitian part `(U - U^{-1})/2` of the direct rotation, which is what the paper's off-diagonal block is.  `directRotationCosine_eq_half_smul_add` is the companion `cos Theta = (U + U^{-1})/2`.

NOT REPRESENTED AS OF M19: `U = exp(J Theta)`.  That needs the operator exponential and the power-series split into `cos` and `sin` on the range of `Theta`, using `J^2 = -1` there.

**M24, 2026-08-09 (Claude Opus 5).  `U = exp(J Theta)` IS NOW PROVED**, in finite dimension over any `RCLike` field.  `directRotation_eq_exp_angleComplexStructure_comp_angleOperator` (`DavisKahan/FiniteDimensional/DirectRotation/Exponential.lean`) states it for Mathlib's `NormedSpace.exp`; the statement is carried on `E ->L[k] E` rather than `E ->l[k] E` because that is the only place the operator exponential is defined, with `LinearMap.toContinuousLinearMap` as the finite-dimensional identification.

THE PREVIOUS NOTE'S `J^2 = -1` IS NOT THE TRUE IDENTITY, and stating it that way would be wrong.  Because the paper sets `J = 0` on `Null Theta`, the correct statement is `angleComplexStructure_comp_self`: `J^2 = -(sin Theta)(sin Theta)^+`, the negative of the Penrose projection onto the nonzero-angle space; `J^2 = -1` holds only there.  It rests on `directRotation_sub_cosine_comp_self` (`(U - cos Theta)^2 = -sin^2 Theta`, from `U + U^{-1} = 2 cos Theta` and the commutation of `cos Theta` with `U^{-1}`) and on `TauCeti.moorePenroseInverse_comm_of_isSymmetric`.

The exponential series is then evaluated on the eigenbasis of `sin Theta`, where `(J Theta)^2` acts by `-theta^2` (`angleComplexStructure_comp_angleOperator_comp_self`) and the even and odd halves are the power series of `cos theta` and `sin theta`.  Reassembling the even half needs `cos Theta = cos(arcsin(sin Theta))` (`directRotationCosine_eq_calculus`), and that needs the spectral bound `sinAngleOperator_eigenvalues_mem_Icc`, itself read off the positivity of `cos^2 Theta = 1 - sin^2 Theta`.

**M33, 2026-08-09 (Claude Opus 5).  THE REAL-SCALAR AXIS IS CLOSED ON THIS ROW.**  `DavisKahan/Geometry/Polar/DirectRotationReal.lean` constructs `TauCeti.DavisKahan.Experimental.directRotationR` -- the direct rotation of a pair of REAL closed subspaces of a real Hilbert space of arbitrary dimension -- and proves it satisfies the printed definition: it is orthogonal, it intertwines `P_U` with `P_V`, and both diagonal blocks are the positive Halmos cosine (`real_directRotation_diagonalBlock`, `real_directRotation_complementaryDiagonalBlock`).  Membership is CONCLUDED: `directRotationR_maps_subspace` proves `U.map W = V`.

THE DESCENT.  `spectraDirectRotation` is the polar factor of `S = P_V P_U + P_Vperp P_Uperp`.  For a complexified pair `S` is the complexification of a real operator, hence conjugation-fixed; `RealComplexification.conjugateOperator_modulus` (added by M31) makes `|S|` conjugation-fixed; in the acute case `|S|` is a unit, so cancelling it in `W |S| = S` makes `W` conjugation-fixed, and `complexify_realPartOperator` returns the real operator.  Nothing else was needed -- no re-proof of the polar decomposition over `R`.

What is left on this row is the DIMENSION axis on `J`, which is a different blocker's business, plus the standing `exact-source-wrappers` entry.

**M37, 2026-08-09 (Claude Opus 5).  STALE BLOCKER ENTRY REMOVED.**  `exact-source-wrappers` asked for 'a statement carrying the paper's numbering, scope and hypotheses'.  This row's 2026-08-06 note had already recorded that `IsPaperDirectRotation` IS printed Definition 3.1, for an arbitrary pair and with no acuteness, and its `next_action` opens 'Nothing outstanding for the printed narrative'.  Re-measured 2026-08-09 by elaborating `IsPaperDirectRotation`, `complex_directRotation`, `real_directRotation` and `directRotation_eq_exp_angleComplexStructure_comp_angleOperator` against `DavisKahan.All`: every one resolves and every one is axiom-clean.  The gap this row still carries is the DIMENSION axis on the quarter turn `J`, recorded in `scope_gap`; no blocker in the table covers it, and it is not a wrapper question.  The blocker is retired; its text is preserved on `S1-block-residual`.
- **Next action:** Nothing outstanding for the printed narrative: the definition is compiled in source form, every Section 3 existence regime is a proved theorem on its own row (DK-3.1-prop, DK-3.2-prop, DK-3.3-prop), and both `U = cos Theta + J sin Theta` and `U = exp(J Theta)` are proved.  Remaining scope work is the standing one: every `J` declaration is finite-dimensional, and lifting `J`, `J^2 = -(support projection)` and the exponential form to the bounded complex tree requires a `J` to exist there first.

#### Definition 3.2: Acute case

- **Kind:** `definition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Both crossed intersections P ∩ Q-perp and P-perp ∩ Q vanish.
- **Current Lean references:** `TauCeti.IsAcute`, `TauCeti.isAcute_iff_inf_orthogonal_eq_bot`, `TauCeti.DavisKahan.IsUniformlyAcute`, `TauCeti.isAcute_of_projectionGap_lt_one`, `TauCeti.directedProjectionGap_lt_one_of_transverse`, `TauCeti.projectionGap_lt_one_of_isAcute`, `TauCeti.isAcute_iff_projectionGap_lt_one`, `TauCeti.one_le_projectionGap_of_forall_exists_unit_lt`
- **Assessment:** The predicate is broadly used but lacks a numbered source alias.

RESOLVED 2026-08-06.  `TauCeti.DavisKahan.IsAcute` IS the source definition -- the projection gap is strictly below one -- compiled, guarded by the default build, axiom-clean, and consumed by every acute-case theorem in the tree.  The conditional next action ("add a source alias only if the facade benefits") is decided in the negative: a numbered alias would duplicate a two-token definition that call sites already read literally, and the api-design rubric asks for lemmas over aliases when nothing is gained.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 3 is UPHELD.  The row read
"the predicate is the printed definition" while listing only `TauCeti.DavisKahan.IsAcute`, which is
`subspaceGap < 1` -- NOT the printed definition.  The printed definition does exist, as
`TauCeti.IsAcute` (`ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean`), and is now listed
here together with the one implication that is proved.  The status stays `compiled_exact` because
the source artifact this row is about -- Definition 3.2 itself -- IS compiled exactly; what is not
exact is every downstream Section 3 row's hypothesis, and that is recorded in `scope_gap` above so
it is visible from this row.

A stale docstring at `AngleGeometry.lean:202` promised a converse `projectionGap_lt_one_of_isAcute`
"below"; no such declaration exists (verified by `#check` and by grep).  The docstring is corrected
in the same change as this note.

**M19, 2026-08-09 (Claude Opus 5).**  The two predicates are now RELATED IN BOTH DIRECTIONS where that is true, and NAMED HONESTLY.

(1) `projectionGap_lt_one_of_isAcute` is proved, in `FiniteDimensional`.  It is the declaration the
docstring of `isAcute_of_projectionGap_lt_one` promised for months and never delivered; it now
exists under exactly that name.  The engine is `directedProjectionGap_lt_one_of_transverse`: on the
unit sphere of `U`, which is compact, `x |-> ||P_V x||` attains a minimum `m`, transversality makes
`m > 0`, and Pythagoras gives `||P_{Vperp} x|| <= sqrt(1 - m^2) ||x||` with `sqrt(1 - m^2) < 1`.
`isAcute_iff_projectionGap_lt_one` packages the two directions.

(2) The predicate formerly named `TauCeti.DavisKahan.IsAcute` is renamed
`TauCeti.DavisKahan.IsUniformlyAcute` (24 files, 192 occurrences).  Two different predicates were
both called `IsAcute`, and the paper's unqualified name was on the strictly stronger one.  The
paper's name now denotes only the printed Definition 3.2.

(3) `isAcute_iff_inf_orthogonal_eq_bot` states Definition 3.2 in the paper's own words --
`U inf Vperp = bot` and `Uperp inf V = bot` -- so the pointwise predicate can be checked against
the printed sentence.

(4) A PRIOR BRIEF'S CLAIM ABOUT THIS ROW IS FALSE and is recorded so it is not retried.  It is not
the case that every Section 3 and Section 4 result is stated on the gap predicate.  MEASURED
2026-08-09 by enumerating the whole `DavisKahan.All` environment and inspecting the type of every
declaration: 78 declarations are stated on the PRINTED predicate `TauCeti.IsAcute` and 160 on the
gap predicate.  The split is by namespace, because an unqualified `IsAcute` resolves differently in
different namespaces: the finite-dimensional tree (`TauCeti.DavisKahanTheory.*`, including
`directRotation`, `directRotation_sq`, `directRotation_symm` and the whole Section 4 extremal
package) is on the printed predicate, and `TauCeti.DavisKahan.Experimental.*` /
`TauCeti.DavisKahanExt.*` are on the gap predicate.  Since the finite-dimensional tree is where the
printed predicate is used, and the two agree there by (1), the finite-dimensional Section 3/4
results are at the printed hypothesis exactly.

(5) `one_le_projectionGap_of_forall_exists_unit_lt` isolates exactly what fails in infinite dimension, with no dimension hypothesis: if unit vectors of `U` are almost annihilated by `P_V` without any being annihilated exactly, the gap is forced to `1`.  That is the complement of `directedProjectionGap_lt_one_of_transverse`, where compactness turns the infimum into a positive minimum, and it supplies half of the missing counterexample.

**M37, 2026-08-09 (Claude Opus 5).  STALE BLOCKER ENTRY REMOVED.**  The wrapper this blocker asked for is `TauCeti.IsAcute` together with `isAcute_iff_inf_orthogonal_eq_bot`, which states Definition 3.2 in the paper's own words (`U ⊓ Vᗮ = ⊥` and `Uᗮ ⊓ V = ⊥`); both were already listed here and both re-elaborate clean.  The row's single open `next_action` -- a compiled infinite-dimensional pair separating the printed predicate from the quantitative one -- is a counterexample, not a wrapper, and is not what this blocker described.  The blocker is retired; its text is preserved on `S1-block-residual`.
- **Next action:** One item.  Compile a counterexample showing the finite-dimensionality of `projectionGap_lt_one_of_isAcute` is not removable -- two closed subspaces of an infinite-dimensional Hilbert space with both crossed intersections zero and `||P_U - P_V|| = 1`, e.g. `U` and `V` spanned by orthonormal families at principal angles `theta_n` increasing to `pi/2`.  Until that is compiled the infinite-dimensional failure is asserted in prose only (it is classical, and the docstrings say so rather than naming a declaration).  Re-scoping Propositions 3.1, 3.4, 3.5 and Corollary 3.2 onto the printed predicate remains the separate infinite-dimensional design question recorded on those rows; it is NOT a rename, because under the printed definition `|S|` is injective with dense range but not invertible.

#### Proposition 3.1: Acute direct rotation existence and uniqueness

- **Kind:** `proposition`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** In the acute case the direct rotation exists, is unique, and positivity of its diagonal blocks characterizes it.
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation`, `TauCeti.DavisKahan1970.complex_directRotation_unique`, `TauCeti.DavisKahan1970.complex_directRotation_diagonalBlock`, `TauCeti.DavisKahan1970.complex_directRotation_complementaryDiagonalBlock`, `TauCeti.DavisKahan1970.complex_directRotation_reflectionConjugate`, `TauCeti.DavisKahan1970.complex_directRotation_of_diagonalBlocks`, `TauCeti.DavisKahan1970.complex_directRotation_iff_diagonalBlocks`, `TauCeti.DavisKahan1970.real_directRotation`, `TauCeti.DavisKahan1970.real_directRotation_orthogonal`, `TauCeti.DavisKahan1970.real_directRotation_intertwines`, `TauCeti.DavisKahan1970.real_directRotation_maps_subspace`, `TauCeti.DavisKahan1970.real_directRotation_maps_orthogonalComplement`, `TauCeti.DavisKahan1970.real_directRotation_diagonalBlock`, `TauCeti.DavisKahan1970.real_directRotation_complementaryDiagonalBlock`, `TauCeti.DavisKahan1970.real_directRotation_principal_of_sq`, `TauCeti.DavisKahan1970.real_directRotation_of_diagonalBlocks`, `TauCeti.DavisKahan1970.real_directRotation_iff_diagonalBlocks`, `TauCeti.DavisKahan1970.complex_directRotation_reflectionConjugate_of_positiveDiagonalBlocks`, `TauCeti.DavisKahan1970.complex_directRotation_of_positiveDiagonalBlocks`, `TauCeti.DavisKahan1970.complex_directRotation_iff_positiveDiagonalBlocks`, `TauCeti.DavisKahan1970.real_directRotation_of_positiveDiagonalBlocks`, `TauCeti.DavisKahan1970.real_directRotation_iff_positiveDiagonalBlocks`, `TauCeti.DavisKahan.Experimental.eq_directRotationR_iff_diagonalBlocks_pos`, `TauCeti.DavisKahan.Experimental.isPositive_of_complexify`, `TauCeti.DavisKahan.Experimental.isPositive_canonicalAbsoluteValueR`
- **Assessment:** The main acute construction and uniqueness are present; the exact characterization by positivity needs source-level verification.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. Existence and uniqueness in the acute case are compiled and axiom-clean; the positivity characterization that the printed Proposition 3.1 also asserts is neither proved nor wrapped, so the exact source theorem is not represented.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

PARTIALLY DISCHARGED 2026-08-04, and the residue is now exact. The positivity half is no longer unwrapped: both diagonal compressions of the direct rotation are the *positive* Halmos cosine -- `P_U W P_U = |S| P_U` and `P_Uperp W P_Uperp = |S| P_Uperp` -- and both are proved, in the default build, and axiom-clean. Source aliases added.

**What is genuinely still missing is the characterisation direction, and it is not a wrapper.** The printed clause is that positivity of the diagonal blocks *characterises* the direct rotation. The compiled uniqueness theorem `complex_directRotation_unique` assumes `0 <= re <W x, x>` for **all** `x`, i.e. that the whole Hermitian part is nonnegative. That is strictly stronger than nonnegativity of the two diagonal compressions, which constrains the numerical range only on `U` and on `Uperp` separately and says nothing about mixed vectors. So the source characterisation does not follow from what is compiled; it needs the off-diagonal argument that recovers global numerical-range positivity from the two blocks.

**DISCHARGED 2026-08-05. The characterisation direction is proved, and the row is now exact.** `complex_directRotation_iff_diagonalBlocks` states Proposition 3.1's characterisation clause as a biconditional: `W` is the direct rotation **iff** it is a unitary square root of `J_V J_U` that intertwines the two reflections and whose compressions to `U` and to `U-perp` have nonnegative numerical range.  No condition is imposed on mixed vectors, which is exactly what made the previous residue real.

WHAT THE MISSING STEP TURNED OUT TO BE, and it was one line of algebra, not a wrapper.  The printed hypothesis that `W` carries the pair `(U, U-perp)` onto `(V, V-perp)` had been dropped in the earlier reading.  Restoring it closes everything: `W J_U = J_V W` together with `W^2 = J_V J_U` gives two expressions for `J_V`, and cancelling `W` yields `J_U W J_U = W*`.  So the Hermitian part `W + W*` **commutes with `J_U`**, its quadratic form splits over `U (+) U-perp` with no cross term, and two separate sign conditions add up to global numerical-range positivity -- which is what `complex_directRotation_unique` was already waiting for.  Without the intertwining hypothesis the implication is false: on `U = V` the Hermitian unitary `[[0,b],[b*,0]]` squares to `1 = J_V J_U` and has both diagonal blocks zero, hence nonnegative, yet is not the direct rotation `1`.

THE REUSABLE HALF was extracted to `ForTauCeti`: `Submodule.re_inner_apply_self_nonneg_of_reflectionConjugate` (with `inner_diagonalPart_apply_self` and `diagonalPart_eq_self_of_reflectionConjugate`) says that an operator commuting with a reflection has nonnegative numerical range as soon as its two blocks do.  Nothing in it mentions direct rotations.  All new declarations are in the default build and axiom-clean [propext, Classical.choice, Quot.sound].

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 4 is UPHELD, and the status is
LOWERED `compiled_exact` -> `compiled_specialization`.

WHAT WAS OVER-CLAIMED.  Printed Proposition 3.1 has three clauses: in the acute case the direct
rotation (a) exists, (b) is unique, and (c) **is characterized by property (i) alone**.  Clause (c)
says that among unitary `V` with `VP = QV`, positivity of the diagonal blocks already forces
`S_1 = S_0*`; the paper proves it from `C_0^2 S_1 = S_1 C_1^2` by the continuous functional calculus
and density of `Range(C_1)` (transcription L887--898).  Measured 2026-08-09 by elaborating both
compiled characterizations, NEITHER is that clause: `complex_directRotation_iff_diagonalBlocks` and
`complex_directRotation_of_diagonalBlocks` both put `W * W = spectraReflectionProduct U V` --
equation (3.8) -- on the left of the implication, alongside unitarity, the intertwining, and the two
accretivity conditions.  (3.8) is extra information, not (i).  (a) and (b) remain exact.

The row also carries the standing scalar narrowing (`InnerProductSpace C` only) and the Definition
3.2 narrowing recorded on `DK-3.2-def`.

**M33, 2026-08-09 (Claude Opus 5).  THE REAL-SCALAR AXIS IS CLOSED ON THIS ROW.**  Clauses (a) existence and (b) uniqueness are now proved over a REAL Hilbert space of arbitrary dimension as well: `real_directRotation` (`TauCeti.DavisKahan.Experimental.directRotationR`) exists, is orthogonal, intertwines the projections and carries `U` onto `V` and `Uperp` onto `Vperp` (concluded, not assumed); `real_directRotation_principal_of_sq` is uniqueness among orthogonal square roots of the reflection product with nonnegative numerical range; `real_directRotation_of_diagonalBlocks` and `real_directRotation_iff_diagonalBlocks` are the compiled characterisation, in the same shape as the complex ones.

THE STATUS DOES NOT MOVE.  The M18 adjudication above lowered this row for clause (c), which puts equation (3.8) on the left of the implication where the paper puts property (i) alone.  That defect is scalar-independent: the real characterisation carries the SAME extra hypothesis `W * W = J_V J_U`, because it is transported from the complex one.  So this discharge closes the scalar axis and nothing else.

**THE M18 DEFECT IS DISCHARGED, 2026-08-10 (Claude Opus 5, coordinator-verified).  NO COMPILED CHARACTERIZATION NOW PUTS (3.8) ON THE LEFT, OVER EITHER FIELD.**  `spectraDirectRotation_unique_of_diagonalBlocks_pos` assumes only: unitary, `W P_U = P_V W`, and both diagonal blocks POSITIVE.  `W * W = spectraReflectionProduct U V` is DERIVED inside the proof by the paper's own `U^2 X = U(UX) = U(X U^-1) = U P U^-1 - U Ptilde U^-1 = Q - Qtilde`.  The biconditional `eq_spectraDirectRotation_iff_diagonalBlocks_pos` and the real implication `directRotationR_unique_of_diagonalBlocks_pos` came with it.

**THE COORDINATOR'S BRIEF SAID `ACCRETIVE` AND THAT STATEMENT IS FALSE.  RECORDED SO IT IS NOT RE-ATTEMPTED.**  Printed property (i) is `C_0 >= 0`, `C_1 >= 0` -- POSITIVE OPERATORS.  With accretivity (`re <W x, x> >= 0`) instead, the characterization FAILS: on `H = C^2` with `U = V = C.e_0`, the unitary `W = diag(i, 1)` commutes with `P_U` (both sides `diag(i,0)`), has `<W e_0, e_0> = i` with real part 0 and `<W e_1, e_1> = 1`, so BOTH blocks are accretive -- yet `W != 1`, and `1` is the direct rotation when `U = V`.  COORDINATOR-VERIFIED by hand.  Over `R` the analogue is rotation by `pi/3` on `R^4` with `U = V = span(e_0, e_1)`.  BOTH COUNTEREXAMPLES ARE HAND-VERIFIED, NOT FORMALIZED.

**CONSEQUENCE: the new theorem is INCOMPARABLE with the older (3.8)-plus-accretivity one, NOT a strengthening of it.**  Dropping (3.8) forces the block condition to be strengthened at the same time.  Over `C` the strengthening is nearly invisible -- `0 <= <W x, x>` in the order on `C` already forces the imaginary part to vanish, hence self-adjointness of the block -- but over `R` it is explicit, which is why the real statement uses `IsPositive` of the compression.

TWO ROUTE ITEMS FROM THE RECORD WERE UNNECESSARY.  (i) NO RECTANGULAR CFC INTERTWINER IS NEEDED: `C_0` and `C_1` are supported on complementary summands of ONE space, so `T := C_0 + C_1` is a single nonnegative operator, `T^2 B = B T^2` is equivalent to `C_0^2 S_1 = S_1 C_1^2`, and the step is `Commute (T*T) B -> Commute T B` -- a three-line lemma, now `TauCeti.commute_of_commute_mul_self` in a new `ForTauCeti/Analysis/CStarAlgebra/PositiveSquareRootCommute.lean`, proved from Mathlib's `Commute.cfc_nnreal` and `CFC.sqrt_mul_self`, which has both halves and not the composite.  `cfcHom_intertwines` was left untouched -- and it is NOT a `LinearPMap` statement as the brief implied; it is already a rectangular bounded intertwiner.  Only `resolvent_intertwines` and `cayley_intertwines` are `LinearPMap`.  (ii) THE PAPER'S DENSITY ARGUMENT AT STEP 4 IS NOT NEEDED: taking adjoints turns `(S_1 - S_0*) C_1 = 0` into `C_1 (S_1 - S_0*)* = 0` with range in `Uperp`, so plain INJECTIVITY of `C_1` on `Uperp` finishes -- no closure, no dense-range API -- and injectivity is immediate from `U inf Vperp = bot` without using positivity of `C_1` at all.

LATENT IMPORT COLLISION, worth knowing: importing `ForTauCeti.Analysis.InnerProductSpace.AngleGeometry` into `DirectRotationSquare.lean` BREAKS THE DEFAULT BUILD -- it makes `TauCeti.projection` (a `LinearMap`) visible, shadowing `TauCeti.DavisKahan.projection` (a `ContinuousLinearMap`) and producing 9 type errors in `InfiniteDimensional/SpectraBridge/DirectRotationAPI.lean`.

**THE REAL BICONDITIONAL LANDED 2026-08-10 (Claude Opus 5, coordinator-verified).**  `eq_directRotationR_iff_diagonalBlocks_pos`, aliased as `real_directRotation_iff_positiveDiagonalBlocks`, with POSITIVITY of the two compressions -- never accretivity -- and with (3.8) neither assumed nor listed.

**THE COORDINATOR'S ROUTE WAS ONE LEVEL OFF.**  The brief said the converse needs operator positivity descended AT THE COMPRESSION.  It does not: the descent happens one level lower, at the HALMOS COSINE.  `isPositive_of_complexify` gives `(complexify A).IsPositive -> A.IsPositive`, and its ONLY use is `isPositive_canonicalAbsoluteValueR`, which consumes the complex `spectraOperatorAbsoluteValue_nonneg` at `|S|` rather than at the block.  The compression step is then elementary and entirely real: compression of a positive operator is positive, and left-multiplying the compiled block identity by the idempotent turns `P W P = |S| P` into `P W P = P |S| P`.  No angle mathematics was redone.
- **Next action:** Nothing on clause (c): the real BICONDITIONAL landed 2026-08-10 (`real_directRotation_iff_positiveDiagonalBlocks`), so both directions hold over both fields with POSITIVE blocks and without (3.8).  What is left on this row is the standing `IsUniformlyAcute` narrowing, which enters through clause (a) only and is carried on `DK-3.2-def`.

#### Proposition 3.2: Nonacute existence criterion

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** A direct rotation exists exactly when the two crossed intersections have equal dimension; it is then nonunique.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_parameterized_nonuniqueness`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_not_unique`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_not_existsUnique`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.remark3_2_bilateralShift_separates_dimensionHypotheses`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.halmosSourceDefect_coordinateHalfSpace`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.halmosTargetDefect_coordinateHalfSpace`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.halmosSourceDefect_ne_bot_of_not_isAcute`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent_real`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_parameterized_nonuniqueness_real`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_not_unique_real`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_not_existsUnique_real`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.remark3_2_bilateralShift_separates_dimensionHypotheses_real`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.directedGap_asymmetric_coordinateHalfSpace`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.coordinateHalfSpace_le_coordinateHalfSpace`
- **Assessment:** No exact general Hilbert-space declaration was found.

CORRECTED 2026-08-04: this row read `not_represented` / `absent` and listed no declarations, but the nonacute existence criterion is stated and **proved sorry-free** in `DavisKahan/Experimental/Frontier/Section3.lean` (verified by `#print axioms`; neither declaration reaches `sorryAx`). It is `proved_outside_build` because the whole `Frontier` tree sits outside the default targets -- see the `frontier-tree-unguarded` blocker.

**2026-08-05 (second session): both promotion-blocking admissions are out of this row's closure.** `directRotation_minimal` was orphaned -- nothing outside its own file referenced it, and the complex statement is already proved in production as `spectraDirectRotation_minimal`; `SpectraBridge/DirectRotationAPI.lean` imported that module only for `IsAcute` and now takes it from `BoundedOperator/Compat`. `projectionDifference_ideal_intervalExterior`, `ideal_sinTheta` and `ideal_sinTwoTheta` moved into `Experimental/InfiniteDimensional/SinTheta/IdealIntervalExterior.lean`, leaving `SinTheta/General.lean` and `InfiniteDimensional/DoubleAngle.lean` sorry-free. Measured closures: 175/188/199 modules, 24/41/50 Experimental, 0 tactic sorries each. WHAT STILL BLOCKS THE ROW: `check_library_structure` rule 2 forbids a production module importing `Experimental`, so promotion means RELOCATING those closures out of `Experimental/`. That is a design decision, not a mechanical step -- take it deliberately. Rule 3 now reports 49 violations (was 6) precisely because 34 modules became admission-free; the checker is enumerating what ought to move.

**IN THE BUILD 2026-08-06.**  `DavisKahan/Experimental/Frontier/{Core,Section3,Section4}.lean` became admission-free and were promoted to `DavisKahan/Frontier/`, reached from `DavisKahan.All` via `DavisKahan.Frontier.All`.  Nothing was renamed -- the `TauCeti.DavisKahan.Experimental.Frontier` namespaces are untouched, exactly as in the 84-module promotion earlier the same day, because the namespace has never been tied to the directory here.  The census declaration probe now resolves 145/145 against `DavisKahan.All`, up from 143/145, and these two declarations are the two that changed.  `check_library_structure` rule 3 drops from 16 violations to 13.

**ROW WAS STALE IN THREE PLACES; CORRECTED 2026-08-09 (Claude Opus 5).  `compiled_general_infrastructure` -> `compiled_exact`.**

The row's summary line read "No exact general Hilbert-space declaration was found", and it was `blocked_by two-subspace-classification`.  Both were false, and had been since 2026-08-06 when the two declarations were promoted into the default build.  Elaborated here rather than inferred:

* `proposition3_2_exists_iff_crossedDefectsEquivalent (U V : Submodule C H) : (exists T, IsPaperDirectRotation U V T) <-> CrossedDefectsEquivalent U V` -- the printed existence criterion, for arbitrary complete complex Hilbert spaces, with NO finite-dimensionality, NO separability and NO compactness hypothesis.  `CrossedDefectsEquivalent` is a linear isometry equivalence between the two crossed defect subspaces, which is the cardinal-free way to say "equal dimension", so the dimension bookkeeping the old blocker demanded is not needed and was never on the path.
* `proposition3_2_parameterized_nonuniqueness ... : CrossedDefectsEquivalent U V -> exists build, (forall J, IsPaperDirectRotation U V (build J)) and Function.Injective build` -- the printed nonuniqueness, as an injective parameterization by the isometries between the defects, which is stronger than merely exhibiting two.

Both give `#print axioms ... [propext, Classical.choice, Quot.sound]` and both resolve from `DavisKahan.All`.  The two printed sentences of Proposition 3.2 are therefore proved at general Hilbert-space scope, and the only recorded gap left is scalar: complex only.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 7 is UPHELD for this row and the
status is LOWERED `compiled_exact` -> `compiled_specialization`.  The existence criterion (3.5) is
exact.  Two printed pieces are not compiled.  (1) "It is not unique": MEASURED 2026-08-09,
`proposition3_2_parameterized_nonuniqueness` gives an INJECTIVE family
`build : (sourceDefect ~= targetDefect) -> ...` of direct rotations, which yields two distinct ones
only once two distinct isometries are exhibited -- and nothing does that, so the printed
nonuniqueness assertion is not stated.  (2) The Remark's bilateral-shift example (transcription
L936--940): `H = l^2(Z)`, `P H` the sequences with `a_n = 0` for `n < 0`, `Q H` those with `a_n = 0`
for `n <= 0`, where (1.5) holds, the shift satisfies (1.4), and (3.5) FAILS.  It is the source's own
witness that (3.5) is not implied by (1.5), and it is formalized nowhere.

**M33, 2026-08-09 (Claude Opus 5).  MEASURED AND LEFT BLOCKED, for the SAME reason as the excluded Theorem 3.1 / Corollary 3.1.**  The rest of the Section 3 direct-rotation tranche was closed over `R` this session by descent (`DavisKahan/Geometry/Polar/DirectRotationReal.lean`), and this row was attempted with it.  It does not go through, and the obstruction is exactly the one already recorded against Theorem 3.1: the row's content is a CLASSIFICATION up to isometric equivalence, and `CrossedDefectsEquivalent U V` is `Nonempty (U ⊓ Vperp ≃ₗᵢ Uperp ⊓ V)`.  The forward direction of `proposition3_2_exists_iff_crossedDefectsEquivalent`, transported, produces a linear isometry equivalence between the COMPLEXIFIED defect spaces, and recovering a real one from it is a real design step, not a transport.  The reverse direction is no better: a real isometry between the defects complexifies fine, but the direct rotation the complex theorem then produces is an opaque existential and there is nothing forcing it to be conjugation-fixed, so no real `T` is obtained.  This row therefore stays on the blocker with a named, not a generic, obstruction.

**BOTH PRINTED PIECES OF THE M18 ADJUDICATION ARE NOW COMPILED, 2026-08-10 (Claude Opus 5, coordinator-verified).**

(1) THE LITERAL NONUNIQUENESS.  `proposition3_2_not_unique` exhibits two distinct direct rotations and `proposition3_2_not_existsUnique` states the negation of `ExistsUnique`, both from `CrossedDefectsEquivalent U V` and `NOT TauCeti.IsAcute U V`.  Witnesses are `build J` and `build (J.trans (LinearIsometryEquiv.neg C))` through the injective builder.

**NO NARROWING WAS NEEDED, AND THE COORDINATOR'S WARNING THAT ONE MIGHT BE WAS WRONG.**  The brief warned that some formally nonacute pairs might have BOTH crossed defects zero, forcing `J = -J` and a narrowed hypothesis.  That set is EMPTY.  `TauCeti.IsAcute` IS the paper's Definition 3.2: `isAcute_iff_inf_orthogonal_eq_bot` proves `IsAcute U V <-> U inf Vperp = bot AND Uperp inf V = bot` (coordinator elaborated the signature to confirm), so NOT IsAcute already means a crossed defect is nonzero.  The warning conflated `IsAcute` with the strictly stronger quantitative `IsUniformlyAcute` (`||P - Q|| < 1`), which is what `proposition3_1_positivity_characterization` uses; `DavisKahan/BoundedOperator/Compat.lean` records that historical misnaming.  DO NOT REINTRODUCE A DEGENERACY HYPOTHESIS HERE.

ALSO MEASURED: `proposition3_2_parameterized_nonuniqueness` is weaker than its name suggests -- its ground `proposition3_2_parameterization_completed` binds (3.5) as `_hdefect` and NEVER USES IT, so that theorem is vacuous exactly when the defects are inequivalent.  That is why `proposition3_2_not_unique` genuinely needs the hypothesis.  (Underscore binder, again.)

(2) THE REMARK'S BILATERAL SHIFT.  New module `DavisKahan/Frontier/Section3BilateralShift.lean`, wired into `Frontier/All.lean` (build job count moved 9578 -> 9579, confirming it is in the closure).  `remark3_2_bilateralShift_separates_dimensionHypotheses` packages the whole separation: the shift is unitary and intertwines the projectors (1.4); both dimension equalities of (1.5) hold; and (3.5) FAILS because the source crossed defect is `span {b 0}` while the target is `bot`.  The paper's own convention is reproduced exactly (transcription L913-915): `P H = {a_n = 0 for n < 0}`, `Q H = {a_n = 0 for n <= 0}`, shift `b n -> b (n+1)`.  The SOURCE defect is the nonzero one, matching the printed `P Qtilde` description; the target is zero, matching `Ptilde Q = 0`.  `l^2(Z)` is presented as any complex Hilbert space carrying a `HilbertBasis Z C H` -- a presentation choice, not a hypothesis change.

THIS REMARK IS LOAD-BEARING BEYOND THIS ROW: it is the canonical demonstration that equality of two infinite ambient dimensions says nothing about equality of crossed defect dimensions, and the same standing assumption (3.5) is what the Theorem 8.2 infinite-dimensional counterexample on `DK-8.2-thm` violates.

**STATUS DELIBERATELY HELD AT `compiled_specialization`.**  The subagent recommended `compiled_exact`.  Declined: the census defines `compiled_exact` as `an exact source-facing theorem or construction is compiled on the base` and `compiled_specialization` as `a useful compiled specialization exists, but not the full source scope`.  Standing assumption 1 of the transcription puts REAL Hilbert spaces inside the source scope, and every declaration on this row is `InnerProductSpace C`.  So the printed-content axis is closed and the SCALAR axis is not.  (`DK-8.1-thm` carries `compiled_exact` with a real gap; the completion handoff names that row as its example of a status that overstates, so it is the anomaly, not the precedent.)

**THE RECORDED M33 OBSTRUCTION IS ROUTE-SPECIFIC AND SHOULD NOT BE READ AS BLOCKING THE SCALAR AXIS.**  It refutes DESCENT FROM THE COMPLEX THEOREM.  Static measurement 2026-08-10 of the NATIVE route, which was never measured: `Section3Nonacute.lean` (1077 lines) contains ZERO `Complex.`, ZERO `spectrum C` and ZERO `ComplexOrder`, and names ZERO declarations from `DirectRotationSquare.lean`, the one genuinely complex-heavy module in the polar directory (38 `Complex.`, 15 `spectrum C`).  Its single dependency on `Section3Elementary.lean` is `re_inner_projection_compression`, already written in `RCLike.re`.  Its only functional-calculus use is `CFC.sqrt` on a positive operator in one private lemma, and 069c246e now supplies that over `R` at unrestricted dimension.  CAVEAT: this is a static token/name measurement, NOT a compile.

**THE SCALAR AXIS IS CLOSED, 2026-08-10, BY THE NATIVE ROUTE.**  Six modules went `RCLike`-generic and EVERY ONE COMPILED ON THE FIRST TRY after pure scalar substitution -- zero tactic changes, zero name repairs, not one `Complex.*` name replaced: `Geometry/Polar/{OperatorAbsoluteValue, PolarIsometryFinal, DirectRotation, PolarIntertwining, Section3Nonacute}.lean`, plus `re_inner_projection_compression` in a nested section of `Section3Elementary.lean` and the whole of `Frontier/Section3BilateralShift.lean`.  The only mechanical work was 41 `omit ... in` lines keeping the new instance binders off declarations that do not use them.

**THE RECORDED M33 OBSTRUCTION IS NOW MOOT FOR THIS ROW, AND WAS NEVER WRONG.**  It refutes DESCENT from the complex theorem.  The native route was taken instead, and the census's own 2026-08-10 static measurement of that route was correct in every particular -- including that `Section3Nonacute.lean` needs NOTHING from `DirectRotationSquare.lean`, now proved by the compile itself: a `K`-generic declaration cannot reference a `C`-only constant without forcing `K = C`.

CORRECTION TO THE COORDINATOR'S OWN FRAMING, recorded because it nearly caused duplicated work: the brief claimed the native route `appears never to have been measured`.  FALSE.  `DavisKahan/Experimental/InfiniteDimensional/DirectRotation.lean` (1215 lines, 44 declarations) is an already-`RCLike`-generic ACUTE direct-rotation development carrying verbatim the same variable block, and `Geometry/Polar/DirectRotationReal.lean` already delivers the real acute direct rotation and every clause of Propositions 3.1/3.3 and Corollary 3.2 over `R` by complexification descent.  What had never been done was the NONACUTE case, which is the genuinely new work here.

**THE BILATERAL-SHIFT PAIR IS NOW A QUANTITATIVE SEPARATOR, 2026-08-10.**  `directedGap_asymmetric_coordinateHalfSpace` compiles `directedGap (P H) (Q H) = 1`, `directedGap (Q H) (P H) = 0`, and `subspaceGap (Q H) (P H) != directedGap (Q H) (P H)`.  So the pair does not merely fail (3.5) qualitatively -- it exhibits the maximal possible asymmetry between the two directed gaps, and it is the compiled falsifier for any claimed (3.5)-free gap symmetry.

**CAUTION ON USING IT AS A FALSIFIER, learned 2026-08-10.**  The coordinator instructed a subagent that any correct (3.5) theorem `must fail on that pair`.  THAT TEST IS ORDER-DEPENDENT AND GIVES A FALSE NEGATIVE IN ONE ORDER.  Read at `(P H, Q H)` the conclusion `subspaceGap = directedGap` HAPPENS TO BE TRUE -- both sides are 1, because the defect sits on the side that already realizes the max.  The honest refutation is at the SWAPPED pair `(Q H, P H)`, where it would assert `1 = 0`.  `Q H <= P H` (the cut at 1 has more vanishing constraints), which is why the reverse directed gap is exactly 0.  Always state which order you are testing.
- **Next action:** Nothing outstanding.

#### Proposition 3.3: Principal square-root characterization

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Every direct rotation is a principal square root of the product of the two reflections; conversely a suitable principal square root is a direct rotation.
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation_sq`, `TauCeti.DavisKahan1970.complex_directRotation_hermitianPart`, `TauCeti.DavisKahan1970.complex_directRotation_principal_of_sq`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_3_principalSquareRoot_forward`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_3_principalSquareRoot_converse`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_3_principalSquareRoot_iff`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_3_principalSquareRoot_forward_of_nonneg_blocks`, `TauCeti.DavisKahan1970.real_directRotation_sq`, `TauCeti.DavisKahan1970.real_directRotation_hermitianPart`, `TauCeti.DavisKahan1970.real_directRotation_principal_of_sq`
- **Assessment:** The square identity and acute spectral branch exist; the source converse with the crossed-intersection mapping condition is not exposed.

STATUS CORRECTED 2026-08-04 (second time): `partial_or_wrapper_missing` -> `compiled_specialization`, and **the previous note and next_action were stale**. They said "the source converse ... is not exposed" and asked to "add the converse". The converse was already proved, as `spectraDirectRotation_unique_of_sq` (`DavisKahan/Geometry/Polar/DirectRotationSquare.lean`), and it resolves against `DavisKahan.All` and is axiom-clean. What was missing was a source-facing alias, now added.

**Both directions are now cited, for the acute case.** Forward: the word "principal" is carried by `complex_directRotation_hermitianPart`, `W + W* = 2|S|`, so the Hermitian part of `W` is positive and `W`'s spectrum misses the closed left half-plane. Converse: `complex_directRotation_principal_of_sq` -- any unitary `W` with `W*W = J_V J_U` and `0 <= re <W x, x>` for all `x` **is** the direct rotation. In the acute case that is *stronger* than the printed statement: the crossed-intersection mapping condition the source imposes is not needed, because acuteness already forces it.

**What keeps this a specialization rather than `compiled_exact`:** the printed proposition says *every* direct rotation, which includes the nonacute pairs of DK-3.2-prop, where direct rotations are non-unique and the principal branch is exactly what becomes ambiguous (`neg_one_not_mem_spectrum_spectraReflectionProduct`, the lemma the half-phase calculus rests on, needs acuteness). The nonacute half is the remaining scope, not a missing wrapper.

The same 2026-08-04 pass proved the infinite-dimensional analogues of both halves over a general `RCLike` field in `Experimental/InfiniteDimensional/DirectRotation.lean` (`directRotation_sq`, `directRotation_add_adjoint`, `nonneg_directRotation_add_adjoint`, `isUnit_directRotation_add_adjoint`); they are not listed here because that tree is outside the default build.

STATUS CORRECTED 2026-08-06 (third time): `compiled_specialization` -> `compiled_exact`.  **The recorded remaining scope was wrong in both halves.**  The note above said the converse was acute-only and that the nonacute case was open; in fact `proposition3_3_principalSquareRoot_converse` never had an acuteness hypothesis -- it takes an arbitrary principal unitary square root with the crossed-intersection mapping property and returns `IsPaperDirectRotation`, for any pair.  What was genuinely missing was the *forward* direction in that generality: the two compiled forward statements (`complex_directRotation_sq`, `complex_directRotation_hermitianPart`) speak only about the canonical acute `W`, not about an arbitrary direct rotation.

That gap is now closed by `proposition3_3_principalSquareRoot_forward`, axiom-clean and in the default build (`DavisKahan.All` imports `DavisKahan.Frontier.All`).  Every direct rotation whose diagonal `U`-compressions are self-adjoint squares to `J_V J_U`, has spectrum in the closed right half-plane, **and** carries `U ∩ Vᗮ` onto `Uᗮ ∩ V`.  The third conclusion is the point of interest: the source imposes the crossed-intersection mapping condition as a hypothesis, and in the forward direction it is a *theorem*.  Both crossed intersections lie in the `-1` eigenspace of the reflection product, `T` and `star T` commute with that operator because `T * T` is it, and the intertwining moves `U` to `V`; those three facts pin the image down.  `proposition3_3_principalSquareRoot_iff` packages the two directions.

The same pass removed the seventy-five-line duplication this created: the `T * T = J_V J_U` argument was inlined inside `proposition3_1_positivity_characterization` and is now the shared `sq_eq_spectraReflectionProduct` in a `BlockCalculus` section, together with `eq_sum_blocks`, `star_blocks_eq` and `add_star_eq_two_diagonal`.

The self-adjointness hypotheses on the two diagonal compressions are *not* a specialization of the source: they are the same two Proposition 3.1 needs, and they are needed because this repository's `IsPaperDirectRotation` records the compressions only through their numerical range, which is strictly weaker than the printed "positive diagonal blocks".  The canonical direct rotation satisfies them, its diagonal blocks being the positive Halmos cosine.

**The self-adjointness hypotheses are gone in the printed form.**  `proposition3_3_principalSquareRoot_forward_of_nonneg_blocks` states the forward direction with the diagonal compressions *positive as operators*, which is what the source prints, and needs no side hypothesis: a positive operator is self-adjoint and has nonnegative numerical range, so both of the weaker conditions this repository's `IsPaperDirectRotation` records come for free.  It also returns `IsPaperDirectRotation` itself, so the printed hypotheses alone give the printed conclusion.

**M33, 2026-08-09 (Claude Opus 5).  THE REAL-SCALAR AXIS IS CLOSED ON THIS ROW.**  Both directions now hold over a REAL Hilbert space of arbitrary dimension.  Forward: `real_directRotation_sq` is `W^2 = J_V J_U` and `real_directRotation_hermitianPart` is `W + W^T = 2 |S|_R`, which is the word 'principal' -- the symmetric part is nonnegative.  Converse: `real_directRotation_principal_of_sq` says an orthogonal `W` with `W^2 = J_V J_U` and nonnegative numerical range IS the direct rotation.  Both are transported through the conjugation-fixedness of the complexified polar factor; see `DavisKahan/Geometry/Polar/DirectRotationReal.lean`.
- **Next action:** None.  Both directions are compiled in full generality, the printed-hypothesis form of the forward direction needs no side conditions, and the census row is exact.

#### Proposition 3.4: Square as a direct rotation

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** When the cosine block squared is at least one half, U squared is the direct rotation from the reflected subspace to the target subspace.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_4_source`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_4_source_eq_directRotation`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.crossedDefect_image_of_unitary_sq`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.norm_projection_apply_le_of_forall_mem_source`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.re_inner_halmosCosineSq_sub_half_nonneg_of_source`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.re_inner_halmosCosineSq_self`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.isSelfAdjoint_source_block_spectraDirectRotation`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.isSelfAdjoint_complement_block_spectraDirectRotation`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.nonneg_add_star_of_re_inner_nonneg`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.reflectionOperator_mul_projection_self`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.projection_mul_reflectionOperator_self`, `TauCeti.DavisKahanTheory.directRotation_sq`, `TauCeti.DavisKahan1970.complex_directRotation_sq`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_4_square_is_reflected_directRotation`
- **Assessment:** Square identities exist; exact source mapping between Q-minus and Q needs verification.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The square-is-a-direct-rotation content is compiled and axiom-clean; an exact source wrapper is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

ROW WAS STALE; RESOLVED 2026-08-06.  The "absent" exact source wrapper exists and is guarded: `proposition3_4_square_is_reflected_directRotation` (`DavisKahan/Frontier/Section3.lean`, reached from `DavisKahan.All`, axiom-clean): the square of the direct rotation is the direct rotation between the reflected pair `(U, reflectedSubspace V U)` -- the direct-rotation repair this row's next action was waiting on landed with the Frontier promotion, and the wrapper landed with it.  The statement is exact in the FAITHFUL MINIMAL CORRECTION recorded in its docstring, which also records why each correction is forced: the half-angle threshold must be on the cosine SQUARE (`re ⟪x, halmosCosineSq x⟫ ≥ ‖x‖²/2`), not on `|S|` as a literal transcription would have it, and acuteness of the reflected pair is a genuinely independent hypothesis (boundary cosine-square `1/2` satisfies the bound while the reflected pair has gap one).  The two justifying counterexamples are prose in the docstring, not compiled Lean terms; that is hypothesis-shape hardening, not Davis--Kahan content, and is recorded below as optional.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 5 is UPHELD and the status is
LOWERED `compiled_exact` -> `compiled_specialization`.  The `next_action` read "Nothing that is proof
debt"; what is compiled is an existential over an unnamed pair, under a symmetrized form bound and an
extra acuteness hypothesis, rather than the printed statement about `(Q_- H, Q H)` under
`C_0^2 >= 1/2`.  See `scope_gap` for the three measured differences.  Nothing recorded here was wrong
about the mathematics -- the compiled theorem is true and axiom-clean; the row's judgement against the
printed statement was too strong.

**M37, 2026-08-09 (Claude Opus 5).  PRINTED PROPOSITION 3.4 IS COMPILED.  STATUS RAISED `compiled_specialization` -> `compiled_exact`, AND THE BLOCKER IS DISCHARGED BY PROOF.**  This was the only one of the six `exact-source-wrappers` rows with real work on it, and the work was not mechanical: each of the three narrowings recorded in `scope_gap` on 2026-08-09 needed mathematics, not a restatement.

`proposition3_4_source` (`DavisKahan/Frontier/Section3.lean`) is the printed sentence -- if `C₀² ≥ ½` then `U²` is the direct rotation of `Q₋ℋ` to `Qℋ` -- as `IsPaperDirectRotation (reflectedSubspace U V) V (W * W)`, with `W` the direct rotation of the pair.  The paper's own proof verifies exactly clauses (i) and (ii) of Definition 3.1 plus the intertwining `U²Q₋ = QU²`, which is what that predicate records.

(1) THE PAIR WAS THE WRONG ONE, AND BOTH ARE TRUE.  `reflectedSubspace A B` is the mirror of `B` in `A`, so the paper's `Q₋ = XQX` is `reflectedSubspace U V`.  The compiled theorem exhibited `(U, reflectedSubspace V U)` -- the source and its own mirror in the target.  Each statement says `W²` is the direct rotation from some subspace onto its `W²`-image, and they are different subspaces; only the second is printed.

(2) THE HYPOTHESIS IS ON `Pℋ` ALONE, AND EXTENDING IT IS A THEOREM.  By (3.7), `C₀² = E₀⋆QE₀`, so the printed `C₀² ≥ ½` is `∀ x ∈ U, ‖x‖²/2 ≤ ‖P_V x‖²`.  What the accretivity of `R_V R_U` needs is the same bound for `cos²Θ` on all of ℋ, i.e. also `C₁² ≥ ½` on `P̃ℋ`.  THAT IMPLICATION IS FALSE FOR AN ARBITRARY PAIR: take `U ⊆ V` with `dim V > dim U`, where `C₀² = 1` while `C₁²` has `0` in its numerical range.  It holds here because the acute case supplies a unitary intertwiner whose two crossed blocks are adjoint -- Definition 3.1(ii), `S₁ = S₀⋆` -- so the two directed gaps `‖P_{Vᗮ}P_U‖` and `‖P_V P_{Uᗮ}‖` are EQUAL.  `norm_projection_apply_le_of_forall_mem_source` is that acute directed-gap transfer, proved through the `star`-block calculus of the canonical direct rotation.  `Submodule.projectionGap_eq_max_directedProjectionGap` does not give it: it only says the symmetric gap is the larger of the two.

(3) THE EXTRA ACUTENESS HYPOTHESIS IS GONE, AND THE ARGUMENT THAT IT WAS NECESSARY WAS ABOUT THE ROUTE, NOT THE CLAIM.  The docstring of `proposition3_4_square_is_reflected_directRotation` argues that `IsUniformlyAcute U (reflectedSubspace V U)` is 'genuinely not derivable' -- correctly, since at the boundary `C₀² = ½` the reflected pair has gap one.  But that hypothesis is needed only to index `spectraDirectRotation` for the reflected pair.  Routing through Proposition 3.3's NONACUTE converse removes it: the crossed-intersection mapping condition that the converse takes as a hypothesis is free for every unitary square root of the reflection product that intertwines the two projections.  That is `crossedDefect_image_of_unitary_sq`, factored out of `proposition3_3_principalSquareRoot_forward` -- which had contained it inline and now cites it, so the twenty-five lines exist once.  Acuteness of the ORIGINAL pair is retained: `spectraDirectRotation U V` is indexed by it, and (2) needs the intertwiner it provides.

`proposition3_4_source_eq_directRotation` supplies the printed definite article: with the reflected pair acute as well, `W²` is the canonical direct rotation of `(Q₋ℋ, Qℋ)` on the nose, by Proposition 3.1 uniqueness.  Without it, `proposition3_4_source` still holds and Proposition 3.2 says the direct rotation need not be unique.

`proposition3_4_square_is_reflected_directRotation` is KEPT, not replaced: it is true, axiom-clean, and it is the statement about the other reflected pair.  All eleven new declarations are axiom-clean `[propext, Classical.choice, Quot.sound]`.
- **Next action:** Nothing outstanding for printed Proposition 3.4.  Optional hardening, unchanged and still optional: compile the two prose counterexamples in the docstring of `proposition3_4_square_is_reflected_directRotation`, which pin the corrected hypothesis shape of THAT statement (they are about its symmetrized form bound and its reflected-pair acuteness, neither of which printed Proposition 3.4 now carries).

#### Theorem 3.1: Classification of pairs of subspaces

- **Kind:** `theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** Spectral multiplicity functions of the two angle operators classify dimension-compatible subspace pairs up to isometric equivalence.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.SameHalmosCosineBlockInvariant`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.exists_cosineBlockEquiv_of_pairEquiv`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_of_cosineBlockEquiv`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.genericTransport`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_of_summandEquivs`, `TauCeti.DavisKahan.Experimental.Frontier.SameSpectralMultiplicity`, `TauCeti.DavisKahan.Experimental.Frontier.sameSpectralMultiplicity_iff_unitarilyEquivalent`, `TauCeti.DavisKahan.Experimental.Frontier.unitarilyEquivalent_of_sameSpectralMultiplicity`, `TauCeti.DavisKahan.Experimental.Frontier.sameSpectralMultiplicity_of_unitarilyEquivalent`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.theorem3_1_spectralMultiplicity_classification`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.twoProjection_operator_classification`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.starProjection_targetSubspace_apply`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.compress_source_eq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.compress_sourceOrthogonal_eq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.halmosCommonPart_eq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.halmosSourceDefect_eq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.halmosTargetDefect_eq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.halmosExteriorPart_eq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.crossedDefectEquiv`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.nonempty_halmosSourceDefect_equiv_targetDefect`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.trivialHalmosAngleDatum`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.trivial_halmosCommonPart_eq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.trivial_halmosExteriorPart_eq`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.theorem3_1_realization`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.theorem3_1_realization_zeroAngle_unconstrained`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.twoProjection_operator_classification_real`
- **Assessment:** **PROVED 2026-08-04, in the paper's own invariant, both directions, admission-free.**

`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant` (`DavisKahan/Geometry/Halmos/GenericReconstruction.lean`): two ordered pairs of subspaces of two complex Hilbert spaces are unitarily equivalent as pairs **iff** their four elementary Halmos summands are linearly isometric and their angle operators `cos^2 Theta` -- the compression of `P_V` to `U /\ generic` -- are unitarily equivalent. No compactness, no finite dimension, no separability, no direct-integral presentation. `#print axioms` gives exactly [propext, Classical.choice, Quot.sound], and the module is reachable from `DavisKahan.All`, so CI guards it.

Brick (2) (`pairOfSubspacesUnitaryEquivalent_of_summandEquivs`, Assembly.lean) glues the four elementary summand isometries and a pair-compatible generic-part isometry into a global unitary. Brick (1) (GenericReconstruction.lean) supplies the generic-part isometry from the cosine block alone, and the extension is *forced*: `B = Phi |B|` has `Phi : M ~= N` unitary, so the only candidate on the U-perp half is `W' := Phi_2 W Phi_1^-1`, and each remaining block is pinned by `A` -- `|B|` is the unique nonnegative square root of `A - A^2`, `D` is pinned by `D B = B (1-A)` plus the dense range of `B`, and `B'` is the adjoint of `B`.

**WHAT IS AND IS NOT LEFT, stated precisely.** The paper phrases Theorem 3.1 with *spectral multiplicity functions* of the angle operators; the theorem above uses the *unitary-equivalence class* of the same operator. The two phrasings differ by Hahn--Hellinger -- 'two self-adjoint operators are unitarily equivalent iff their multiplicity data agree' -- which is a translation of the invariant, not a step in Davis and Kahan's argument. So what remains for the literal printed sentence is a multiplicity theory Mathlib does not have; the classification content of the theorem is done.

**Why the U-side invariant, and not the frontier's.** `SameHalmosOperatorInvariant.generic` records `genericHalmosCosineSq`, the compression of `P_U P_V P_U + P_Uperp P_Vperp P_Uperp`. On the generic part that operator is the cosine block on the U-half and `1 - D` on the U-perp half, i.e. `A (+) A` (`coe_genericHalmosCosineSq_of_mem_left` proves the M half). Recovering `A` from `A (+) A` is multiplicity-halving -- Hahn--Hellinger again, and this time gratuitously, since the pair is determined by `A` alone by elementary means. Davis and Kahan state Theorem 3.1 for the angle operator on the U-side, so recording the cosine block is the paper-faithful reading; the symmetrized operator was a repository choice that doubled the multiplicity.

HISTORY. The pre-existing frontier statement `TauCeti.DavisKahan.Experimental.Frontier.Section3.theorem3_1_spectralMultiplicity_classification` remains `sorry`, and is **vacuous** besides: its premise `TauCeti.DavisKahan.Experimental.Frontier.SameSpectralMultiplicity` is `noncomputable def ... : Prop := by sorry` (`DavisKahan/Experimental/Frontier/Core.lean`), and a Prop-valued definition with a `sorry` body asserts nothing. Its sibling `twoProjection_operator_classification` (Frontier/Section3) is now PROVED: on 2026-08-04 `SameHalmosOperatorInvariant.generic` was re-pointed from `genericHalmosCosineSq` to `genericCosineBlock` -- the angle operator on the U-side, which is what the paper states Theorem 3.1 for -- and the theorem is grounded by `:=` on `pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`. It is admission-free. Only three declarations referenced that invariant, all in Frontier/Section3, so the change was contained.

NOTE ON EVIDENCE. `twoProjection_operator_classification` is deliberately NOT listed in this row's `lean_declarations`: it lives under `DavisKahan.Experimental.Frontier`, which no default target builds, so listing it would drop the row to `partially_in_build`. The census checker catches this. The row's evidence is the `Geometry/Halmos` declarations, which CI guards; the frontier statement is grounded on them by `:=`.

**PROVED 2026-08-06, in the paper's multiplicity phrasing, admission-free.**  The remaining gap this row recorded -- "what remains for the literal printed sentence is a multiplicity theory Mathlib does not have" -- is closed.  `Frontier.SameSpectralMultiplicity` is no longer a `sorry`ed `def`; `Frontier.sameSpectralMultiplicity_iff_unitarilyEquivalent` and `Frontier.Section3.theorem3_1_spectralMultiplicity_classification` are proved, and `#print axioms` gives exactly [propext, Classical.choice, Quot.sound] on all of them.

THE DEFINITION.  Two operators have the same spectral multiplicity when each is unitarily equivalent to the multiplication model of a `TauCeti.MultiplicityDatum` -- a finite measure on C plus an ANTITONE sequence of measurable level sets -- and the data agree: base measures in the same measure class (`TauCeti.MeasureEquiv`, proved an `Equivalence` at its point of definition, with `measureClassSetoid` alongside), level sets equal up to null sets.  The cardinal-valued multiplicity function is encoded by its super-level sets, so every hypothesis is a plain `MeasurableSet` rather than measurability of an N-infinity-valued function.

WHAT WAS BUILT, all in ForTauCeti and all admission-free: `MeasureClass.lean` (the measure-class relation), `LpComp.lean` (relabelling unitaries and the intertwining law), `LpRestrict.lean` (extension by zero, and `L^2` of a measure as the Hilbert sum over a countable measurable partition), `LpSliceSum.lean` (a countable family of measures assembled into one, which turns a direct sum of multiplication models into a single one), `MultiplicityLevels.lean` (dominating measure, rank, level sets, and the normal form), `OperatorUnitaryEquiv.lean`, `HilbertSumIntertwine.lean`, `BorelCalculus/SeparableCyclic.lean` and `BorelCalculus/MultiplicityModel.lean` (`exists_hasMultiplicityModel`, the existence half of Hahn--Hellinger).  See `dev/section3-multiplicity-plan-2026-08-06.md` section 7.

SEPARABILITY, AND WHY IT IS NOT A WEAKENING.  The multiplicity phrasing carries `[TopologicalSpace.SeparableSpace H1]`.  (1) It is one of the paper's STANDING ASSUMPTIONS -- verified 2026-08-06 against the public source surrogate rather than inferred.  `prose/distilled_literature/DavisKahan1970_part_III.tex`, "Standing assumptions from the transcription", anchored to the Introduction, Section 1 and Section 2, records "H is a separable Hilbert space, real or complex, with finite dimensionality only a special case"; it therefore governs Section 3.  The same list records that for noncompact operators the source itself expects singular-value lists to be replaced by SPECTRAL MULTIPLICITY LANGUAGE -- the phrasing proved here.  (This corrects the first justification offered for the hypothesis, which cited only the Section 6 rank hypothesis, where separability is used incidentally to force the trial coordinate space to be finite-dimensional; that is a consequence of the convention, not a statement of it.)  (2) Nothing already proved is weakened: `pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, this row's evidence and the grounding of the frontier node, is untouched -- arbitrary complex Hilbert spaces, no compactness, no finite dimension, no separability.  (3) It is confined to one direction and one space: `unitarilyEquivalent_of_sameSpectralMultiplicity` is separability-free, and `H2` needs nothing because `B` inherits `A`'s datum along the given unitary.  It is needed for exactly one reason: producing a model needs a COUNTABLE cyclic decomposition, because `rank S x n` counts earlier indices and so the index type must be linearly ordered.

WHY NOT THE CARDINAL-INDEXED (NON-SEPARABLE) FORM.  The uniform-multiplicity normal form over an arbitrary index type needs NON-sigma-finite base measures -- `H = sum over t in [0,1] of L^2(delta_t)` has uniform multiplicity one with counting measure on [0,1] as base -- and every Radon-Nikodym tool available, in Mathlib and in `ForTauCeti/MeasureTheory/RadonNikodymL2.lean`, is sigma-finite.  That form is not merely harder here; it is not expressible with the measure theory on hand.

WHAT IS NOT CLAIMED.  `SameSpectralMultiplicity` is an EXISTENTIAL OVER PRESENTATIONS.  Nothing proved says the datum of an operator is unique, so this does NOT inhabit `SpectralMultiplicityFoundation`, whose `multiplicity` field is a function and therefore needs uniqueness as well as existence plus a canonical `Datum` (the quotient by `measureClassSetoid`).  Uniqueness of the multiplicity decomposition remains an explicitly recorded open obligation.  What is proved is the biconditional, which is what the paper's sentence asserts.

THE ANGLE OPERATOR IS `genericCosineBlock`.  The frontier statement of Theorem 3.1 used to compare the symmetrized `genericHalmosCosineSq`, which on the generic part is `A (+) A`; recovering `A` from it is multiplicity-halving.  It now uses the U-side cosine block, matching the 2026-08-04 decision behind `SameHalmosOperatorInvariant` and the 2026-08-06 correction of Corollary 3.1.  Do not restore the symmetrized reading.

NOW GUARDED BY CI.  The multiplicity statements were briefly unguarded: they lived under `DavisKahan.Experimental.Frontier`, which no default target builds, so they could not be listed here without dropping the row to `partially_in_build`.  On 2026-08-06 `Frontier/{Core,Section3,Section4}.lean` were promoted to `DavisKahan/Frontier/`, reached from `DavisKahan.All`; nothing was renamed, exactly as in the 84-module promotion earlier the same day.  The declaration probe resolves 145/145 against `DavisKahan.All`, so both the operator-level and the multiplicity-level statements are now on this row's evidence path and `lake build` guards them.  The frontier gate agrees: 68/80 nodes and 27/32 paper results recursively grounded, up from 65/80 and 26/32, with every remaining ungrounded node in Section 9.

The ForTauCeti stack that proves them is in the default build but is not reachable from `DavisKahan.All`, so it is still not listed; its guard is `lake build` over the `ForTauCeti` glob.

RESOLVED 2026-08-06.  `DavisKahan/Experimental/Frontier/**` holds the Section 3 classification spine, the infinite-dimensional Section 4 propositions and the Section 9 analytic model -- 80 manifest declarations, 19 of them `sorry` -- and **no module in the repository imported any of it**. `lake build` missed it, `lake build DavisKahan.Experimental` missed it, and so did `Challenge` and `FinishTanTwoTheta`. It compiled only when a module was named explicitly on the command line. This is the same defect the `RoadmapBridge` block in `lakefile.toml` records for the suggested-signature files, and it went unnoticed for longer because the frontier checker elaborates the tree through its own probe file rather than through a build target, so the status document kept reporting '80 declarations resolving' from a tree nothing built.  `Frontier/{Core,Section3,Section4}.lean` became admission-free and were promoted to `DavisKahan/Frontier/`, reached from `DavisKahan.All`; the declaration probe went from 143/145 to 151/151.  This blocker entry is removed because no row is blocked by it any more.

UNIQUENESS PROVED 2026-08-06, BOTH HALVES; THE DATUM IS A COMPLETE INVARIANT CANONICALLY, NOT ONLY EXISTENTIALLY.  The open obligation recorded above -- "Nothing proved says the datum of an operator is unique" -- is discharged.  `TauCeti.BorelCalculus.operatorUnitaryEquiv_iff_measureEquiv_and_level` (`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/MultiplicityLevelUniqueness.lean`): two multiplicity data present unitarily equivalent operators IFF their base measures are in the same measure class AND every level set agrees up to a base-null set.  The forward direction is Hahn--Hellinger uniqueness: the measure-class half is `measureEquiv_base_of_operatorUnitaryEquiv` (maximal vectors and the scalar spectral measure of a multiplication operator), and the level-set half is `base_level_symmDiff_eq_zero_of_operatorUnitaryEquiv`, proved by comparing the generator-count invariant `SpectralGeneratedLE` -- the range of the spectral projection of a Borel set lies in the closed Borel-calculus span of m vectors -- which transfers along unitaries by naturality of the bounded Borel calculus (no monotone-class argument: the calculus is defined by polarised diagonal integrals, which transport) and is computed on the model by counting slices.  The dimension count (k generators cannot cover k+1 slices) is done measurably: `TauCeti.exists_measurable_unit_nullVector` selects, with no continuity in the spectral parameter, a unit kernel vector for a measurable family of strictly wide matrices, via the resolvent limit t(B+t)^-1 -> proj ker B of det-adjugate rational functions.  All axiom-clean [propext, Classical.choice, Quot.sound]; guarded by `lake build` over the ForTauCeti glob.  Inhabiting `SpectralMultiplicityFoundation` (a canonical `Datum` as a quotient by `measureClassSetoid` plus a function-valued multiplicity field) is now unobstructed but is repository bookkeeping beyond the paper's sentence, and remains parked with the other promotion work.

**STATUS AND BLOCKER TRUED UP 2026-08-09 (Claude Opus 5).  `compiled_general_infrastructure` -> `compiled_exact`; `two-subspace-classification` removed.**

The row's own notes had already recorded that the printed multiplicity phrasing and the uniqueness of the datum are proved, but the status still described a missing source-numbered wrapper and the blocker still described the multiplicity phrasing as the obstacle.  Both are stale.  Elaborated here:

`theorem3_1_spectralMultiplicity_classification (U1 V1 : Submodule C H1) (U2 V2 : Submodule C H2) [SeparableSpace H1] : PairOfSubspacesUnitaryEquivalent U1 V1 U2 V2 <-> SameHalmosTrivialDimensions U1 V1 U2 V2 and SameSpectralMultiplicity (genericCosineBlock U1 V1) (genericCosineBlock U2 V2)`, axiom-clean and resolving from `DavisKahan.All`; and its engine `sameSpectralMultiplicity_iff_unitarilyEquivalent`, likewise.  That is the paper's sentence: the spectral multiplicity data of the angle operators classify the pairs.  The separability hypothesis is one of the transcription's standing assumptions, not an added restriction, and it is confined to one direction and one space.

The blocker `two-subspace-classification` is deleted from the census.  Its three recorded residues are all resolved: the Halmos canonical form (resolved 2026-08-04), the multiplicity phrasing (resolved 2026-08-06, and uniqueness with it), and the "cardinal-valued dimension bookkeeping for the infinite-dimensional existence statement", which turned out not to be needed at all -- Proposition 3.2's existence criterion is stated through a linear isometry equivalence of the crossed defects rather than through a cardinal (see DK-3.2-prop).  What remains beyond the printed sentence is the `SpectralMultiplicityFoundation` inhabitation, which is repository bookkeeping and is recorded in `next_action`, not a blocker.

**REALIZATION HALF ADDED 2026-08-09 (Claude Opus 5).  `DavisKahan/Geometry/Halmos/Realization.lean`, with the source-numbered wrapper `Frontier.Section3.theorem3_1_realization`.**

Everything above is the CLASSIFICATION half of Theorem 3.1 -- the angle datum determines the pair.  The paper's sentence (ii), that a prescribed admissible angle datum is ATTAINED by a concrete pair, was not represented anywhere in the repository.  It now is, by the paper's own direct-rotation construction.

THE CONSTRUCTION.  For complex Hilbert spaces `E` (read: `P H`) and `F` (read: `Pperp H`), work in `WithLp 2 (E x F)`.  `U` is the `E`-factor and `V` is the range of the isometry `W0 x = (C0 x, J S0 x)`, where `(C0, S0)` and `(C1, S1)` are the prescribed `(cos Theta, sin Theta)` pairs and `J` is the intertwiner.  `W0` is isometric because `J` is isometric on the range of `S0`, so `V` is closed and `P_V = W0 W0*`.

THE BLOCK MATRIX AGREES WITH THE SOURCE.  `HalmosAngleDatum.starProjection_targetSubspace_apply` computes `P_V = [[C0 C0, C0 S0 J*], [J S0 C0, S1 S1]]`, POSITIVE in both off-diagonal entries, read off a genuine `starProjection` so that self-adjointness is structural rather than assumed.  This MATCHES the printed (3.7), `Q = U P U^-1 ~= [[C0^2, C0 S0*], [S0 C0, S0 S0*]]` on page 14 of the original.  A 2026-08-08 campaign note had claimed the printed `Q` carried a mixed sign and was not self-adjoint; that claim was CHECKED AGAINST THE ORIGINAL SCAN ON 2026-08-09 AND WITHDRAWN -- there is no such defect.  The minus sign occurs only in the second column of the direct rotation `U` at (3.6), where it is correct, and in the nearby `Q_- = XQX` display, which carries two minus signs and is likewise self-adjoint.  Do not reassert a Section 3 sign erratum without re-reading page 14; see `dev/external-literature-references.md`, Known source errata, item 2.

WHY 0 IS EXCEPTIONAL AND pi/2 IS NOT, PROVED RATHER THAN ASSERTED.  The four elementary Halmos summands of the constructed pair are computed exactly: `U /\ V = modelInl '' ker S0` (`halmosCommonPart_eq`), `Uperp /\ Vperp = modelInr '' ker S1` (`halmosExteriorPart_eq`), `U /\ Vperp = modelInl '' ker C0` (`halmosSourceDefect_eq`), `Uperp /\ V = modelInr '' ker C1` (`halmosTargetDefect_eq`).  For an angle in [0, pi/2] `ker S` is the angle-0 eigenspace and `ker C` the angle-pi/2 eigenspace.  The angle-0 spaces therefore land in the two UNCROSSED intersections and the angle-pi/2 spaces in the two CROSSED defects.  `crossedDefectEquiv` then proves `ker C0 ~= ker C1` as a linear isometric equivalence -- `J` restricted -- because `ker C0` lies inside the range of `S0`, where `J` is isometric, and symmetrically; so the multiplicity at pi/2 is FORCED to agree, and `nonempty_halmosSourceDefect_equiv_targetDefect` transports that to `U /\ Vperp ~= Uperp /\ V`, which is exactly the condition for a unitary of the ambient space to carry `U` onto `V`.  By contrast `trivialHalmosAngleDatum` (the all-0 datum over an arbitrary pair `(E, F)`) realizes `U = V` with angle-0 spaces all of `E` and all of `F`; `E` and `F` are unrelated, so no condition at angle 0 can be imposed.  That asymmetry is the content of Theorem 3.1's hypothesis and it is now four compiled statements, not a remark.

GENERALITY, STATED HONESTLY.  Arbitrary complex Hilbert spaces; no compactness, no finite dimension, no separability.  The angle datum is recorded by the PAIR `(cos Theta, sin Theta)` through the algebraic relations it satisfies -- self-adjoint, commuting, `C^2 + S^2 = 1`, plus the two intertwining relations and the two partial-isometry relations for `J`.  A CORRECTION TO THE BRIEF THIS WORK WAS GIVEN: positivity of `C` and `S` (equivalently, spectrum of Theta inside [0, pi/2]) is NOT used anywhere in the construction or in any of the four summand identities.  The first draft of the route assumed it would be needed to get `C0 a = a` from `S0 a = 0`; it is not, because `C0` restricted to `ker S0` is an involution of `ker S0`, so `C0 '' ker S0 = ker S0` and the identity `U /\ V = modelInl '' ker S0` holds with no order theory at all.  Positivity belongs to the READING of the theorem (it is what makes `ker S` the angle-0 space and `ker C` the angle-pi/2 space), not to its proof.  What is therefore NOT claimed: no bridge is proved from a self-adjoint `Theta` with `spectrum` in [0, pi/2] to the `(C, S)` pair via the continuous functional calculus, and in particular `J Theta_0 = Theta_1 J` is not shown to imply `J cos Theta_0 = cos Theta_1 J`; the datum carries the two intertwining relations as hypotheses instead.  That bridge is the one piece of the paper's sentence still stated at the level of `(cos, sin)` rather than of `Theta`.  All declarations axiom-clean [propext, Classical.choice, Quot.sound] and reachable from `DavisKahan.All`.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 8 is UPHELD and the status is
LOWERED `compiled_exact` -> `compiled_specialization`.  The audit's own reading is the right one: the
CLASSIFICATION half is genuinely both-directional and correct, and `compiled_exact` overstated only
the REALIZATION half.  MEASURED 2026-08-09 by elaborating `theorem3_1_realization`: its input is a
`HalmosAngleDatum` of `(cos_0, sin_0, cos_1, sin_1, J)` with the intertwining relations supplied as
FIELDS.  The printed sentence starts instead from Hermitian `Theta_j` with `0 <= Theta_j <= pi/2` and
equal spectral multiplicity functions, and PRODUCES the intertwiner `J_0` from that equality.  So the
gap is exactly the bridge recorded in the row's own follow-up (1), and it is a scope gap, not proof
debt about something false.  The invariant translation (Halmos summand dimensions plus
`genericCosineBlock` multiplicity, against the paper's spectral multiplicity functions of
`Theta_0, Theta_1`) is likewise argued in prose and not itself compiled.

**THE OPERATOR-LEVEL CLASSIFICATION IS NOW REAL, 2026-08-10 (Claude Opus 5, coordinator-verified).**  `twoProjection_operator_classification_real` states the printed iff over `InnerProductSpace R` with NO compactness, NO finite dimension and NO separability, grounded by `:=` on the `RCLike`-generic `twoProjection_operator_classification`.  The realization half is real too and cost NOTHING: `Realization.lean` went over by pure scalar substitution with zero tactic edits and needs NO functional-calculus hypothesis at all.  The Halmos spine, generic-position block algebra, pair-equivalence vocabulary and canonical compression API are all `RCLike` as of 129e25a4 and today's work.

**THE RESIDUAL REAL-SCALAR GAP ON THIS ROW IS NOW NARROW AND SPECIFIC: real SPECTRAL-MULTIPLICITY theory.**  `SameSpectralMultiplicity` is built on `TauCeti.MultiplicityDatum`, Borel measures on `C`, and `IsStarNormal`; it is complex by construction, not by binder choice.  So the blocker on this row should be read as `real Borel/multiplicity theory`, NOT as `real scalars` -- the operator-level statement is done.
- **Next action:** Nothing for Theorem 3.1's statement or for uniqueness: the biconditional is proved in the operator phrasing, the paper's multiplicity phrasing, and -- since 2026-08-06 -- the datum is unique (measure class and level sets both determined by the operator, `operatorUnitaryEquiv_iff_measureEquiv_and_level`); and since 2026-08-09 the realization half (sentence (ii)) is proved as well, `Frontier.Section3.theorem3_1_realization`.  Two follow-ups, neither blocking.  (1) Bridge the realization datum from `(cos Theta, sin Theta)` to a single self-adjoint `Theta` with spectrum in [0, pi/2] via the continuous functional calculus; the missing lemma is that an intertwiner of two self-adjoint operators intertwines their continuous functional calculi, for a PARTIAL isometry (`ForTauCeti/Analysis/InnerProductSpace/SeparatedIntertwiner.lean` has `cfcHom_intertwines`, which should be the starting point).  Until that exists, `HalmosAngleDatum` carries `J cos Theta_0 = cos Theta_1 J` and `J sin Theta_0 = sin Theta_1 J` as hypotheses rather than deriving them from `J Theta_0 = Theta_1 J`.  (2) Inhabit `SpectralMultiplicityFoundation` from the now-proved uniqueness (canonical Datum as a quotient by `measureClassSetoid`); parked with the promotion bookkeeping.

#### Corollary 3.1: Compact classification by angle eigenvalues

- **Kind:** `corollary`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** When the cross projection is compact, the decreasing angle eigenvalue lists, including possible zero multiplicity, classify the pair.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.SameCompactAngleData`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.isCompactOperator_genericCosineBlock`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.eigenspace_genericCosineBlock_zero`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.finrank_eigenspace_eq_of_intertwiner`, `TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.sameHalmosTrivialDimensions_orthogonal_right_iff`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_compact_classification_real`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_compact_angleList_classification_real`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_realization`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_realization_zeroMultiplicity`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_prescribedAngleSequence_classification`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.approximationNumber_genericCosineBlock_eq_ambient`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification_complex`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification_real`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_prescribedAngleSequence_classification_real`
- **Assessment:** **PROVED 2026-08-04, both directions, admission-free.**

`pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData` (`DavisKahan/Geometry/Halmos/CompactClassification.lean`): when `P_U P_V P_U` is compact on both sides, two ordered pairs are unitarily equivalent as pairs **iff** their four elementary Halmos summands are isometric and every angle has the same multiplicity. `#print axioms` gives exactly [propext, Classical.choice, Quot.sound], and the module is reachable from `DavisKahan.All`.

HOW THE PAPER'S 'DECREASING EIGENVALUE LIST' IS RECORDED. Coordinate-free, as the dimension function `mu |-> finrank (ker (cos^2 Theta - mu))`. That carries the same information as the decreasing list -- for a compact positive operator with trivial kernel the nonzero eigenvalues have finite multiplicity and accumulate only at 0, so the dimension function *is* the multiset of the list -- and it needs no ordering theory to state. The paper's 'including possible zero multiplicity' bookkeeping is not lost: a zero or right angle is an elementary summand (`U /\ V`, `U /\ Vperp`, `Uperp /\ V`, `Uperp /\ Vperp`), carried by the four `Nonempty` fields separately from the generic angle data.

THE NEW FOUNDATION. `ForTauCeti/Analysis/InnerProductSpace/CompactSelfAdjointClassification.lean`: two compact self-adjoint operators with trivial kernel and equal eigenspace dimensions are unitarily equivalent. Built on Mathlib's spectral theorem for compact self-adjoint operators (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` and `finite_dimensional_eigenspace`) plus `IsHilbertSum`. The construction routes both operators through a COMMON Euclidean model per eigenvalue, so the two `IsHilbertSum.linearIsometryEquiv`s land in one `lp` space and compose -- Mathlib has no congruence `lp G 2 ~= lp G' 2` from a family of isometries, and this sidesteps needing one.

Feeding it needed two facts about the angle operator, both new: it is the compression of `P_U P_V P_U` to the U-half (`genericCosineBlock_eq_compress_halmos`), hence compact; and its kernel is trivial, which is generic position -- its quadratic form is `||P_V m||^2`.

HISTORY. The pre-existing frontier statement `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_compact_angleList_classification` remains `sorry` and is not on this row's evidence path. Unlike the Theorem 3.1 frontier statement it was at least not vacuous.

**PROVED 2026-08-06.** `Frontier.Section3.corollary3_1_compact_angleList_classification` is axiom-clean. It had been a `sorry` for two reasons, both bookkeeping rather than mathematics. (1) It compared the SYMMETRIZED `genericHalmosCosineSq`, which is `A + A` -- doubled multiplicity -- while the classification's invariant had been moved onto `genericCosineBlock` on 2026-08-04 precisely to keep multiplicity-halving off the critical path (docstring at Frontier/Section3.lean:1005). The corollary was never updated; it now uses `genericCosineBlock`. (2) It phrased the invariant as an approximation-number list where the proved theorem `pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData` (Geometry/Halmos/CompactClassification.lean:195, sorry-free all along) uses a dimension function.

The list/dimension bridge is now proved for compact positive operators with trivial kernel (`TauCeti.finrank_eigenspace_eq_card_approximationNumber_eq` and the capstone `TauCeti.exists_linearIsometryEquiv_intertwining_of_approximationNumber_eq`, ForTauCeti/Analysis/InnerProductSpace/CompactApproximationEigenvalues.lean); the reverse direction is `approximationNumber_eq_of_boundedOperatorsUnitaryEquivalent`, by sandwiching between the two contractions of a linear isometric equivalence.

TRIVIAL KERNEL IS LOAD-BEARING, not decoration: `A = 0` on `C` and `B = 0` on `C^2` have identical approximation-number sequences and are not unitarily equivalent. Genericity supplies it -- on the generic part no vector sits at angle pi/2 (`eigenspace_genericCosineBlock_zero`). The same omission made `CompactPositiveListFoundation` UNINHABITABLE until it was repaired the same day.

**HYPOTHESIS FIDELITY BUG FOUND AND FIXED 2026-08-07 (Claude Opus 5).**  The compiled corollary assumed `P Q P` compact.  Davis and Kahan assume the DEFECT block `P tilde(Q) P = P (I - Q) P` compact.  The two are incomparable in infinite dimension: `P(I-Q)P` compact says the principal angles accumulate only at `0`; `PQP` compact says they accumulate only at `pi/2`; neither implies the other unless `P` is itself compact.  So the compiled statement was not the printed one, and on the generic infinite part it is the wrong one.

The repair is exact rather than approximate because `P (I - Q) P = P P_{Vperp} P`: the defect block of the pair `(U, V)` IS the cosine block of the pair `(U, Vperp)`.  Two elementary new lemmas -- complementing the second subspace preserves pair-equivalence, and merely permutes the four elementary Halmos summands (`U cap V` with `U cap Vperp`, `Uperp cap V` with `Uperp cap Vperp`) -- turn the printed statement into the compiled one applied to `(U, Vperp)`.  The classifying invariant is correspondingly the SINE-square angle list, `compactAngleEigenvalueList (genericCosineBlock U Vperp)`.

On the invariant's phrasing: the list is of `sin^2 theta_j` in decreasing order (the approximation numbers of the defect block).  `theta |-> sin^2 theta` is strictly monotone on `[0, pi/2]`, so equality of these lists is equivalent to equality of the printed angle lists; the statement is therefore exact, not a reparametrised weakening.  The old `PQP` statement is retained -- it is a true theorem, just not this corollary.

**SOURCE-VERIFIED AGAINST THE FULL TRANSCRIPTION 2026-08-07 (Claude Opus 5).**  The printed Corollary 3.1 hypothesis is `P (I - Q) P` compact -- confirmed verbatim against the transcription, not merely against the distilled notes.  The repair landed as `corollary3_1_compact_defectBlock_angleList_classification` is therefore against the right statement.  The printed conclusion is that the eigenvalues of `Theta_0` form an arbitrary sequence `pi/2 >= theta_1 >= theta_2 >= ...` approaching `0`, with those of `Theta_1` the same up to the multiplicity of `0`; the paper adds that the hypothesis holds in particular when `dim P` is finite.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 7 is UPHELD for this row and the
status is LOWERED `compiled_exact` -> `compiled_specialization`.  The classification half is exact and
both-directional, on the printed compactness hypothesis, and MEASURED 2026-08-09 by elaborating
`corollary3_1_compact_defectBlock_angleList_classification`.  What is absent is the corollary's second
sentence, its REALIZATION half: "The eigenvalues `theta_i` of `Theta_0` are an arbitrary sequence
satisfying `pi/2 >= theta_1 >= theta_2 >= ...` and approaching 0, together with a possible eigenvalue
0.  The eigenvalues of `Theta_1` must be the same except perhaps for the multiplicity of 0."  Nothing
constructs a pair from a prescribed decreasing null sequence.

**THE DIMENSION-FUNCTION PHRASING IS NOW REAL, 2026-08-10 (Claude Opus 5, coordinator-verified).**  `corollary3_1_compact_classification_real` instantiates `pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData` at `R` by `:=`.  `CompactSelfAdjointClassification.lean`'s complex restriction WAS GRATUITOUS and is gone: Mathlib states both ingredients over `RCLike` (`orthogonalComplement_iSup_eigenspaces_eq_bot` and `finite_dimensional_eigenspace`, Analysis/InnerProductSpace/Spectrum.lean L443 and L463); the only real fix was `set G : K -> Type` becoming `Type _`, since `EuclideanSpace K (Fin n)` leaves `Type` once `K : Type*`.  No hypothesis added, no proof changed.

TWO THINGS REMAIN, and they are different from each other.  (1) The DECREASING EIGENVALUE LIST phrasing (`corollary3_1_compact_angleList_classification`) is blocked on exactly one file, `ForTauCeti/Analysis/InnerProductSpace/CompactApproximationEigenvalues.lean`, which is C-hardwired with `((s : R) : C)` eigenvalue coercions -- a self-contained migration and the next cheapest real target.  (2) THE COMPACT-OBJECT QUESTION ALREADY RECORDED ON THIS ROW IS UNCHANGED AND IS INHERITED BY THE REAL FORM: the classification hypothesis is `IsCompactOperator (P_U P_V P_U)`, while Davis and Kahan assume the DEFECT block `P (I - Q) P` compact, and this row already records that the two are INCOMPARABLE in infinite dimension.  The real theorem faithfully instantiates the existing generic one, so it neither fixes nor worsens that; do not read `real form landed` as `compact object settled`.

**THE DECREASING EIGENVALUE LIST PHRASING IS NOW REAL, 2026-08-10 (Claude Opus 5, coordinator-verified).**  `corollary3_1_compact_angleList_classification_real` instantiates the generic corollary at `R` by `:=` with no added hypothesis; the CFC instances are SYNTHESIZED at `R`, not carried.  `CompactApproximationEigenvalues.lean`'s complex restriction WAS GRATUITOUS: no hypothesis added, no proof restructured, no lemma introduced -- only `Complex.ofReal_injective`, `Complex.conj_eq_iff_re` and `.re` dot notation replaced by their `RCLike` spellings (dot notation dies once the type head is a variable), plus three `simp` calls tightened into explicit identities.

**THE `SINGLE BLOCKER` CLAIM WAS WRONG.**  A prior report named `CompactApproximationEigenvalues.lean` as the one remaining blocker; there were TWO.  The angle-list layer itself -- `compactAngleEigenvalueList`, `approximationNumber_eq_of_boundedOperatorsUnitaryEquivalent` and `corollary3_1_compact_angleList_classification` -- was also C-bound, pinned inside Section3's `section Classification` next to the genuinely-complex `theorem3_1_spectralMultiplicity_classification`.  Migrating the ForTauCeti file alone would have produced NO real endpoint.  Those three moved into the already-generic `section OperatorClassification`; their explicit hypotheses are unchanged (verified by diffing the signature across the move).  `theorem3_1_spectralMultiplicity_classification` stayed at C, correctly.

MEASURED AND VERIFIED BY THE COORDINATOR: `compactAngleEigenvalueList` elaborates to codomain `N -> R` over EVERY field -- only `K` moved, the angle list did NOT become `K`-valued.  That was the one way this migration could have silently changed what this row claims.

**WHAT REMAINS ON THIS ROW, unchanged in substance.**  (1) THE REALIZATION HALF -- nothing constructs a pair from a prescribed decreasing null sequence `pi/2 >= theta_1 >= theta_2 >= ... -> 0` with prescribed zero-angle multiplicities.  That is the row's actual remaining mathematics and the reason it is `compiled_specialization`.  (2) The `P(I-Q)P` versus `PQP` compact-object question, already recorded above, untouched and inherited by both real forms.  (3) NEW AND SMALL: the printed-hypothesis form `corollary3_1_compact_defectBlock_angleList_classification` is still C-only because its two helpers (`pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff`, `sameHalmosTrivialDimensions_orthogonal_right_iff`) remain in the C section; nothing in them looks complex-specific, so this is probably cheap.

**THE REALIZATION SENTENCE IS DISCHARGED, IN BOTH FORMS, 2026-08-10 (Claude Opus 5, coordinator-verified).**  `corollary3_1_realization` takes a prescribed decreasing null sequence with `0 <= theta_n <= pi/2` and EXHIBITS the pair -- compactness of the defect block, the angle list equal to `sin^2 theta_n`, and both Halmos parts identified.  `corollary3_1_realization_zeroMultiplicity` does the same with PRESCRIBED ANGLE-ZERO MULTIPLICITIES, over arbitrary independent spaces `Z0`, `Z1`, under the extra `hne : theta n != 0` used ONLY by the two multiplicity conclusions.  Both are `RCLike`-generic, so they instantiate at `R` for free.  The pair is EXHIBITED, not asserted to exist.

**IT IS ON THE PRINTED COMPACT OBJECT.**  Machine-checked, and coordinator-confirmed by reading the statement: the compactness is of `P_U (id - P_V) P_U`, the DEFECT block Davis and Kahan assume, not `PQP`.  Non-compactness of `PQP` here is commentary in the docstrings and explicitly NOT proved.  The `P(I-Q)P` versus `PQP` question recorded above is therefore untouched -- but note the realization now sits on the printed side while this development's CLASSIFICATION hypothesis sits on `PQP`.

**WHAT REMAINS IS ONE BRIDGE, AND IT IS THE CHEAPEST ITEM LEFT ON THIS ROW.**  The realization does not yet plug into the classification by `:=`.  The classification's invariant is `compactAngleEigenvalueList (genericCosineBlock U Vperp)`, an operator on `genericLeftHalf U Vperp`; the realization gives the same list for the AMBIENT block.  They coincide when the four elementary Halmos summands are trivial, since extension by zero preserves approximation numbers, but that lemma is not proved.  Prove it and the two halves of Corollary 3.1 compose.

**THREE ROUTE CORRECTIONS, measured, recorded so they are not re-derived.**  (i) `PrescribedSequence.lean` was NOT the right tool: `exists_approximationNumber_eq_of_antitone` is EXISTENTIAL, and a `HalmosAngleDatum` needs a MATCHED pair `(cos, sin)` with `cos^2 + sin^2 = 1` POINTWISE, which an existentially produced operator cannot supply.  The key was one level below, in `DiagonalSequence.lean`: `diagOpLp`, `approximationNumber_diagOpLp`, `isCompactOperator_diagOpLp`.  (ii) The handoff's `add the four elementary Halmos summands` is wrong twice: the `pi/2` multiplicity needs NO extra summand -- with `theta <= pi/2` it sits at the head of the sequence as `ker cos_0` inside the same `l^2` -- and it CANNOT be prescribed independently anyway, because item 7 of `theorem3_1_realization` FORCES the two `pi/2` multiplicities to agree.  Only TWO summands are needed.  (iii) The bare-sequence version alone CANNOT realize a finite nonzero angle-zero multiplicity: on `l^2(N)` with `theta` antitone and tending to zero, `ker (diag sin theta)` has dimension `0` or `aleph_0`, never finite and nonzero.  That is exactly why the multiplicity version is a separate theorem.

**THE BRIDGE IS PROVED AND THE TWO HALVES NOW COMPOSE, 2026-08-10 (Claude Opus 5, coordinator-verified).**  `approximationNumber_genericCosineBlock_eq_ambient` shows the generic cosine block and the ambient block have the same approximation numbers when `halmosTrivialPart U V = bot`, over arbitrary `RCLike`, with no compactness and no dimension hypothesis.  `corollary3_1_prescribedAngleSequence_classification` then goes from a prescribed angle sequence to the classification iff WITH NO UNPROVED STEP.  Both conclusions are on the DEFECT block `P (1 - Q) P`, as printed, on both sides -- the bridge needs NEITHER compact object, so the `PQP` versus `P(I-Q)P` incomparability record is untouched.

**RECORDED NARROWING, in those words.**  The printed sequence allows `pi/2 >= theta_1 >= ... -> 0` together with a possible eigenvalue `0`; the composed statement assumes `0 < theta_n < pi/2` STRICTLY.  That strictness is exactly what makes the four elementary Halmos summands trivial, which is what the bridge needs.  The angle-`0` and angle-`pi/2` data are not lost -- they ARE the elementary summands, carried by `SameHalmosTrivialDimensions`.

THE NEAR-REBUILD WAS REAL.  The general fact -- extension by zero preserves approximation numbers -- existed nowhere as a named lemma, but its exact proof was sitting INLINE inside `exists_approximationNumber_eq_of_antitone` in `ForTauCeti/.../PrescribedSequence.lean`, the very file `Section3.lean` already imports.  It is now extracted as `approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto` and the original site consumes it, so that file is 33 lines shorter with one source of truth.  A COORDINATOR CLAIM WAS ALSO WRONG: the brief suggested looking in `Pinching.lean` and a `Compression.lean`; there is no `Compression.lean` under `ApproximationNumber/` and the lemma was in neither.

ALSO CORRECTED: the claim that this development's classification hypothesis is `PQP` is only HALF TRUE.  `corollary3_1_compact_defectBlock_angleList_classification` (`Section3.lean:2169`) was ALREADY stated with the printed `P (I - Q) P` hypothesis and the `genericCosineBlock` invariant.  The defect-block classification was already there.

**WHAT REMAINS.**  (a) The same composition against `corollary3_1_realization_zeroMultiplicity`, where the elementary summands are DELIBERATELY nontrivial, so the bridge as stated does not apply; a multiplicity-aware version would need the ambient list to be the generic list merged with `1`s of multiplicity `dim (U inf Vperp)`.  (b) A real-scalar instance of the composed corollary -- BLOCKED, because `corollary3_1_compact_defectBlock_angleList_classification` is `C`-only while the realization is `RCLike`-generic.  (c) The `PQP` versus `P(I-Q)P` question, untouched.

**REAL DEFECT-BLOCK AND COMPOSED CLASSIFICATIONS LANDED 2026-08-10 (Claude Opus 5, coordinator-verified).**  `corollary3_1_compact_defectBlock_angleList_classification` and its two helpers `pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff` and `sameHalmosTrivialDimensions_orthogonal_right_iff` are now `RCLike`-generic.  SIGNATURE DIFFS WERE MEASURED ACROSS THE RELOCATION and are reported here because a section move can silently change hypotheses: the two helpers gained ONLY `{K} [RCLike K]`, nothing else; the defect theorem gained `{K} [RCLike K]` and SIX INSTANCE-IMPLICIT calculus arguments, with EXPLICIT hypotheses and conclusion LITERALLY UNCHANGED -- confirmed by discharging the pre-move complex statement verbatim as an `example`.

The defect theorem went into a NEW adjacent generic section rather than into `section OperatorClassification` as the coordinator's brief suggested, and the reason is worth keeping: that section's calculus variables are pinned to the specific subspace pairs and Lean auto-includes them in every later declaration mentioning those pairs, which both attached four hypotheses the defect statement never uses AND broke one helper's own proof, since it applies its sibling at `V_1 perp` and so demanded a calculus instance at a different generic half.

STALE CITATION CORRECTED: this row's notes cited `corollary3_1_compact_defectBlock_angleList_classification` at `Section3.lean:2169`; it was at `:2267` and is now at `:2149`.
- **Next action:** Three items, none of them scalars: the multiplicity-aware composition; the `P(I-Q)P` versus `PQP` compact-object question; and, if one generic composed corollary is wanted rather than a per-field split, the concrete-pair instance diamond in `scope_gap` item (c), which is upstream work.

#### Proposition 3.5: Angle commutation and eigenspace geometry

- **Kind:** `proposition`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** The full angle commutes with both projections, the quarter-turn and direct rotation; its eigenspaces are maximal reducing constant-angle subspaces in the acute case.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.bounded_angle_commute`, `TauCeti.DavisKahan1970.bounded_sinAngleOperatorC_norm`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.IsFixedCosineReducingSubspace`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.fixedCosineSubspace`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.fixedCosineSubspace_isFixedCosineReducing`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.fixedCosineSubspace_maximal`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_5_fixedAngle_maximal`, `TauCeti.DavisKahan.Experimental.halmosCosineSq_commute_projection`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.halmosCosineSq_commute_projection_right`, `TauCeti.DavisKahanTheory.sq_sinAngleOperator_add_sq_directRotationCosine`, `TauCeti.DavisKahanTheory.projection_comm_sinAngleOperator`, `TauCeti.DavisKahanTheory.projection_right_comm_sinAngleOperator`, `TauCeti.DavisKahanTheory.directRotation_comm_sinAngleOperator`, `TauCeti.DavisKahanTheory.angleOperator_comm_projection`, `TauCeti.DavisKahanTheory.angleOperator_comm_projection_right`, `TauCeti.DavisKahanTheory.angleOperator_comm_directRotation`, `TauCeti.adjoint_moorePenroseInverse_of_isSymmetric`, `TauCeti.comp_moorePenroseInverse_comm_of_isSymmetric`, `TauCeti.moorePenroseInverse_comm_of_isSymmetric`, `TauCeti.DavisKahanTheory.directRotationCosine_comm_sinAngleOperator`, `TauCeti.DavisKahanTheory.angleOperator_comm_directRotationCosine`, `TauCeti.DavisKahanTheory.angleOperator_comm_sinAngleOperator`, `TauCeti.DavisKahanTheory.angleOperator_comm_moorePenroseInverse_sinAngleOperator`, `TauCeti.DavisKahanTheory.angleOperator_comm_angleComplexStructure`, `TauCeti.complementaryProjection_eq_id_sub`, `TauCeti.DavisKahanTheory.vectorAngle_directRotation_eq_of_angleOperator_apply`, `TauCeti.DavisKahanTheory.adjoint_angleComplexStructure`, `TauCeti.DavisKahanTheory.re_inner_angleComplexStructure_apply_self`, `TauCeti.DavisKahanTheory.sinAngleOperator_apply_of_angleOperator_apply`, `TauCeti.DavisKahanTheory.directRotationCosine_apply_of_angleOperator_apply`, `TauCeti.DavisKahanTheory.angleOperator_eigenvalue_mem_Icc`, `TauCeti.vectorAngle`, `TauCeti.vectorAngle_real_eq_angle`, `TauCeti.vectorAngle_eq_angle_rclikeToReal`, `TauCeti.vectorAngle_comm`, `TauCeti.vectorAngle_eq_of_re_inner_eq`, `TauCeti.repr_eq_zero_of_calculus_apply_eq_smul`, `TauCeti.selfAdjointFunctionalCalculus_apply_of_calculus_apply_eq_smul`, `TauCeti.exists_eigenvalue_of_calculus_apply_eq_smul`, `TauCeti.DavisKahanExt.commute_paperAngleOperatorC_starProjection`, `TauCeti.DavisKahanExt.commute_paperAngleOperatorC_starProjection_right`, `TauCeti.DavisKahanExt.commute_sinAngleOperatorC_starProjection`, `TauCeti.DavisKahanExt.commute_sinAngleOperatorC_starProjection_right`, `TauCeti.DavisKahanExt.adjoint_starProjection_sub`
- **Assessment:** Commutation identities are present, but the maximal eigenspace characterization is not represented.

**ROW WAS STALE.  CORRECTED 2026-08-06: the maximal eigenspace characterisation IS represented, and is proved.**  The note above -- "the maximal eigenspace characterization is not represented" -- was written when the Section 3 frontier was unbuilt and was never revisited.  `proposition3_5_fixedAngle_maximal` states both halves: the fixed-cosine eigenspace `ker (cos^2 Theta - c^2)` is itself a fixed-cosine reducing subspace, and every such subspace is contained in it.  `#print axioms` gives exactly [propext, Classical.choice, Quot.sound] on it and on both halves, and since the Frontier promotion the same day it resolves against `DavisKahan.All`, so `lake build` guards it.  The frontier gate had been reporting `s3-prop3-5` as recursively grounded throughout; the census and the manifest disagreed and the manifest was right.

**A TRANSCRIPTION CORRECTION IS CARRIED, AND IT IS LOAD-BEARING.**  The printed predicate constrains only the source vectors `M cap U` and the target vectors `M cap V`.  That is insufficient for the maximality half: a nonzero vector of the exterior `U-perp cap V-perp` -- which acuteness permits -- spans a subspace that reduces both projections and satisfies the printed conditions vacuously, yet carries cosine square `1`, not `c^2`.  So for `c < 1` the printed predicate admits subspaces not contained in the eigenspace and the proposition as transcribed is false.  `IsFixedCosineReducingSubspace` adds the two complement conditions on `M cap U-perp` and `M cap V-perp`, which is what the paper's own phrasing -- *all nonzero vectors make the fixed angle with the opposite subspace* -- actually says, and which excludes the exterior.  The acuteness and `c <= 1` hypotheses are kept for source correspondence; the proof needs only `0 < c`.

The commutation identities this row already listed (`bounded_angle_commute`, `bounded_sinAngleOperatorC_norm`) are the other clause of the printed proposition and remain the reusable half.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 6 is UPHELD and the status is
LOWERED `compiled_exact` -> `compiled_specialization`.  The `next_action` read "Both clauses of
Proposition 3.5 are proved"; the printed proposition has SIX assertions, not two (transcription
L1143--1153): `Theta` commutes with `P`, with `Q`, with `J` and with `U`; every eigenvector satisfies
`angle(x, Ux) = theta`; and the eigenspace `Omega({theta})H` is the unique maximal subspace with
(a)(b)(c).

MEASURED 2026-08-09 by elaboration.  The two declarations the row offered are NEITHER printed
commutation: `bounded_angle_commute` is `Commute (sinAngleOperatorDirectedC U V) (cosAngleOperatorC U V)`,
and `bounded_sinAngleOperatorC_norm` is the norm identity `||sin Theta|| = subspaceGap U V`.  What
IS proved of the commutations is at the `cos^2 Theta` level, and was not listed:
`halmosCosineSq_commute_projection` and its right companion, now added.  The maximal-subspace clause
is genuinely proved (`fixedCosineSubspace_maximal`).  Absent: the commutations at the `Theta` level
rather than `cos^2 Theta`, `Theta <-> J` and `Theta <-> U` (there is no `J` operator anywhere in the
repository -- see `next_action`), and the eigenvector-angle clause.

**M19, 2026-08-09 (Claude Opus 5).**  THE PREVIOUS NOTE'S PARENTHESIS -- "there is no `J` operator anywhere in the repository" -- IS FALSE, and was false when written.  `TauCeti.DavisKahanTheory.angleComplexStructure` (`DavisKahan/FiniteDimensional/DirectRotation.lean`) is the paper's `J`, and `directRotation_eq_cos_add_J_sin` is the paper's `U = cos Theta + J sin Theta`.  Both predate this work; what was missing were the properties.

THREE OF THE FOUR PRINTED COMMUTATIONS ARE NOW PROVED, at the level of `Theta` itself and not `cos^2 Theta`, over any `RCLike` field in finite dimension: `angleOperator_comm_projection` (`Theta` with `P`), `angleOperator_comm_projection_right` (`Theta` with `Q`) and `angleOperator_comm_directRotation` (`Theta` with `U`).  Each is the corresponding `sin Theta` statement pushed through `selfAdjointFunctionalCalculus_comm`, since `angleOperator U V = arcsin |P_U - P_V|`.

The linchpin is `sq_sinAngleOperator_add_sq_directRotationCosine`, the operator Pythagoras identity `sin^2 Theta + cos^2 Theta = 1` in the finite `RCLike` `LinearMap` setting.  It needs no acuteness hypothesis: it reduces to `(P-Q)^2 + PQP + (1-P)(1-Q)(1-P) = 1`, an identity for any two idempotents.  With it, commutation with `cos Theta` transfers to `sin^2 Theta` and then to `sin Theta` by `sqrt_comm`.

STILL ABSENT AS OF M19: `Theta` commutes with `J`, and the eigenvector clause `angle(x, Ux) = theta`.  The first needs a Moore--Penrose commutation lemma (`B A = A B` implies `B A+ = A+ B` for self-adjoint `A`), which the repository does not have; `J` is `(U - cos Theta) . (sin Theta)+`.  The second still needs `InnerProductGeometry`.

**M24, 2026-08-09 (Claude Opus 5).  `Theta` COMMUTES WITH `J` IS NOW PROVED** -- `angleOperator_comm_angleComplexStructure` -- so five of the six printed assertions hold, in finite dimension over any `RCLike` field.  Only the eigenvector clause `angle(x, Ux) = theta` remains, and it still needs `InnerProductGeometry`.

TWO BRICKS WERE MISSING, NOT ONE.  The M19 next_action recorded that `Theta` "already commutes with `U` and with `cos Theta`", so that only the Moore--Penrose lemma was wanted.  The first half was true (`angleOperator_comm_directRotation`); the second was not -- no declaration said `Theta` commutes with `cos Theta`, and `J = (U - cos Theta)(sin Theta)^+` needs it.  It is now `directRotationCosine_comm_sinAngleOperator` (`cos Theta` commutes with the Gram operator `S*S = cos^2 Theta`, which operator Pythagoras rewrites as `1 - sin^2 Theta`, so it commutes with `sin Theta` by `sqrt_comm`; no acuteness needed) together with `angleOperator_comm_directRotationCosine`.

The Moore--Penrose brick is `TauCeti.moorePenroseInverse_comm_of_isSymmetric` in `ForTauCeti/Analysis/InnerProductSpace/MoorePenroseInverse.lean`: for self-adjoint `A`, `B A = A B` implies `B A+ = A+ B`.  Only commutation with `A` is assumed -- `A* = A` makes `B*` commute with `A` as well, and the two together force `B` to commute with the Penrose projection `P = A A+ = A+ A` (`comp_moorePenroseInverse_comm_of_isSymmetric`, itself downstream of `adjoint_moorePenroseInverse_of_isSymmetric`).  Then `A+ B = A+ P B = A+ B P = A+ B A A+ = A+ A B A+ = P B A+ = B P A+ = B A+`.

**M33, 2026-08-09 (Claude Opus 5).  MEASURED AND LEFT BLOCKED; the entry point is written out.**  The real direct rotation now exists in arbitrary dimension (`TauCeti.DavisKahan.Experimental.directRotationR`) and the real angle operators already existed (`DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean`), so the natural expectation is that this row's commutations transport.  THEY CANNOT, because the complex statements they would be transported from DO NOT EXIST.  Measured 2026-08-09 by searching the whole tree: no declaration anywhere says that `paperAngleOperatorC` or `sinAngleOperatorC` commutes with either projection or with the direct rotation.  Every `Theta`-level commutation on this row -- `angleOperator_comm_projection`, `angleOperator_comm_directRotation`, `angleOperator_comm_angleComplexStructure` and the rest -- is `RCLike` (so already real) but `[FiniteDimensional]`; the only INFINITE-dimensional complex facts the row carries are `bounded_angle_commute` (sin and cos of the DIRECTED angle commute), `bounded_sinAngleOperatorC_norm`, `halmosCosineSq_commute_projection` and the fixed-cosine subspace material.  So closing the scalar axis honestly requires the bounded-tree `Theta` commutations to be proved over `C` FIRST -- which is the dimension axis this row already records -- and only then transported.  Transporting the three ambient facts that do exist would put real infinite-dimensional declarations on the row without covering any printed commutation clause, so it was not done.

**AUDIT FINDING 2026-08-10 (Claude Opus 5, coordinator), relevant to the outstanding eigenvector clause.**  `next_action` correctly says `InnerProductGeometry` is used nowhere in the repository and the angle has to be brought in.  WHEN IT IS BROUGHT IN, MATCH THE PAPER'S OWN DEFINITION, WHICH IS PRINTED AND CURRENTLY UNCOVERED BY ANY CENSUS ROW.  Transcription (1.14) defines the angle between nonzero VECTORS as `arccos( Re(y* x) / (||x|| ||y||) )`; (1.15) defines the angle between the LINES `[x]`, `[y]` as `arccos( |y* x| / (||x|| ||y||) )`.  REAL PART versus ABSOLUTE VALUE -- the paper draws that distinction explicitly and they differ.  The eigenvector clause `angle(x, Ux) = theta` is a VECTOR angle, so it is (1.14).  Picking Mathlib's `InnerProductGeometry.angle` without checking which normalization it uses is exactly the trap the handoff warns about here.  Equations (1.14)-(1.18) -- the vector angle, the line angle, `Theta_j = arccos (C_j C_j*)^(1/2)`, the ambient `Theta = diag(Theta_0, Theta_1)`, and `U = exp(J Theta) = cos Theta + J sin Theta` -- are the definitional foundation of the whole angle apparatus and are named by NO census row: `S1-block-residual` stops at (1.8) and `S1-ui-norms` stops at (1.13).  Consider a new `S1-angle-operators` row so that dictionary is probed rather than assumed.

**GENUINE COMPLEX OBSTRUCTION FOUND 2026-08-10 (Claude Opus 5, coordinator-verified by reading the proof).  THIS ROW'S REAL-SCALAR AXIS IS NOT CHEAP, UNLIKE ITS SECTION 3 SIBLINGS.**

`eigen_of_reducing_quadratic` (`DavisKahan/Frontier/Section3.lean`, ~L1000) states that a bounded operator preserving a subspace and having vanishing quadratic form there vanishes on it.  Its proof is COMPLEX POLARIZATION: it tests against `w + Complex.I . v` and uses `Complex.conj_I` and `Complex.I_ne_zero`.

**THE STATEMENT IS FALSE OVER `R`.**  Any skew-symmetric operator satisfies `<T x, x> = 0` for every `x` and is not zero; rotation by ninety degrees in `R^2` is a two-line counterexample.  So the real form of the fixed-cosine block characterization CANNOT be obtained by scalar substitution.  It needs either a symmetry hypothesis making the real polarization identity sufficient -- and then a CHECK that such a hypothesis is actually available at the call site, not merely assumed -- or a route that never passes through `vanishing quadratic form implies zero`.

This is the FIRST complex restriction this campaign has examined that is mathematics rather than decoration.  Every other one -- Realization, CompactSelfAdjointClassification, CompactApproximationEigenvalues, and the entire polar/direct-rotation stack -- was a binder choice that substituted away with no proof change.  Do not dispatch this row as a binder-editing mission.

**THE LAST PRINTED ASSERTION LANDED 2026-08-11 (Claude Opus 5, coordinator-verified), AND THE ANGLE MATCHES THE PAPER'S OWN DEFINITION -- PROVED, NOT ASSERTED.**  New `TauCeti.vectorAngle K x y = arccos (re <y,x> / (||x|| ||y||))`, which is transcription (1.14), the VECTOR angle with a REAL PART.  Two machine-checked bridges settle the trap this row recorded: `vectorAngle_real_eq_angle` and `vectorAngle_eq_angle_rclikeToReal` show Mathlib's `InnerProductGeometry.angle` normalizes with the REAL PART too, so it is (1.14) and NOT (1.15)'s modulus.  The recorded mismatch does not fire.

TWO COORDINATOR PREMISES WERE WRONG.  (i) `J is skew-adjoint on the ACTIVE-ANGLE SUBSPACE` UNDERSTATES it: `adjoint_angleComplexStructure` gives `J* = -J` on the WHOLE space, with no subspace restriction, precisely BECAUSE `J = 0` on the zero-angle kernel.  The kernel caveat is real for `J^2 = -1` -- correctly flagged -- but does NOT apply to `J* = -J`; believing the restriction would have forced an unnecessary subspace argument.  (ii) `cfc gives cos Theta x = cos theta . x` was NOT AVAILABLE: `Theta`, `sin Theta` and `cos Theta` are functional calculi of `sin Theta`, not of `Theta`, and the repository had only the transfer FROM the operator itself.  The transfer BETWEEN TWO SYMBOLS of the same operator did not exist and was built (`selfAdjointFunctionalCalculus_apply_of_calculus_apply_eq_smul`).  Likewise `theta in [0, pi/2]` is not free -- `arccos (cos theta) = theta` fails outside `[0, pi]` -- so `angleOperator_eigenvalue_mem_Icc` was needed.

PART OF THE RECORDED SCOPE WORK ALSO LANDED: in the BOUNDED COMPLEX tree at arbitrary dimension, `Theta` now provably commutes with BOTH projections (`commute_paperAngleOperatorC_starProjection` and `..._right`, plus the `sinAngleOperatorC` siblings), with no acuteness, no finite dimension and no spectral hypothesis.  The route is the idempotent identity `(p-q)^2 p = p - p q p = p (p-q)^2` followed by `Commute.cfc_nnreal` through `CFC.sqrt` and `Commute.cfc_real` through `arcsin`.  This SUPERSEDES the M33 note that no declaration anywhere says `paperAngleOperatorC` commutes with either projection -- accurate when written.

`cfcHom_intertwines_selfAdjoint` (arrived 2026-08-11) was checked and NOT used: it is a bounded `E ->L[C] E` statement while the eigenvector clause is finite-dimensional `E ->l[K] E` over `RCLike`.  For the commutation lifting it WOULD work, but Mathlib's `Commute.cfc_real` does the same job in one line without the `symbolRestrict` bookkeeping.
- **Next action:** **ALL SIX PRINTED ASSERTIONS ARE NOW PROVED** in finite dimension over any `RCLike` field, 2026-08-11.  The eigenvector clause `angle(x, U x) = theta` is `vectorAngle_directRotation_eq_of_angleOperator_apply`; `theta in [0, pi/2]` is DERIVED, not assumed, and `IsAcute` is not a narrowing since it is what makes the direct rotation exist.

**THIS FIELD PREVIOUSLY SAID `InnerProductGeometry` IS USED NOWHERE IN `DavisKahan/` OR `ForTauCeti/`.  THAT WAS FALSE, AND THE 2026-08-10 AUDIT PARAGRAPH IN `notes` MADE IT WORSE BY BROADENING IT TO `the repository` WHILE ENDORSING IT AS CORRECT.**  MEASURED: it is used TEN times in `DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean`, landed by commit 90781d7d -- work the coordinator integrated TWO MISSIONS EARLIER in the same session.  An absence claim is falsified by any mission that creates the thing, including one's own; re-grep such claims at dispatch rather than relaying them.

WHAT REMAINS: (i) REAL SCALARS, per the `eigen_of_reducing_quadratic` obstruction recorded on `DK-3.1-prop` -- note the eigenvector clause ITSELF is already real-valid, being `RCLike`; the real gap is the fixed-cosine block characterization plus the infinite-dimensional real angle.  (ii) The `Theta`-to-`J` and `Theta`-to-`U` clauses AT BOUNDED INFINITE DIMENSION, blocked on CONSTRUCTING `J` and `U = cos Theta + J sin Theta` there -- the bounded tree has neither.  The finite proofs are structurally transportable but the OBJECTS must exist first; that is a construction project, not a transport.  (iii) The eigenvector clause at bounded infinite dimension, same blocker.

#### Corollary 3.2: Reversal symmetry

- **Kind:** `corollary`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Swapping P and Q leaves the angle operator unchanged and reverses the quarter-turn operator.
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation_reversal`, `TauCeti.DavisKahanTheory.directRotation_symm`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_2_reversal`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_2_reversal_source_form`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_2_sinAngleOperator_symm`, `TauCeti.DavisKahanTheory.angleComplexStructure_symm`, `TauCeti.DavisKahanTheory.angleOperator_comm`, `TauCeti.DavisKahanTheory.sinAngleOperator_comm`, `TauCeti.DavisKahanTheory.directRotationCosine_comm`, `TauCeti.DavisKahan1970.real_directRotation_reversal`
- **Assessment:** Direct-rotation reversal is represented; the exact angle/J statement needs a source wrapper.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The reversal theorem is compiled, axiom-clean, and resolves against the default build -- the earlier "promote it into DavisKahan/FiniteDimensional so CI guards it" instruction is discharged. The source-facing angle and quarter-turn wrapper is still absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**ROW WAS STALE ON BOTH COUNTS (2026-08-07, Opus 5).**  The recorded next_action asked to
promote the reversal theorem out of the unguarded Experimental tree and then to add a
source-facing statement.  `directRotation_symm` has been in the guarded tree
(DavisKahan/FiniteDimensional/DirectRotation.lean) all along, and
`corollary3_2_reversal_source_form` already stated the quarter-turn half in
DavisKahan/Frontier/Section3.lean.  What was genuinely missing is what that theorem's own
docstring claimed and did not prove: the *angle* half.  Corollary 3.2 asserts both, so the
row now carries `corollary3_2_sinAngleOperator_symm` and the combined
`corollary3_2_reversal`, and the older docstring was corrected to say which half it proves.

**M19, 2026-08-09 (Claude Opus 5).**  THE PRINTED FORM IS NOW PROVED, and the recorded narrowing `J |-> -J` rendered as `U |-> U*` is discharged.  `angleComplexStructure_symm` states exactly the corollary's second clause -- `J(V,U) = -J(U,V)` for the repository's `J`, `TauCeti.DavisKahanTheory.angleComplexStructure` -- and `angleOperator_comm` states the first, `Theta(V,U) = Theta(U,V)`, on the angle operator itself.  `sinAngleOperator_comm` and `directRotationCosine_comm` are the `sin Theta` and `cos Theta` halves of the latter.

The `U |-> U*` form is now the INPUT rather than the conclusion: from `U(V,U) = U(U,V)^{-1}` (`directRotation_symm`) and `2 cos Theta = U + U^{-1}` (`two_smul_abs_canonicalIntertwiner`) one gets `U(V,U) - cos Theta = -(U(U,V) - cos Theta)`, and the Moore--Penrose factor is common to both sides because `Theta` is symmetric.  Scope: finite dimension, any `RCLike` field.  The bounded complex declarations already on this row are unchanged.

**M33, 2026-08-09 (Claude Opus 5).  THE REAL-SCALAR AXIS IS CLOSED ON THIS ROW.**  The reversal clause is now proved over a REAL Hilbert space of arbitrary dimension: `real_directRotation_reversal` says `W(V,U) = W(U,V)^T` for the real direct rotation (`DavisKahan/Geometry/Polar/DirectRotationReal.lean`).  The angle half `Theta(V,U) = Theta(U,V)` already had a real form through `DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean`, whose operators are defined as real restrictions.  What is left is the DIMENSION axis on `J`.
- **Next action:** Nothing outstanding for the printed statement: both clauses of Corollary 3.2 are proved in the paper's own vocabulary (`Theta` unchanged, `J |-> -J`) and guarded by `lake build`.  Remaining scope work is the same as elsewhere in Section 3: the `J` clause is finite-dimensional, and the bounded complex tree has no `J` to state it on.

### Section 4

#### Proposition 4.1: Pointwise and singular-value extremality of the direct rotation

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** For any unitary carrying P to Q, an orthonormal sequence experiences angles at least the principal angles; equivalently the singular values of (1-V)|P are minimized by the direct rotation and equal 2 sin(theta_k/2).
- **Current Lean references:** `TauCeti.DavisKahanTheory.singularValues_restrictedDisplacement_le`, `TauCeti.DavisKahanTheory.singularValues_restrictedDisplacement_directRotation`, `TauCeti.DavisKahan1970.Proposition4_1`, `TauCeti.DavisKahan1970.Proposition4_1_directRotationValues`, `TauCeti.DavisKahan1970.Proposition4_1_infiniteDimensional`, `TauCeti.DavisKahan1970.Proposition4_1_real`, `TauCeti.DavisKahan1970.restrictedDisplacementDominance_real`
- **Assessment:** The finite pointwise singular-value theorem is compiled: every singular value of the restricted displacement (1-V)P is minimized by the direct rotation, whose values are the doubled half-angle sines 2 sin(theta_k/2).  A source-numbered wrapper and the infinite-dimensional scope remain open.

**SOURCE WRAPPER ADDED 2026-08-05**, in `DavisKahan/Sources/DavisKahan1970/Section4.lean` (namespace `TauCeti.DavisKahan1970`), so the facade can cite the paper's numbering directly.  The wrappers are `alias`es over the already-compiled general theorems, so they carry the exact statements.  The infinite-dimensional form is proved in `Experimental/MathAhead/Section4/InfiniteProposition41.lean` by a spectral-cutoff min--max argument; it is NOT aliased here, because no production module may import `Experimental` and `lake build` does not yet guard that chain.

**SECTION 4 SCOPE RE-AUDITED 2026-08-07 (Claude Opus 5).**  `DavisKahan/Sources/DavisKahan1970/Section4.lean` used to assert in its module docstring that the finite-dimensional forms "is the scope Section 4 is written at".  The transcription says otherwise: Section 4 opens "We shall make the hypotheses of Theorem 3.1 and Corollary 3.1 (leaving to the reader the modifications entailed in the absence of compactness)" and then states its propositions over infinite orthonormal sequences and infinite sums.  The docstring is corrected and the finite-dimensional aliases are now labelled as specializations.  The infinite-dimensional form was already proved and build-guarded at `DavisKahan/MathAhead/Section4/InfiniteProposition41.lean`; it is now aliased into the source facade as `Proposition4_1_infiniteDimensional`.  Elaborated signature: arbitrary complex Hilbert space, `IsAcute U V`, any unitary `W` with `W * projection U = projection V * W`, concluding that every `approximationNumber` of `sourceRestrictedDisplacement U (spectraDirectRotation U V)` is at most that of `sourceRestrictedDisplacement U W`.  No `[FiniteDimensional]` and no compactness of `P Q-tilde P`, so it is strictly more general than the hypotheses Section 4 inherits from Corollary 3.1.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreements 10 and 11 are UPHELD; both are stale paths, verified 2026-08-09 by
listing the tree and by elaboration.  (a) `DavisKahan/Experimental/MathAhead/Section4/` DOES NOT
EXIST; the two infinite-dimensional modules are `DavisKahan/MathAhead/Section4/InfiniteProposition41.lean`
and `InfiniteProposition43.lean`, they are in the default build, and `Proposition4_1_infiniteDimensional`
and `Proposition4_3_infiniteDimensional` both report `[propext, Classical.choice, Quot.sound]`.  The
promotion this row kept asking for was completed; the instruction is removed from `next_action`.
(b) `DavisKahan/Experimental/Frontier/Section4.lean` DOES NOT EXIST either, so the dated note
asserting that the infinite-dimensional form there "is `sorry` (`#print axioms` reaches `sorryAx`)"
describes a file that is gone; every Section 4 frontier declaration in the tree is axiom-clean.  Both
statements are left above as the historical record and are superseded by this paragraph.

**M33, 2026-08-09 (Claude Opus 5).  THE REAL-SCALAR AXIS IS CLOSED ON THIS ROW.**  `Proposition4_1_real` (`DavisKahan/Sources/DavisKahan1970/Section4Real.lean`) is the printed statement over a REAL Hilbert space of arbitrary dimension: for every orthogonal `W` with `W P_U = P_V W`, every approximation number of `(1 - W)|_U` is minimized by the real direct rotation.  No `[FiniteDimensional]`, no compactness.

THE ROUTE NOTE ON THE BLOCKER WAS WRONG ABOUT WHAT WAS NEEDED, AND THE CENSUS UNDERSTATED WHAT WAS ALREADY BUILT.  Both the `next_action` and the `scope_gap` here said the remedy was 'the complexification route rather than a reproof', implying machinery still to be written.  MEASURED 2026-08-09: `DavisKahan/OperatorIdeal/ComplexificationApproximation.lean` ALREADY PROVED, since before this tranche, that a real operator and its complexification have EQUAL approximation numbers (`approximationNumber_complexify`) and equal finite Ky Fan approximation gauges (`kyFanApproximationGauge_complexify`).  It was built for the real Ky Fan ideal work and was recorded on no Section 4 row.  The only genuinely missing ingredient was a real MINIMIZER, i.e. the real direct rotation, which is `DavisKahan/Geometry/Polar/DirectRotationReal.lean`.  With those two, the real Proposition 4.1 is three rewrites.
- **Next action:** Nothing outstanding at source scope.  Both scalar fields and arbitrary dimension are covered: `Proposition4_1_infiniteDimensional` (complex) and `Proposition4_1_real` (real), each without `[FiniteDimensional]` and without compactness, plus the finite `RCLike` singular-value forms.  Beyond source: the printed form A of Proposition 4.1 (there exist orthonormal `v_k` in `P H` with `angle(v_k, V v_k) >= theta_k`) is still not stated in any form; only form B, the singular-value minimization, is.

#### Corollary 4.1: UI-norm minimality of direct rotation displacement

- **Kind:** `corollary`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The direct rotation minimizes the norm of (1-V)P for every unitary-invariant norm.
- **Current Lean references:** `TauCeti.DavisKahanTheory.uiNorm_restrictedDisplacement_le`, `TauCeti.DavisKahanTheory.directRotation_minimizes_restrictedDisplacement_uiNorm`, `TauCeti.DavisKahan1970.Corollary4_1`, `TauCeti.DavisKahan1970.Corollary4_1_minimizer`, `TauCeti.DavisKahan.Experimental.Frontier.Section4.corollary4_1_restrictedDisplacement_idealGauge`, `TauCeti.DavisKahan1970.Corollary4_1_real`, `TauCeti.DavisKahan1970.Corollary4_1_opNorm_real`
- **Assessment:** Compiled without any angle restriction, for every unitarily invariant norm, over every RCLike field (finite dimension).  The earlier note conflating this row with Proposition 4.4 is resolved: the corollary concerns the restricted displacement and needs no angle hypothesis.

**SOURCE WRAPPER ADDED 2026-08-05**, in `DavisKahan/Sources/DavisKahan1970/Section4.lean` (namespace `TauCeti.DavisKahan1970`), so the facade can cite the paper's numbering directly.  The wrappers are `alias`es over the already-compiled general theorems, so they carry the exact statements.

**SECTION 4 SCOPE RE-AUDITED 2026-08-07 (Claude Opus 5).**  `DavisKahan/Sources/DavisKahan1970/Section4.lean` used to assert in its module docstring that the finite-dimensional forms "is the scope Section 4 is written at".  The transcription says otherwise: Section 4 opens "We shall make the hypotheses of Theorem 3.1 and Corollary 3.1 (leaving to the reader the modifications entailed in the absence of compactness)" and then states its propositions over infinite orthonormal sequences and infinite sums.  The docstring is corrected and the finite-dimensional aliases are now labelled as specializations.  Only the finite-dimensional `Corollary4_1` is aliased; the infinite-dimensional wrapper is a short derivation from `Proposition4_1_infiniteDimensional` and is recorded in `scope_gap` rather than claimed.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 9 is UPHELD.  The `scope_gap` said the
infinite-dimensional wrapper "is not yet stated" and the `next_action` said it "still lives under
Experimental"; both were false.  The declaration's NAMESPACE still contains `Experimental.Frontier`,
but its MODULE is `DavisKahan/Frontier/Section4.lean`, which is production and in the default build --
the same namespace-versus-location distinction already recorded on `DK-8.2-thm` for the 2026-08-06
promotion.  Verified here by elaboration and `#print axioms`, not by grep, and the declaration is now
listed on the row.

**M33, 2026-08-09 (Claude Opus 5).  THE REAL-SCALAR AXIS IS CLOSED ON THIS ROW.**  `Corollary4_1_real` (`DavisKahan/Sources/DavisKahan1970/Section4Real.lean`) is the ideal-gauge form over a REAL Hilbert space of arbitrary dimension: for every `KyFanDominantIdealFamily (k := R)` and every orthogonal `W` with `W P_U = P_V W`, the real direct rotation's restricted displacement is IN the ideal (concluded) and its gauge is least.  `Corollary4_1_opNorm_real` is the operator-norm specialization.

THE RECORDED OBSTRUCTION DOES NOT APPLY HERE.  The blocker's obstruction (1) says `KyFanDominantIdealFamily` is scalar-fixed and carries no `gauge_complexify`, so an endpoint stated over it 'cannot be transported as stated'.  True, and irrelevant on this row: the real statement is made over a REAL family and nothing about the family is transported.  What is transported is the approximation-number sequence, by `ComplexificationApproximation.approximationNumber_complexify`, and the certificate/bridge pair `RestrictedDisplacementApproximationDominance` / `restrictedDisplacement_idealGauge_le` is `RCLike`-generic, so a real certificate feeds a real family directly.
- **Next action:** Real scalars, through the complexification route rather than a reproof.  Nothing else outstanding at source scope: the finite every-UI-norm form (`Corollary4_1`, `directRotation_minimizes_restrictedDisplacement_uiNorm`) and the infinite-dimensional ideal-gauge form (`Frontier.Section4.corollary4_1_restrictedDisplacement_idealGauge`) are both compiled, axiom-clean and in the default build.

#### Proposition 4.2: Basis-angle square-sum extremality

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** For every orthonormal basis of P, the sum of squared displacement sines under V dominates the sum of squared principal sines.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.MathAhead.Section4.sum_displacementAngleSineSq_ge`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.displacementAngleSineSq_directRotation_eq_of_smul`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.norm_absoluteValue_apply_eq_norm_projection`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.norm_inner_competitor_le`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.sum_displacementAngleSineSq_ge_of_mem`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.tsum_displacementAngleSineSq_ge_of_mem`, `TauCeti.DavisKahan1970.displacementAngleSineSqR`, `TauCeti.DavisKahan1970.displacementAngleSineSq_ge_real`, `TauCeti.DavisKahan1970.sum_displacementAngleSineSq_ge_of_mem_real`, `TauCeti.DavisKahan1970.tsum_displacementAngleSineSq_ge_of_mem_real`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.sum_one_sub_sq_norm_absoluteValue_eq_sum_sq_principalSines`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.sum_displacementAngleSineSq_ge_sum_sq_principalSines`, `TauCeti.DavisKahan.Experimental.Frontier.Section4.proposition4_2_basisAngleSquareSum_principalSines`, `TauCeti.DavisKahan1970.norm_canonicalAbsoluteValueR_apply_eq_norm_projection`, `TauCeti.DavisKahan1970.sum_one_sub_sq_norm_canonicalAbsoluteValueR_eq_sum_sq_principalSines`, `TauCeti.DavisKahan1970.sum_displacementAngleSineSqR_ge_sum_sq_principalSines`
- **Assessment:** The finite orthonormal-basis displacement-energy extremality is compiled via the nuclear-norm specialization of the displacement-square majorization.

VERIFIED 2026-08-04: the nuclear-norm specialization for a finite orthonormal basis is compiled, axiom-clean and in the default build. The **infinite-dimensional** form is stated in `DavisKahan/Experimental/Frontier/Section4.lean` and is `sorry` (`#print axioms` reaches `sorryAx`). Proposition 4.1's infinite form *is* proved, in `Experimental/MathAhead/Section4/InfiniteProposition41.lean`, by a spectral-cutoff min-max argument -- that is the pattern to follow.

TRANSCRIPTION DEFECT FOUND AND FIXED 2026-08-04, in the frontier statement, not the paper. `Frontier/Section4.lean`'s `proposition4_2_basisAngleSquareSum` quantified over an arbitrary `Finset` of an arbitrary orthonormal family in `U`, with no completeness requirement. **In that form it is false**, and the singleton case is the natural first attack, so this was a trap. It had been audited as "sound" on 2026-07-30 along with ten sibling obligations.

The argument, which needs no computation: for a single unit `x` in `U`, the direct rotation scores `re <x, D x> = <C x, x>` with `C = |S|` the positive Halmos cosine, while an admissible competitor can score `re <x, W x> = norm (P_V x)`, and `norm (P_V x) = norm (C x)` because `C^2 = 1 - (P_U - P_V)^2`. Cauchy--Schwarz makes `<C x, x> < norm (C x)` **strictly** whenever `x` is not a principal vector, and the maximising `W` exists whenever `U` and `V` have equal finite dimension. So *every* non-principal unit vector of `U` refutes the singleton case. Concretely in C^4 at principal angles 0 and pi/3 with `x = (e1+e2)/sqrt 2`: competitor cost 3/8 < direct-rotation cost 7/16. Summing the same example over the full basis restores the inequality (1.025 < 1.125), which is the point -- **the statement is about total energy and no proper subfamily inherits it.**

The frontier statement now carries an `OrthonormalBasis` of `U`, which is what the source says, and the refutation of the old form is written into its docstring so it is not re-attempted. This is the second refuted transcription in Section 4 (see DK-4.4-prop); unlike that one it is a missing hypothesis rather than a wrong theorem, so the row keeps its status.

**A SECOND TRANSCRIPTION DEFECT FOUND AND FIXED 2026-08-05, in the same statement.** Adding the basis hypothesis was necessary and NOT sufficient. The once-repaired frontier form compared the competitor's cost against the *same sum evaluated at the direct rotation*, `sum_i cost D b_i`.  That is not the paper's right-hand side and the inequality is false in that form: the paper's right-hand side is the sum of squared principal sines, which is basis-independent, whereas `sum_i cost D b_i` is minimised at the principal basis and strictly larger elsewhere, because `re <b_i, D b_i> = <C b_i, b_i>` falls strictly below `norm (C b_i)` off the eigenvectors of `C`.

REFUTATION, computed and checked numerically.  In R^4 take `U = span(e1,e2)` and `V` at principal angles `0` and `arccos(1/10)`; the pair is acute (`norm (P_U - P_V) = sqrt(1 - 1/100) < 1`).  Rotate the basis of `U` by 0.2 radians.  The direct rotation costs 1.051417; an explicit admissible competitor -- an orthogonal 4x4 matrix `W` with `W P_U = P_V W`, the maximiser of `sum_i (re <b_i, W b_i>)^2` over the admissible class, obtained from a rank-one pencil -- costs 1.028237.  Both exceed the principal-sine sum 0.99, which is what Proposition 4.2 actually asserts, so the paper is fine and only the transcription was wrong.

**OBLIGATION (1) IS NOW DISCHARGED, at arbitrary Hilbert-space generality.** `sum_displacementAngleSineSq_ge` (`DavisKahan/Sources/DavisKahan1970/Section4BasisAngleEnergy.lean`, default build, axiom-clean): for every orthonormal basis of `U` and every unitary `W` with `W P_U = P_V W`, `sum_i (1 - (re <b_i, W b_i>)^2) >= sum_i (1 - norm (C b_i)^2)`.  The right-hand side is `dim U - tr((C|_U)^2)`, hence basis-free, and it is the sum of squared principal sines because the eigenvalues of `C|_U` are the principal cosines. `displacementAngleSineSq_directRotation_eq_of_smul` supplies the equality case on a `C`-eigenvector, so the bound is attained by the direct rotation on a principal basis and is the true minimum.

THE PROOF NEEDS NO MAJORIZATION -- two Cauchy--Schwarz steps.  `W x` lies in `V` and `norm (W x) = norm x`, so `abs <x, W x> <= norm (P_V x)`; and `norm (P_V x) = norm (C x)` for `x` in `U`, because `C^2 = P_U P_V P_U + P_Uperp P_Vperp P_Uperp` and the second summand kills a source vector.  Squaring termwise and summing is the whole argument.  No acuteness hypothesis is needed for the inequality; only the attainment statement mentions the direct rotation.

The frontier statement `proposition4_2_basisAngleSquareSum` is no longer `sorry`: it is grounded by `:=` on the production theorem, with the refutation of the previous form written into its docstring so it is not re-attempted a third time.

**OBLIGATION (2), THE SUMMABILITY CONVENTION, HAS NOTHING TO SETTLE -- 2026-08-05.** With the paper's basis-free right-hand side the estimate is **termwise**: `displacementAngleSineSq_ge` constrains one unit vector of `U` at a time.  So it uses neither completeness nor orthogonality, and survives passage to any subfamily -- which is exactly what fails for the wrong right-hand side `sum_i cost D b_i`, a genuine total statement.  Taking the sums in `ENNReal` then makes them unconditionally defined (divergence is a value, not a failure), and `ENNReal.tsum_le_tsum` lifts the termwise bound to an arbitrary index type with no hypothesis at all.

`sum_displacementAngleSineSq_ge_of_mem` (arbitrary finite subfamily) and `tsum_displacementAngleSineSq_ge_of_mem` (arbitrary index type, `ENNReal` sums) are both in the default build and axiom-clean, and the frontier statement `proposition4_2_basisAngleSquareSum_infinite` is grounded on the second by `:=`.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 12 is UPHELD in both of its parts, and
the status is LOWERED `compiled_exact` -> `compiled_specialization`.

(a) `DavisKahanTheory.directRotation_minimizes_sum_sq_basis_angles` IS NOT PROPOSITION 4.2 and has
been moved off this row onto `DK-4.3-prop`.  MEASURED 2026-08-09 by elaboration: it is
`sum_i ||U (b i) - b i||^2 <= sum_i ||W (b i) - b i||^2` over an `OrthonormalBasis (Fin n) K E` of the
WHOLE SPACE and the FULL displacement, i.e. a Frobenius statement and a consequence of Proposition 4.3.
Proposition 4.2 is about an orthonormal basis of `P H` and the displacement SINES.  The row's
"nuclear-norm specialization" gloss for it was also wrong: the norm involved is Frobenius.

(b) THE PRINTED RIGHT-HAND SIDE IS NOT COMPILED, and this is why the status moves.  What is proved is
`sum_i (1 - (re <b_i, W b_i>)^2) >= sum_i (1 - ||C b_i||^2)`.  The notes above argue -- in prose -- that
the right-hand side equals `dim U - tr((C|_U)^2)` and hence `sum_k sin^2 theta_k`.  That identification
is nowhere in the build: no lemma connects
`spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)` to the principal sines.  Until it
exists, `sum_displacementAngleSineSq_ge` is a true theorem about a quantity the census asserts, rather
than proves, to be the printed one.  Everything else recorded above -- the two refuted transcriptions,
the termwise proof, the `ENNReal` convention -- is unaffected and still correct.

**M33, 2026-08-09 (Claude Opus 5).  THE REAL-SCALAR AXIS IS CLOSED ON THIS ROW.**  The compiled inequality now holds over a REAL Hilbert space of arbitrary dimension, in all three shapes the complex row carries: termwise (`displacementAngleSineSq_ge_real`), over an arbitrary finite subfamily of unit vectors of `U` (`sum_displacementAngleSineSq_ge_of_mem_real`), and over an arbitrary index type with `ENNReal` sums (`tsum_displacementAngleSineSq_ge_of_mem_real`).  All in `DavisKahan/Sources/DavisKahan1970/Section4Real.lean`.  The proof is the complex termwise bound evaluated on the real copy, using `complexify_ofReal`, `inner_ofReal` and `ofReal.norm_map`; no functional calculus is involved on either side.

THE STATUS DOES NOT MOVE, and for a reason that has nothing to do with scalars: the printed RIGHT-HAND SIDE is still not identified.  The real form has exactly the same unidentified right-hand side `sum_i (1 - ||C_R b_i||^2)` as the complex one, so obligation (1) of the `next_action` is unchanged and applies over both fields.

**THE `sum sin^2 theta_k` IDENTIFICATION IS COMPILED OVER `C`, 2026-08-10 (Claude Opus 5, coordinator-verified).**  `sum_one_sub_sq_norm_absoluteValue_eq_sum_sq_principalSines` closes the M18 finding exactly as that adjudication stated it: no lemma connected `spectraOperatorAbsoluteValue` to the principal sines, and now one does.

**THE ROUTE WAS NOT THE RECORDED ONE, AND THE RECORDED ONE HIDES A TRAP.**  The handoff and the coordinator's brief both proposed `dim - trace(C^2)`.  What worked is TERMWISE PYTHAGORAS: `||C x|| = ||P_V x||` on `U` (already compiled) and `||P_Vperp x||^2 = 1 - ||P_V x||^2` for unit `x`.  THE TRAP: sorted decreasingly, `sin^2 theta` is the REVERSE of `1 - cos^2 theta`, so a TERMWISE cos-to-sin identity would have been FALSE -- only the SUMS agree.  A trace route would also have needed the eigenvalues of the compression `C|_U`, which nothing supplies.  Note also that `sum_i ||C b_i||^2 = trace(C* C)` holds for a basis of the WHOLE space; over a basis of `U` it is the trace of the COMPRESSION, which is what makes the trace route longer than it looks.

**THE SECTION 8 DICTIONARY DID NOT SUPPLY THIS, contrary to the coordinator's brief.**  `Section8SourceDictionary.lean` identifies ambient cosine-block approximation numbers with `principalCosines` POINTWISE (`approximationNumber_cosineBlock_eq_principalCosines` is literally `rfl` after two rewrites).  It contains NO sum, trace or Frobenius identity and nothing connecting a basis of a SUBSPACE to a singular-value sequence.  Following that pointer alone would not have closed the row.  What was missing was one reusable fact, now in `ForTauCeti/.../AngleGeometry.lean`: `singularValues_comp_subtype`, that restricting the domain to a subspace only removes zero padding.

**THE REAL IDENTIFICATION LANDED 2026-08-10 and COMPILED ON THE FIRST ATTEMPT** -- about twenty lines, no iteration.  `sum_one_sub_sq_norm_canonicalAbsoluteValueR_eq_sum_sq_principalSines` and `sum_displacementAngleSineSqR_ge_sum_sq_principalSines`.  The route mirrors `displacementAngleSineSq_ge_real` two declarations above: read `norm_absoluteValue_apply_eq_norm_projection` on the real copy through `complexify_canonicalAbsoluteValueR`, then `sum_sq_principalSines_eq_sum_one_sub_sq_norm_projection` applies at `K = R` unchanged and the `DavisKahan.projection` / `TauCeti.projection` spelling gap closes by `rfl`.  BOTH RECORDED TRAPS WERE AVOIDED RATHER THAN TESTED, and are now restated in a module-level docstring so they are not re-attempted a third time.
- **Next action:** Nothing outstanding.

#### Proposition 4.3: Squared displacement UI-norm minimality

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The direct rotation minimizes the UI norm of (1-V*) (1-V).
- **Current Lean references:** `TauCeti.DavisKahanTheory.directRotation_displacementSquare_kyFan`, `TauCeti.DavisKahanTheory.directRotation_displacementSquare_uiNorm`, `TauCeti.DavisKahanTheory.directRotation_minimizes_displacementSquare_uiNorm`, `TauCeti.DavisKahan1970.Proposition4_3`, `TauCeti.DavisKahan1970.Proposition4_3_kyFan`, `TauCeti.DavisKahan1970.Proposition4_3_minimizer`, `TauCeti.DavisKahan1970.Proposition4_3_infiniteDimensional`, `TauCeti.DavisKahanTheory.directRotation_minimizes_sum_sq_basis_angles`, `TauCeti.DavisKahan1970.Proposition4_3_real`
- **Assessment:** Compiled for every unitarily invariant norm over every RCLike field (finite dimension), via Fan-Hoffman majorization of the pinched competitor and two-block pinching contraction.

VERIFIED 2026-08-04: the finite-dimensional UI-norm minimality is compiled, axiom-clean and in the default build. The **infinite-dimensional** form is stated in `DavisKahan/Experimental/Frontier/Section4.lean` and is `sorry` (`#print axioms` reaches `sorryAx`). Proposition 4.1's infinite form *is* proved, in `Experimental/MathAhead/Section4/InfiniteProposition41.lean`, by a spectral-cutoff min-max argument -- that is the pattern to follow.

**A THIRD REFUTED TRANSCRIPTION IN SECTION 4, 2026-08-05 -- in the frontier, not the paper.** `Frontier/Section4.lean` stated the infinite-dimensional form as pointwise domination of the *individual* approximation numbers of the squared displacement, `a_n((1-D)*(1-D)) <= a_n((1-W)*(1-W))` for every `n`.  **That is false**, and the repository already contained the configuration that kills it: pointwise domination would imply the Ky Fan sums are dominated, hence Proposition 4.4, which this repository REFUTES (see DK-4.4-prop, `shortRotation_fullDisplacement_refuted`).  Same equal-angle multiplicity mixing.

COUNTEREXAMPLE, computed and checked.  In R^4 take `U = span(e1,e2)` and `V` at principal angles `pi/4, pi/4` (acute: `norm (P_U - P_V) = sin(pi/4) < 1`).  Let `W` carry `U` onto `V` by a quarter turn in the `V`-frame and `U-perp` onto `V-perp` by the identity; it is orthogonal with `W P_U = P_V W`.  Then `a_n(1-D) = (0.765367, 0.765367, 0.765367, 0.765367)` while `a_n(1-W) = (1.586707, 1.586707, 0.261052, 0.261052)`, so at `n = 2` the competitor is strictly smaller, and squaring preserves it: `0.585786` against `0.068148`.

**PROPOSITION 4.3 ITSELF IS UNTOUCHED.** Its Ky Fan sums of *squares* are `(0.586, 1.172, 1.757, 2.343)` for the direct rotation against `(2.518, 5.035, 5.103, 5.172)` for the competitor -- dominated at every `k`.  Sums of squares and sums behave differently, which is exactly why 4.3 survives while 4.4 does not.  The finite-dimensional theorems on this row are unaffected.

The frontier statement is now `proposition4_3_squaredDisplacement_kyFan`, at Ky Fan level -- what a unitarily invariant norm actually sees -- with the refutation of the pointwise form written into its docstring so it is not attempted a second time.

**PROVED 2026-08-05**, in `Experimental/MathAhead/Section4/InfiniteProposition43.lean`.  The finite-dimensional route (diagonalize, then Fan--Hoffman on the pinched competitor) does NOT survive: in infinite dimensions `2 - 2C` need not be compact and has no eigenvalue list.  The replacement chains

    kyFan_k(2 - 2C) = kyFan_k(D's block sum) <= kyFan_k(W's block sum)
                    = kyFan_k(pinch((1-W)*(1-W))) <= kyFan_k((1-W)*(1-W)),

reading the pinch through the isometry `H = U (+) U-perp`, feeding the middle step with Proposition 4.1 on `U` and on `U-perp`, and closing with the Fan--Hoffman pinching contraction `kyFanApproximationGauge_diagonalPart_le`.

TWO THINGS THAT TURNED OUT NOT TO BE EXTRA WORK.  (i) **Proposition 4.1 for the complementary pair is the same theorem.**  The canonical intertwiner `P_V P_U + P_Vperp P_Uperp` is symmetric under exchanging each subspace for its complement, so `spectraDirectRotation Uperp Vperp = spectraDirectRotation U V` on the nose (`spectraDirectRotation_orthogonal`) and acuteness is literally the same number; only the competitor's admissibility has to be transported, and that is one subtraction.  (ii) **The direct rotation's squared displacement is already block diagonal**, since `(1-D*)(1-D) = 2 - 2C` and `C` commutes with `P_U` -- so the first step of the chain is an equality, not an estimate.

ONE BRICK WAS MISSING AND IS NOW BUILT: `a_n(X*X) = a_n(X)^2`, in `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/GramSquare.lean`.  Proposition 4.1 dominates approximation numbers at the FIRST power, 4.3 is about the Gram operator of the displacement, and nothing else bridges them.  Its hard direction cannot be done by pointwise norm domination -- `norm(X*Xx) >= s norm(x)` on a subspace only gives `norm(Xx) >= (s/norm X) norm(x)`, the wrong power -- so the optimal subspace has to be spectral and the proof runs through the Gram spectral projections.  That lemma is also precisely why 4.3 survives while 4.4 does not: sums of SQUARES of the approximation numbers are dominated at every `k`, and the sums themselves are not.

The infinite form lives under `DavisKahan/Experimental`, so `lake build` does not guard it.  Promoting it is the remaining work on this row, together with the exact source wrapper.

**SOURCE WRAPPER ADDED 2026-08-05**, in `DavisKahan/Sources/DavisKahan1970/Section4.lean` (namespace `TauCeti.DavisKahan1970`), so the facade can cite the paper's numbering directly.  The wrappers are `alias`es over the already-compiled general theorems, so they carry the exact statements.

**SECTION 4 SCOPE RE-AUDITED 2026-08-07 (Claude Opus 5).**  `DavisKahan/Sources/DavisKahan1970/Section4.lean` used to assert in its module docstring that the finite-dimensional forms "is the scope Section 4 is written at".  The transcription says otherwise: Section 4 opens "We shall make the hypotheses of Theorem 3.1 and Corollary 3.1 (leaving to the reader the modifications entailed in the absence of compactness)" and then states its propositions over infinite orthonormal sequences and infinite sums.  The docstring is corrected and the finite-dimensional aliases are now labelled as specializations.  The infinite-dimensional form was already proved and build-guarded at `DavisKahan/MathAhead/Section4/InfiniteProposition43.lean`; it is now aliased as `Proposition4_3_infiniteDimensional`.  Elaborated signature: arbitrary complex Hilbert space, `IsAcute U V`, any unitary `W` carrying `U` onto `V`, concluding `kyFanApproximationGauge k ((1 - star U_direct) * (1 - U_direct)) <= kyFanApproximationGauge k ((1 - star W) * (1 - W))` at every level `k`.  Ky Fan level is the honest scope: pointwise singular-value domination would imply Proposition 4.4, which this repository refutes.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreements 10 and 11 are UPHELD; both are stale paths, verified 2026-08-09 by
listing the tree and by elaboration.  (a) `DavisKahan/Experimental/MathAhead/Section4/` DOES NOT
EXIST; the two infinite-dimensional modules are `DavisKahan/MathAhead/Section4/InfiniteProposition41.lean`
and `InfiniteProposition43.lean`, they are in the default build, and `Proposition4_1_infiniteDimensional`
and `Proposition4_3_infiniteDimensional` both report `[propext, Classical.choice, Quot.sound]`.  The
promotion this row kept asking for was completed; the instruction is removed from `next_action`.
(b) `DavisKahan/Experimental/Frontier/Section4.lean` DOES NOT EXIST either, so the dated note
asserting that the infinite-dimensional form there "is `sorry` (`#print axioms` reaches `sorryAx`)"
describes a file that is gone; every Section 4 frontier declaration in the tree is axiom-clean.  Both
statements are left above as the historical record and are superseded by this paragraph.

**M33, 2026-08-09 (Claude Opus 5).  THE REAL-SCALAR AXIS IS CLOSED ON THIS ROW.**  `Proposition4_3_real` (`DavisKahan/Sources/DavisKahan1970/Section4Real.lean`) is the Ky Fan statement over a REAL Hilbert space of arbitrary dimension: every Ky Fan sum of the approximation numbers of `(1 - W^T)(1 - W)` is minimized by the real direct rotation.  Transported by `ComplexificationApproximation.kyFanApproximationGauge_complexify`, which was already in the tree; see the M33 note on `DK-4.1-prop` for why no new analysis was required.  Ky Fan level remains the honest scope over `R` for the same reason as over `C`.
- **Next action:** One item, and it is not about scalars.  Take the step from Ky Fan domination to the printed 'every unitarily invariant norm' phrasing for the INFINITE-dimensional forms; the finite `Proposition4_3` already takes it, while `Proposition4_3_infiniteDimensional` and `Proposition4_3_real` stop at `kyFanApproximationGauge`.  Do NOT attempt pointwise approximation-number domination: it is false (notes), and it would contradict this repository's own refutation of Proposition 4.4.

#### Proposition 4.4: Real-space full displacement minimality below pi/3

- **Kind:** `proposition`
- **Status:** `refuted_as_transcribed`
- **Verification:** `proved_in_build`
- **Mathematics:** In a real Hilbert space, if the maximal angle is at most pi/3, the direct rotation minimizes every UI norm of 1-V.
- **Current Lean references:** `TauCeti.DavisKahanTheory.shortRotation_fullDisplacement_refuted`, `TauCeti.DavisKahanTheory.DavisKahanProposition4_4_Finite`, `TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite`
- **Assessment:** The transcribed claim is false: a compiled R^4 counterexample exhibits an acute pair with both principal angles pi/4 and a competitor unitary carrying P to Q whose full displacement 1-V has trace norm 2 sqrt 2, strictly below the direct rotation value 4 sqrt(2 - sqrt 2).  The competitor mixes the equal-angle multiplicity space (rotation angles 0 and pi/2), an obstruction available at every angle threshold; the same family refutes the closing conjecture of Davis 1958.  Operator-norm and squared-displacement consequences survive via 4.1/4.3.

**SOURCE-VERIFIED AGAINST THE FULL TRANSCRIPTION 2026-08-07 (Claude Opus 5).**  The refutation is INSIDE the printed scope, which matters because `refuted_as_transcribed` is the strongest claim in this census.  Proposition 4.4 is printed "in a real space `H`" with `Theta <= pi/3`; the counterexample is in `R^4` with both principal angles `pi/4 <= pi/3`, so it meets both printed hypotheses.  The printed proof reduces to the 2-by-2 blocks (`e = f = 0` because the space is real, then a `pi/3` trigonometric inequality on `mu_1 + mu_2`) and then sums over blocks -- which is exactly the invalid step this row already localizes at equation (4.3).  The paper itself notes the conclusion fails beyond `pi/3` by Example 4.1 and fails in complex space by Example 4.2, so the real-space and `pi/3` restrictions are deliberate and the counterexample is not exploiting an unintended reading.
- **Next action:** None outstanding.  The source re-audit is done: the printed Proposition 4.4 carries no hypothesis restricting the competitor class, excluding multiplicity mixing, or replacing the full displacement, so the refutation applies to the claim as printed.  The defect is localized to equation (4.3), whose derivation from (1.12) needs superadditivity of the Ky Fan sum across an orthogonal decomposition of the domain; range orthogonality fails.  The block-level claim the printed proof body establishes (each `||K Omega_k||_2` minimized at V=U, via the pi/3 trigonometry) remains true in the counterexample.  `not_davisKahanProposition4_4_Finite` now refutes the claim in its "every UI norm" form, instantiating N at `(RectangularUnitarilyInvariantSeminorm.kyFan 4).toSquare`.

### Section 5

#### Theorem 5.1: Banach-space Sylvester lower bound

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Under a norm bound on B and an inverse norm bound on A, AX-XB=C implies ||C|| >= delta ||X|| for any compatible operator norm.
- **Current Lean references:** `TauCeti.DavisKahan1970.bounded_sylvester_neumann_solution`, `TauCeti.DavisKahan1970.banach_sylvester_lower_bound`, `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_uiNorm`, `TauCeti.DavisKahan.Experimental.Frontier.RemainingSourceSurface.theorem5_1_banach_sylvester`
- **Assessment:** The repository has Neumann and ordered-gap engines, but no explicit audited source wrapper for this Banach-space theorem.

CLOSED 2026-08-04: `partial_or_wrapper_missing` -> `compiled_exact`. The previous next_action -- "Add the exact Banach-space statement and derive it from the geometric-series proof" -- had the derivation backwards, and that is why the row stayed open. **The geometric series is what produces a solution; it is not what bounds one.** From `A X = C + X B` and a bounded left inverse, `X = A^{-1} C + A^{-1} X B`, so `||X|| <= ||A^{-1}||(||C|| + rho ||X||) <= (rho+delta)^{-1}(||C|| + rho ||X||)`, and one multiplication by `rho + delta` cancels `rho ||X||` from both sides. That is the whole proof.

So the source statement needs **no inner product, no completeness, no self-adjointness and no Neumann series** -- which is exactly why every other Sylvester lower bound in this repository, all of them proved through coercivity or the spectral theorem, was the wrong thing to try to specialise. New foundation: `ForTauCeti/Analysis/Normed/Operator/SylvesterBoundedInverse.lean`, over Banach spaces and a `NontriviallyNormedField`.

The source's "for any compatible operator norm" clause is carried literally by `banach_sylvester_lower_bound_uiNorm`: it is stated for an arbitrary size function subject to exactly subadditivity and the two one-sided ideal bounds, which is also what a symmetric-norm-ideal gauge supplies, so the unitarily-invariant-norm reading of Theorem 5.1 is the same theorem. `banach_sylvester_lower_bound` is its operator-norm specialisation. Both are admission-free and resolve against `DavisKahan.All`.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 13, first half, is UPHELD:
`Frontier.RemainingSourceSurface.theorem5_1_banach_sylvester` -- the form carrying the paper's LITERAL
compatibility axiom, `CompatibleCrossOperatorNorm` plus a `BoundedLeftInverseData` at
`(gamma + delta)^{-1}` -- was proved, axiom-clean and in the default build while this row did not name
it.  Verified by elaboration 2026-08-09 and now listed.

Disagreement 13, second half, concerned inequality (5.1), which no row claimed.  It now has its own
row, `DK-5-hermitian-inequalities`.

TWO PRINTED REMARKS OF SECTION 5 REMAIN UNFORMALIZED, both about Theorem 5.1 itself and neither
previously recorded.  (1) "the roles of `A` and `B` are symmetrical, so the hypotheses upon them may be
interchanged" (transcription L1607) -- a one-line companion.  (2) The unbounded remark (L1648--1649):
"Although that theorem was stated for bounded operators `B` and `X`, its statement and proof encompass
the case where `A` is an unbounded operator with domain dense in `Y`".  Both compiled forms take `A`
bounded (`A : Y ->L[C] Y` and `A : Y ->L[K] Y`), so this is a printed claim about the theorem's own
scope that the formalization does not carry.
- **Next action:** Three items, none blocking.  (1) The unbounded-`A` scope the paper claims for Theorem 5.1 itself (transcription L1648--1649): restate the estimate with `A` a densely defined closed operator with a bounded left inverse, which is what the printed proof actually uses.  (2) The `A`/`B` interchange remark (L1607), a one-line `symm` companion.  (3) If a future consumer wants the bound with `BoundedInverseData` rather than a bare left inverse, `hA.left_inv` is the argument to pass; do not restate the estimate.

#### Section 5, inequalities (5.1) and (5.2): Square-norm and rank-corrected Sylvester inequalities

- **Kind:** `equation`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** For Hermitian A and B whose eigenvalues are pairwise at distance at least delta, C = AX - XB satisfies the square-norm bound (5.1); (5.2) is its trace-norm corollary with a sqrt(rank C) factor.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactSinTheta.paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.paperHilbertSchmidtEnergy_sylvester_le_of_pairwiseSpectrumGap`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.paperOperatorNorm_sylvester_le_of_pairwiseSpectrumGap`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.paperOperatorNorm_sylvester_real_le_of_pairwiseSpectrumGap`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.paperOperatorNorm_sylvester_le_finrank_range`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.sharp52_constant_one_too_small`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.sharp52_sylvester`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.sharp52_gap`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.sharp52_opNorm_X`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.sharp52_opNorm_C`
- **Assessment:** **M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  **ROW ADDED**, closing disagreement 13: inequality (5.1) is proved and no census row claimed it, which is exactly the under-reporting the census exists to prevent.

(5.1) IS COMPILED, AND MORE GENERALLY THAN PRINTED.  MEASURED 2026-08-09 by elaboration.  The printed inequality is `||C||_sq >= delta ||X||_sq` for HERMITIAN MATRICES `A`, `B`, possibly of different dimensions, with `delta <= |lambda - mu|` for every eigenvalue `lambda` of `A` and `mu` of `B`.  `paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap` proves it for self-adjoint CLOSED (hence possibly unbounded) operators on arbitrary complete complex inner product spaces, with `PairwiseSpectrumGap` as the hypothesis and Hilbert--Schmidt membership of `X` CONCLUDED rather than assumed; `..._real_...` is the same statement over real Hilbert spaces with the pairwise gap spelled directly over `realSpectrum`; `paperHilbertSchmidtEnergy_...` is the `ENNReal` energy form covering infinite defect energy.  All axiom-clean `[propext, Classical.choice, Quot.sound]` and all reached from `DavisKahan.All`.  The scalar axis is therefore CLOSED on this row -- unusually for this census -- so it carries no `real-scalar-infinite-dimensional-scope` blocker.

WHY THE ROW IS NOT `compiled_exact`.  Two further printed items of the same passage are absent.  (a) Inequality (5.2), `||C||_1 sqrt(rank C) >= delta ||X||_1`, which the source derives from (5.1) and attributes independently to G. W. Stewart III.  The nearest compiled brick is a `sqrt(dim)` bound, not a `sqrt(rank)` one.  (b) The source's own 2x2 witness that the constant 1 is too small in (5.2): `X = [[3,-3],[-3,1]]`, `A = diag(1,-1)`, `B = diag(0,2)`, `delta = 1`, where `delta ||X||_1 = 2 + sqrt 10 > ||AX - XB||_1 = 3 sqrt 2`.  Note that whether `rank C` in (5.2) can be replaced by a constant is the source's OWN open question and is not proof debt.

**(5.2) AND THE 2x2 WITNESS ARE COMPILED, 2026-08-10 (Claude Opus 5, coordinator-verified).**  `paperOperatorNorm_sylvester_le_of_pairwiseSpectrumGap` gives `delta * ||X|| <= ||C|| * sqrt r` from a rank bound `C.rank <= r`, with a `_real_` twin and a `finrank_range` form.  The sharpness calculation is compiled, not prose: `sharp52_sylvester`, `sharp52_gap`, `sharp52_opNorm_X`, `sharp52_opNorm_C`, and the punchline `sharp52_constant_one_too_small`.

**THIS ROW WAS STALE IN TWO WAYS, AND BOTH MATTERED.**  (i) The notes said `the nearest compiled brick is a sqrt(dim) bound, not a sqrt(rank) one`.  FALSE: `paperHilbertSchmidtNorm_le_sqrt_rank_mul_opNorm` (`Ideals/HilbertSchmidtFiniteRank.lean:119`, COORDINATOR-VERIFIED PRESENT) is a genuine `sqrt(rank)` bound and was already compiled, as were `opNorm_le_paperHilbertSchmidtNorm` and `isPaperHilbertSchmidt_of_rank_le`; the full derivation chain was already written TWICE, at `SineTheta/Theorem62.lean:205` and `:413`.  (ii) `next_action` said `at trace-norm scope`.  FALSE, and it contradicted a decision recorded in the docstring of the very module holding the brick.

**THE PAPER'S SUBSCRIPT 1 IS THE BOUND (OPERATOR) NORM, NOT A TRACE NORM, AND THE PAPER NEVER WRITES A SUBSCRIPT 2 -- IT WRITES `sq`.**  Determined three independent ways, and the coordinator re-derived the third.  (a) Transcription L544: `In particular, kappa_1 is equal to the bound norm of K, which we write ||K||_1`; L555-566 defines `||.||_sq` as Hilbert-Schmidt and (1.11) gives `||K||_nu = kappa_1 + ... + kappa_nu`.  (5.1) is printed with `_sq`, not `_2`.  (b) THE PAPER'S OWN ARITHMETIC SETTLES IT: for the witness, `C = [[3,3],[3,-3]]` has both singular values `3 sqrt 2`, and the paper records `||AX - XB||_1 = 3 sqrt 2` -- the OPERATOR norm; the trace norm would be `6 sqrt 2`.  Likewise `X = [[3,-3],[-3,1]]` has singular values `2 + sqrt 10` and `sqrt 10 - 2`, and the paper records `||X||_1 = 2 + sqrt 10`, not the trace norm `2 sqrt 10`.  (c) `Ideals/HilbertSchmidtFiniteRank.lean:11` already recorded it: `Davis and Kahan write the bound norm with a subscript one.`

CONSEQUENTLY THE RECORDED ROUTE WAS WRONG: it is NOT Cauchy-Schwarz between Schatten 1 and 2.  It is the two exact comparisons `kappa_1 <= sqrt(sum kappa^2)` and `sum_{k<rank} kappa_k^2 <= rank * kappa_1^2`, BOTH ALREADY COMPILED.
- **Next action:** Nothing outstanding.  The paper's subsequent open question about replacing rank C by a constant is not a completion obligation.

#### Theorem 5.2: Semibounded self-adjoint Sylvester theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** For A >= gamma+delta > gamma >= B, a bounded solution of AX=XB+C satisfies the sharp UI-norm inequality.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactSinTheta.directOrderedSylvesterEngine_lowerUpper`, `TauCeti.DavisKahan1970.unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`, `TauCeti.DavisKahan1970.Theorem5_2`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.davisKahan1970_sylvester_real`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.real_unbounded_sylvester_kyFan`
- **Assessment:** The completed Section 6 route contains the needed constant-one engines, while the exact source theorem alias is still in the full Part III repair campaign.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The ordered Sylvester engine and the unbounded interval/exterior UI-norm theorem are compiled and axiom-clean; an exact Theorem 5.2 wrapper is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**SOURCE WRAPPER ADDED 2026-08-05**: `Theorem5_2`, in `DavisKahan/Sources/DavisKahan1970/Section5.lean`, aliasing `directOrderedSylvesterEngine_lowerUpper`.  That engine is the printed theorem: `SemiboundedBelow A (c + delta)` and `SemiboundedAbove B c` are the source's ordering `A >= gamma + delta > gamma >= B`, `HasClosedSylvesterEquation A B X R` is `AX = XB + C`, and the conclusion `delta * N(X) <= N(R)` carries the sharp constant.  It is more general than the print on the ideal axis (arbitrary `KyFanDominantIdealFamily`, not a fixed UI norm) and admits unbounded closed self-adjoint operators.

THE ORDERED BRANCH IS NOT THE INTERVAL/EXTERIOR BRANCH.  `unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`, also on this row, carries a different separation hypothesis; the wrapper's docstring says so, and the two must not be substituted for one another.

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  FALSE POSITIVE, `scope_gap` removed.  `davisKahan1970_sylvester_real` (`DavisKahan/Sylvester/RealUnbounded.lean:77`) elaborates as an arbitrary real Hilbert-space, arbitrary `KyFanDominantIdealFamily ℝ`, UNBOUNDED (`ClosedOperator`) form of the full Theorem 5.2: self-adjoint `A`, `B`, `0 < delta`, `FormBoundedSylvesterGap A B delta`, `HasClosedSylvesterEquation A B X C`, `N.Mem C`, concluding `N.Mem X` and `delta * N.gauge X <= N.gauge C`.  No new proof was needed -- only the census entry.  `real_unbounded_sylvester_kyFan` is the per-Ky-Fan-level companion.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 14 is UPHELD: the row still carried
`blocked_by: ["real-scalar-infinite-dimensional-scope"]` while its own `scope_gap` had been cleared and
both real endpoints were already listed on it.  The blocker is REMOVED.

EVIDENCE, measured 2026-08-09 by elaboration.  `davisKahan1970_sylvester_real` is
`[InnerProductSpace R E] [InnerProductSpace R F] [CompleteSpace ...]` with NO `[FiniteDimensional]`,
over `KyFanDominantIdealFamily R`, with `A`, `B` self-adjoint `ClosedOperator`s, `FormBoundedSylvesterGap`
as the printed `A >= gamma + delta > gamma >= B`, and both ideal membership and the sharp
`delta * N.gauge X <= N.gauge C` concluded.  `real_unbounded_sylvester_kyFan` is the same at every Ky
Fan level.  That is printed Theorem 5.2 over a real Hilbert space of arbitrary dimension, so this row
is not part of the real-scalar gap the blocker describes.
- **Next action:** Nothing outstanding at source scope.  `S2-unbounded-scope` names Theorem 5.2 as one of its two halves; that prerequisite is now met, so the remaining work on the unbounded scope claim is the cutoff/Ky-Fan passage (`DK-6-appendix`) and the leakage lemma (`DK-6.3-lem`).

#### Lemma 5.1: Strong-cutoff convergence of singular values

- **Kind:** `lemma`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** If projections converge strongly to one, each singular value of K composed with the projection converges to the corresponding singular value of K.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactSinTheta.approximationSingularValue_comp_strongProjection_tendsto`, `TauCeti.DavisKahan1970.Lemma5_1`
- **Assessment:** The modern approximation-number theorem is stronger and scalar-generic.

**SOURCE WRAPPER ADDED 2026-08-05**: `Lemma5_1`, in `DavisKahan/Sources/DavisKahan1970/Section5.lean`.  The compiled statement is stronger than the printed one on two axes, and the wrapper's docstring says which: the index is an arbitrary filtered net rather than a sequence, and the scalar field is generic rather than complex.  The paper's lemma is the specialization to a sequence over the complex field.
- **Next action:** Nothing outstanding.  The source-numbered wrapper is in the default build and axiom-clean.

### Section 6

#### Lemma 6.1: Direct-sum UI-norm comparison and converse

- **Kind:** `lemma`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Two diagonal block inequalities imply the direct-sum inequality; under equisingularity of paired blocks the converse holds.
- **Current Lean references:** `TauCeti.DavisKahan1970.lemma6_1`, `TauCeti.DavisKahan1970.lemma6_1_converse`
- **Assessment:** Both directions are proved; the converse should be added to the exact audit manifest.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**STATUS RESTORED 2026-08-08 (Claude Opus 5): `compiled_specialization` -> `compiled_exact`; blocker `real-scalar-infinite-dimensional-scope` removed from this row.**  The 2026-08-07 scope_gap claim that 'every declaration is `InnerProductSpace ℂ` only' is FALSE at this HEAD: the mathematics was generalized to `RCLike` in commit 83e1b854, and both declarations on this row elaborate to

    {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
      [CompleteSpace E] [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜]

with no finite-dimensionality hypothesis.  `HasMinMaxLowerBoundEverywhere` has instances for both `ℝ` (`TauCeti.ApproximationNumber.hasMinMaxLowerBoundEverywhere_real`) and `ℂ`, so real infinite-dimensional Hilbert spaces are covered.  VERIFIED BY ELABORATION 2026-08-08 (`#check @TauCeti.DavisKahan1970.lemma6_1`, `lemma6_1_converse`) rather than by reading the file, per the method the blocker itself prescribes.  No code change was needed on this row -- only the audit record was stale.
- **Next action:** Harden the audit, not the mathematics.

#### Lemma 6.2: Reflection-pinch contraction

- **Kind:** `lemma`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The sum of the two diagonal projection blocks of an operator is no larger than the operator in every source unitary-invariant norm.
- **Current Lean references:** `TauCeti.DavisKahan1970.lemma6_2`
- **Assessment:** Part of the clean Section 6 surface.
- **Next action:** No mathematical gap.

#### Proposition 6.1: Symmetric sine theorem

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Two complementary source gap hypotheses give the full sine-angle inequality with perturbation H.
- **Current Lean references:** `TauCeti.DavisKahan1970.Proposition6_1`, `TauCeti.DavisKahan1970.RealSymmetricSinThetaProblem`, `TauCeti.DavisKahan1970.Proposition6_1_real`, `TauCeti.DavisKahan1970.Proposition6_1_real_kyFan`, `TauCeti.DavisKahan1970.Proposition6_1_real_sinTheta_singularValues`, `TauCeti.DavisKahan1970.Proposition6_1_real_sinTheta_eq_literalFullSinAngle`, `TauCeti.DavisKahan1970.Proposition6_1_real_representative`
- **Assessment:** Complex and real source forms are compiled.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**STATUS RESTORED 2026-08-08 (Claude Opus 5): `compiled_specialization` -> `compiled_exact`; blocker `real-scalar-infinite-dimensional-scope` removed from this row.**  The real-scalar form is now compiled, for an arbitrary real Hilbert space with no finite-dimensionality hypothesis: `DavisKahan/Sources/DavisKahan1970/SineTheta/SymmetricReal.lean`, surfaced as `TauCeti.DavisKahan1970.Proposition6_1_real`.  The proof MIRRORS the complex one step for step -- same two directed applications of the one-sided sine theorem, same Lemma 6.1 coupling on the scaled identity, same Lemma 6.2 contraction -- with exactly one substitution: `davisKahan1970_sylvester_complex` becomes `real_unbounded_sylvester_kyFan`.  No new mathematics was needed; `paperLemma61_all_kyFan`, `paperDiagonalPair_all_kyFan_le`, the ambient/subspace singular-value transport, and `PaperUnitaryInvariantNorm` were already `RCLike`-generic.

**How the conclusion avoids a real functional calculus.**  The complex row's conclusion is phrased through `paperSinAngleOperatorC`, i.e. `cfc Real.sin` of the operator angle, which is why the complex file cannot be generalized as written.  The real theorem is instead stated on `paperCrossSineSum U V`, and that this is the paper's whole-space `sin Theta` is COMPILED, not asserted:
* `Proposition6_1_real_sinTheta_singularValues` (from the `RCLike` `paperCrossSineSum_same_projectionDiff`) gives every source norm the same membership and value on `paperCrossSineSum U V` as on the projector difference `P_V - P_U`;
* `Proposition6_1_real_sinTheta_eq_literalFullSinAngle` matches its complete approximation-singular-value sequence to that of the repository's LITERAL real full sine angle `paperSourceFullSinR`;
* `Proposition6_1_real_representative` states the estimate for an ARBITRARY operator carrying that sequence, which is the precise sense in which only the source singular sequence matters.

The theorem's own statement mentions no complexification, no functional calculus, and no caller-supplied inequality.  Axiom audit on all five real declarations plus the structure: exactly `propext`, `Classical.choice`, `Quot.sound`.  Full `lake build` green (9487 jobs), plus the non-default `FinishTanTwoTheta` and `Challenge` libraries.
- **Next action:** No mathematical gap and no scope gap.

#### Theorem 6.1: Generalized sine theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** A lower frame bound on the trial map and interval/exterior separation give delta epsilon times any equisingular sine representative bounded by the residual.
- **Current Lean references:** `TauCeti.DavisKahan1970.Theorem6_1`, `TauCeti.DavisKahan1970.Theorem6_1_real`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`
- **Assessment:** This is the canonical source-general sine theorem.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  FALSE POSITIVE, restored to `compiled_exact`.  Theorem 6.1 has a real infinite-dimensional source theorem already: `Theorem6_1_real` elaborates over `[InnerProductSpace ℝ]`, `[CompleteSpace]`, no `[FiniteDimensional]`, and the common-domain and common-core unbounded variants `Theorem6_1_real_commonDomain` / `Theorem6_1_real_commonCore` do too.  The row's declaration list simply omitted them; the mathematics was never missing.

**M32, THE SECTION 6 SCALAR TRANCHE, 2026-08-09 (Claude Opus 5).**  THE `real-scalar-infinite-dimensional-scope` ENTRY IN `blocked_by` WAS STALE AND IS REMOVED.  The 2026-08-07 note above already recorded the false positive and restored the status, but the blocker was left on the row, so the blocker's own tally counted this row.  RE-MEASURED 2026-08-09 by elaborating the signature: `Theorem6_1_real` is `[InnerProductSpace ℝ]` on four spaces with `[CompleteSpace]` and NO `[FiniteDimensional]` anywhere, over `PaperRealTheorem61Data` and an arbitrary `PaperUnitaryInvariantNorm`, concluding `N.Mem S.operator ∧ gap * frameLowerBound * N.gauge S.operator ≤ N.gauge P.data.residual` -- membership CONCLUDED, constant intact.  `Theorem6_1_real_commonDomain` and `Theorem6_1_real_commonCore` likewise.  All axiom-clean (`[propext, Classical.choice, Quot.sound]`).  Nothing was proved for this row today; the row was already correct.
- **Next action:** No mathematical gap.

#### Theorem 6.2: Pairwise-gap square-norm sine theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Arbitrary pairwise spectral distance gives the sharp Hilbert–Schmidt/square-norm residual bound.
- **Current Lean references:** `TauCeti.DavisKahan1970.Theorem6_2`, `TauCeti.DavisKahan1970.Theorem6_2_real`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperTheorem62Data.operatorNorm_result_across_of_rank_le`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperRealTheorem62Data.operatorNorm_result_across_of_rank_le`
- **Assessment:** The defect-first pairwise tensor proof is compiled.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  FALSE POSITIVE, restored to `compiled_exact`.  Theorem 6.2 has a real infinite-dimensional source theorem already: `Theorem6_2_real` elaborates over `[InnerProductSpace ℝ]`, `[CompleteSpace]`, no `[FiniteDimensional]`, and the common-domain and common-core unbounded variants `Theorem6_2_real_commonDomain` / `Theorem6_2_real_commonCore` do too.  The row's declaration list simply omitted them; the mathematics was never missing.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 15 is UPHELD.  Theorem 6.2's printed
RANK VARIANT -- the source obtains `delta epsilon ||sin Theta_0||_1 <= ||R||_1 sqrt(rank R)` by using
(5.2) in place of (5.1) at the end of the proof (transcription L1920) -- is compiled and was not listed
here.  MEASURED 2026-08-09 by elaboration:
`PaperTheorem62Data.operatorNorm_result_across_of_rank_le (P) (S) (h : rank P.data.residual <= r) :
P.gap * P.frameLowerBound * ||S.operator|| <= ||P.data.residual|| * sqrt r`, over arbitrary complete
complex inner product spaces with no dimension hypothesis, axiom-clean, plus the real twin
`PaperRealTheorem62Data.operatorNorm_result_across_of_rank_le` with the identical statement over
`InnerProductSpace R`.  Both are now on the row.  Note that the general inequality (5.2) they answer to
is itself still absent as a Section 5 statement; that is tracked on `DK-5-hermitian-inequalities`.

**M32, THE SECTION 6 SCALAR TRANCHE, 2026-08-09 (Claude Opus 5).**  THE `real-scalar-infinite-dimensional-scope` ENTRY IN `blocked_by` WAS STALE AND IS REMOVED, for the same reason as on `DK-6.1-thm`.  RE-MEASURED 2026-08-09 by elaboration: `Theorem6_2_real` is `[InnerProductSpace ℝ]`, `[CompleteSpace]`, no `[FiniteDimensional]`, over `PaperRealTheorem62Data`, concluding `IsPaperHilbertSchmidt S.operator ∧ gap * frameLowerBound * paperHilbertSchmidtNorm S.operator ≤ paperHilbertSchmidtNorm P.source.R` -- square-norm membership CONCLUDED.  `Theorem6_2_real_commonDomain`, `Theorem6_2_real_commonCore` and the printed rank variant `PaperRealTheorem62Data.operatorNorm_result_across_of_rank_le` likewise.  All axiom-clean.  Nothing was proved for this row today.
- **Next action:** No mathematical gap.

#### Theorem 6.3: Generalized tangent theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** A strict inequality of source-coordinate Hilbert dimensions, the Rayleigh–Ritz residual condition, and a one-sided gap control a directed rectangular tangent representative defined from the singular values of E₀*F₁.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_all_kyFan_core`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem63DirectedTangent`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_all_kyFan_core_directedTangent`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal_directedTangent`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_of_formBounds_equalRank`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_equalRank_spectral`, `TauCeti.DavisKahan1970.Theorem6_3`, `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteTrial_real`, `TauCeti.DavisKahan1970.theorem63DirectedTangentReal`, `TauCeti.DavisKahan1970.exists_hasTheorem63DirectedTangentApproximationNumbersReal`, `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_infiniteTrial_source_ideal`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.hasTheorem63DirectedTangentApproximationNumbers_iff_infinite`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal_of_infiniteTrial`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_infiniteTrial_spectral_exists`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_infiniteTrial_of_formBounds`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.exists_hasTheorem63DirectedTangentApproximationNumbersInfinite`, `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm`, `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_spectral`
- **Assessment:** Bounded finite-source Theorem 6.3 proved axiom-clean in DavisKahan.TanTheta.Theorem63FiniteSource (theorem6_3_all_kyFan_core, theorem6_3_generalizedTanTheta_source_ideal); promoted out of Scratch.

**A HYPOTHESIS WITH NO PRODUCER, FOUND AND DISCHARGED 2026-08-05.** Every compiled form of Theorem 6.3 quantified over a `tanTheta0` satisfying `HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0`, and a grep for *producers* rather than consumers showed that nothing anywhere in the repository ever constructed one.  The compiled theorem was therefore a conditional whose antecedent had no witness -- strictly weaker than the printed theorem, which takes the tangent representative for granted.  The row said `proved_in_build`, which was true of the declarations and misleading about the mathematics.

THE WITNESS.  `ExactTanTheta.theorem63DirectedTangent`: diagonal in the right singular basis of the directed sine block, with entries `tan (arcsin s_i)`.  `hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent` proves it has the required approximation numbers.  Two facts do the work: the singular values of a diagonal operator with antitone nonnegative diagonal are the diagonal itself, and `t |-> t / sqrt(1 - t^2)` is increasing on `[0,1)`, so the entries inherit the sine block's ordering.  Post-composition with the inclusion `Z -> H` does not move approximation singular values (`approximationSingularValue_subtypeL_comp`), and above `dim Z` both sides vanish (`approximationSingularValue_eq_zero_of_finrank_le`).

**NO NEW HYPOTHESIS WAS NEEDED.** Finiteness of the entries requires `s_i < 1`, and `theorem63_singularValues_sine_lt_one` -- already in the file -- derives exactly that from the source gap, i.e. from the same `hCompressionUpper` and `hUnwantedLower` Theorem 6.3 assumes.  So `theorem6_3_all_kyFan_core_directedTangent` and `theorem6_3_generalizedTanTheta_source_ideal_directedTangent` carry precisely the printed hypotheses.  Both are in the default build and axiom-clean, and are wrapped in `RemainingSourceSurface` as `theorem6_3_all_kyFan_core_unconditional` and `theorem6_3_generalizedTanTheta_source_ideal_unconditional`.

**THE DIMENSION HYPOTHESIS WAS REDUNDANT, 2026-08-05.** `theorem6_3_generalizedTanTheta_of_formBounds` binds `_hStrictDimension : Module.rank Z < Module.rank V` and never uses it, and the Ky Fan core never took it at all.  The printed inequality does one job -- under the paper's separability convention it forces the trial coordinate space to be finite-dimensional -- and here that is an explicit instance.  `theorem6_3_generalizedTanTheta_of_formBounds_equalRank` and `theorem6_3_generalizedTanTheta_equalRank_spectral` state the theorem without it, which is what the equal-rank Section 2 tangent theorem needs; see S2-tan-theta.

**RE-ASSESSED 2026-08-09 (Claude Opus 5).  THE ROW DOES NOT MOVE, AND HERE IS THE MEASUREMENT BEHIND THAT.**

`theorem6_3_generalizedTanTheta_source_ideal_directedTangent` was elaborated in full.  It is the printed theorem: `Module.rank C Z < Module.rank C V` (the paper's strict source-coordinate dimension inequality, present rather than dropped), `spectrum R (theorem63Compression T Z) subset Icc beta alpha`, `spectrum R (T.restrict ...) subset Ici (alpha + delta)`, arbitrary `KyFanDominantIdealFamily`, conclusion `delta * N.gauge (theorem63DirectedTangent Z V) <= N.gauge (theorem63Residual T Z)` with the representative constructed.  Axiom-clean, in the default build.

Two things keep it from `compiled_exact`.

1. It carries `[FiniteDimensional C Z]` as an INSTANCE, in addition to the printed rank inequality.  Under the paper's standing separability convention the two are equivalent (every infinite-dimensional closed subspace of a separable space has the same Hilbert dimension, so `rank Z < rank V` forces `Z` finite-dimensional), but that convention is not a hypothesis of the Lean statement, so the compiled theorem is neither implied by nor implies the printed one without it.  The honest reading is a specialization.  This is not idle: the directed tangent representative `theorem63DirectedTangent` itself requires the instance, so it cannot simply be dropped -- at arbitrary trial dimension the representative is only exhibited existentially (`theorem6_3_infiniteTrial_*`, `theorem6_3_unbounded_infiniteTrial_*`).
2. Complex scalars only, now recorded in `blocked_by` and `scope_gap` like its Section 6 siblings.

The Appendix obligation this row's `next_action` deferred to S2-unbounded-scope IS now discharged for the single-angle tangent, at unbounded ambient and arbitrary trial dimension; see DK-6-appendix.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 16 is UPHELD: the row omitted
`TauCeti.DavisKahan1970.Theorem6_3`, which is the literal source surface and is `[RCLike]`, so the
`real-scalar-infinite-dimensional-scope` blocker was only half true on this row.  Verified 2026-08-09
by elaboration; the declaration is added and `scope_gap` now says which half is real.

**M32, THE SECTION 6 SCALAR TRANCHE, 2026-08-09 (Claude Opus 5).**  **THE REAL-SCALAR AXIS IS CLOSED AT EVERY TRIAL DIMENSION, AND HALF OF IT WAS ALREADY CLOSED AND UNRECORDED ON THIS ROW.**

ALREADY PRESENT, MISSING FROM THIS ROW: `theorem6_3_all_kyFan_core_infiniteTrial_real` (`Sources/DavisKahan1970/DirectedReal.lean`) is the Theorem 6.3 Ky Fan core over `InnerProductSpace ℝ` with the printed form hypotheses (`T` self-adjoint, `T.Reduces V`, compression form bound `alpha`, `Vᗮ` form lower bound `alpha + delta`), no finite-dimensionality anywhere, concluding `delta * Σ_{n<k} tan (arcsin a_n(sineBlockReal Z V)) ≤ kyFan_k (residualReal T Z)`.  It was listed only on `S2-tan-theta`.

PROVED TODAY: the trial-dimension restriction on the real endpoint is removed.  `tanTheta_directed_paperUINorm_real_infinite` needed `¬ FiniteDimensional ℝ Z` because the only representative constructor available was `ApproximationNumber.exists_approximationNumber_eq_of_antitone`, which builds an operator with a prescribed antitone sequence only on an infinite-dimensional space.  On a finite-dimensional real trial space the representative is instead written down: `theorem63DirectedTangentReal` is `diagOp (stdOrthonormalBasis ℝ Z) (tan ∘ arcsin ∘ a_·(sineBlockReal Z V))`, included into the ambient space.  `TauCeti.singularValues_diagOp` is already `RCLike`, so the diagonal IS the singular sequence; above `finrank ℝ Z` both sequences vanish for rank reasons (`approximationSingularValue_eq_zero_of_finrank_le_real`); and the entries are finite because the source gap forces `a_n < 1` (`approximationSingularValue_sineBlock_lt_one_infiniteTrial_real`).  NO ORTHONORMAL BASIS ADAPTED TO THE SINE BLOCK IS NEEDED -- any orthonormal basis of `Z` works, because only the singular values are prescribed.  `exists_hasTheorem63DirectedTangentApproximationNumbersReal` then covers every closed real trial subspace by case split, and `tanTheta_directed_paperUINorm_real` is Theorem 6.3 over a real Hilbert space of arbitrary dimension, arbitrary closed real trial subspace, every source `PaperUnitaryInvariantNorm`, tangent representative EXHIBITED and its membership CONCLUDED.  `tanTheta_directed_paperUINorm_real_infinite` is now a one-line specialization of it.  All axiom-clean.

WHAT THE REAL ENDPOINT DOES NOT MATCH IN THE COMPLEX ONE, stated so nobody has to rediscover it: the complex `theorem6_3_generalizedTanTheta_source_ideal_directedTangent` quantifies over an arbitrary `KyFanDominantIdealFamily (𝕜 := ℂ)`, the real one over `PaperUnitaryInvariantNorm`.  That is the class the paper itself states the theorem for, and the transport is deliberately at the finite Ky Fan level precisely because `KyFanDominantIdealFamily` instances cannot be compared across scalar fields; it is a difference in the norm abstraction, not in scope or in the constant.  The real endpoint also drops the printed strict rank inequality `rank Z < rank V`, which is a weakening of hypotheses, not of conclusion.

**TRIAL-DIMENSION AXIS CLOSED 2026-08-09 (Claude Opus 5, coordinator-verified).**  See `scope_gap` for the two measurements that collapsed it.  The short version: the finite and infinite tangent predicates are definitionally equal (`Iff.rfl`, now in the build) and the printed strict-dimension hypothesis was already bound as `_hStrictDimension` and never used.  The mission expected a cardinal argument and needed none.

THIS ROW'S OWN `scope_gap` PREVIOUSLY SAID THE GAP WAS `the finite-dimensional trial-space INSTANCE ... and nothing else`, while its very next sentence recorded that `theorem6_3_infiniteTrial_spectral_exists` and `theorem6_3_infiniteTrial_of_formBounds` drop the restriction entirely.  The gap was already closed by declarations in this same repository that were cross-listed only on `S2-tan-theta`.  This was a BOOKKEEPING gap, not a mathematical one, and it is a concrete instance of the documented `probe_census_declarations` blind spot: a row's declaration list being incomplete is invisible to every gate.  Those declarations are now listed here as well.

ALSO RECORDED, operational: the census and frontier gate scripts shell out to Lean, so running them concurrently with `lake build` fabricates missing-`.olean` failures (`EXIT=2`/`EXIT=1` on a clean tree).  Sequence build then gates in one job.

**CORRECTION TO THIS ROW'S OWN PREVIOUS `scope_gap`, which the coordinator wrote and which was WRONG.**  It named `PaperUnitaryInvariantNorm.prefixGauge_le_of_all_kyFan_le_hetero` as `exactly the bridge the real endpoint uses`.  MEASURED 2026-08-10: the real endpoint `tanTheta_directed_paperUINorm_real` NEVER INVOKES IT -- it uses `N.mul_gauge_le_of_all_mul_kyFan_le` (`DirectedReal.lean:448`, coordinator-verified by reading the line).  The `_hetero` variant is for operators with DIFFERENT CODOMAINS, whereas here both operands are `Z ->L E`; and it could not have been the bridge anyway, being unscaled (no `delta`) and concluding only a `prefixGauge` inequality rather than membership plus the gauge bound.

ALSO CORRECTED: `theorem6_3_all_kyFan_core` is the FINITE-TRIAL core and carries `[FiniteDimensional C Z]` (`Theorem63FiniteSource.lean:787`, coordinator-verified).  Building the complex paper-norm endpoint on it would have produced a statement STRICTLY WEAKER than the real one it was meant to match.  The arbitrary-trial core `theorem6_3_all_kyFan_core_infiniteTrial` is the right one.
- **Next action:** Nothing outstanding.

### Section 6 appendix

#### Appendix to Section 6, equations (6.7)–(6.11): Unbounded-operator passage

- **Kind:** `appendix`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** Domain invariance, bounded residual, spectral cutoffs, and limiting arguments extend the single-angle theorems to unbounded self-adjoint operators.
- **Current Lean references:** `TauCeti.DavisKahan1970.Theorem6_1_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_commonCore`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists`, `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteData_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.perturbation_isSymmetric`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.forward_all_kyFan`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.reverse_all_kyFan`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.symmetric_all_kyFan`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.ofBounded`, `TauCeti.DavisKahan1970.CommonDomainSymmetricSinThetaProblem`, `TauCeti.DavisKahan1970.Proposition6_1_commonDomain`, `TauCeti.DavisKahan1970.Proposition6_1_commonDomain_kyFan`, `TauCeti.DavisKahan1970.Proposition6_1_commonDomain_ofBounded`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_real`
- **Assessment:** Common-domain and graph-core source forms are compiled. This does not by itself ground the Appendix's full arbitrary-unitarily-invariant tan-theta cutoff/Fan passage, which remains a separate frontier obligation.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  The sine half of this row was a false positive; the tangent half was not.  Recorded in `scope_gap` rather than by flipping the status, because a row that mixes a covered and an uncovered passage is not honestly described by either label alone.

**SHARED ADAPTER LANDED 2026-08-07 (Claude Opus 5).**  `complexifySubmoduleEquiv (Z : Submodule ℝ E) : RealComplexification ↥Z ≃ₗᵢ[ℂ] ↥(complexifySubmodule Z)` (`DavisKahan/SpectralTheory/Complexification/SubmoduleEquiv.lean`, axiom-clean, in the default build) removes the first load-bearing obstruction to the real lift on this row.  The problem it solves: a real configuration carries an operator on `↥Z`, complexifying lands on `RealComplexification ↥Z`, and every complex theorem here speaks about `↥(complexifySubmodule Z)`.  Canonically the same space, NOT definitionally equal.  `re`/`im` are preserved on the nose, so conjugating a compression or residual through it is mechanical.  It is deliberately an isometric equivalence rather than a definitional identification, because the ideal/norm layer only needs equality of approximation singular values and unitary conjugation gives exactly that.  The unbounded appendix reuses the same adapter for trial subspaces, on top of the existing closed-operator transports in `DavisKahan/SpectralTheory/ClosedOperator/Complexification.lean`.  Do not rewrite the cutoff argument.

**UNBOUNDED DOUBLE-ANGLE MACHINERY LANDED 2026-08-08 (Claude Opus 5).  THE ROW STATUS IS UNCHANGED; THE ENDPOINT IS NOT PROVED.**

The Appendix says the unbounded extension of the Section 7 double-angle theorems is analogous to the single-angle passage, but never writes it out.  Three new `ForTauCeti` modules now carry the part of that passage that is genuinely new, under `ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/`.  They are deliberately NOT listed in `lean_declarations`: rows are probed against the `DavisKahan.All` closure, and a `ForTauCeti` name there would make the row report `partially_in_build`.

* `ReflectionBlocks.lean` -- the block algebra of the reducing reflection `Z = 2Q - 1` relative to a trial subspace `U`, expressed through the existing `Submodule.diagonalPart` / `Submodule.offDiagonalPart` pinches rather than four separate blocks.  From `Z * Z = 1` alone: `D^2 + S^2 = 1` and `D S + S D = 0`, which blockwise are `D_0^2 + G* G = 1`, `D_1^2 + G G* = 1` and `D_1 G = G D_0`.  Also the parity lemmas (`D` even, `S` odd for `U + U-perp`) and the vector Pythagoras identity `||D x||^2 + ||S x||^2 = ||x||^2` on `U` and on `U-perp`, which needs only that `Z` is isometric.  This is the reflection-side sibling of the rectangular `G* G = 4 M (1 - M)` in `DoubleAngle/Gram.lean`; the module docstring records the kinship.

* `UnboundedReflection.lean` -- the domain half and the engine.  Domain preservation of `Z` plus `ReducesSubspace A U` gives `D` and `S` preserving `D(A)`, i.e. exactly `D_0 D(A_0) subset D(A_0)`, `G D(A_0) subset D(A_1)`, `G* D(A_1) subset D(A_0)`, `D_1 D(A_1) subset D(A_1)`, with no separate argument per block.  On top of that, the domain-correct branch-free form of equation (7.6):

      A (S x) - S (A x) = C (B x) - B (C x)   for every x in D(A),

  which on `D(A_0)` is `A_1 G - G A_0 = -D_1 B - B D_0`.  Every term is defined by the domain inclusions; no global `|A|`, no indefinite closed form, and no sign of `cos 2 theta` is selected anywhere -- the sign is inside `C x`.  Both block forms and the ambient form are proved.

* `UnboundedPole.lean` -- the pole-exclusion theorem with an explicit constant.  With `A` reduced by `U`, quadratic form at most `a` on `U` and at least `b` on `U-perp`, `B` bounded and fully off-diagonal (`H_0 = H_1 = 0`), and `delta = b - a > 0`:

      ||S x|| <= (2 ||B|| / sqrt(delta^2 + 4 ||B||^2)) ||x||    and    (delta / sqrt(delta^2 + 4 ||B||^2)) ||x|| <= ||C x||

  for `x` in `U`.  So `|cos 2 Theta_0| >= kappa > 0` with `kappa` explicit: **the pole at `sin 2 Theta_0 = 1` is excluded as a theorem, before `tan 2 Theta_0` is defined**, matching the pattern the repository already uses for `tan Theta`.  The proof pairs (7.6) with the matching left vector at a near-maximiser of `||S .||` inside a bounded spectral cutoff of `A`; the only unbounded contribution is `<A x, r>`, and it is controlled because `A x` is fixed by the cutoff, so `r` is tested against its cutoff component, whose size `sqrt(m^2 - q^2)` is purely geometric.  The near-maximisation error is sent to zero at frozen cutoff level, and only then is the cutoff level sent to infinity.

**WHAT IS NOT PROVED, AND WHERE IT STOPS.**  (i) The general Ky Fan inequality `delta * sum_{k<=nu} |tan 2 theta_k| <= 2 ||B||_nu` and the arbitrary-unitarily-invariant-norm endpoint `delta N(tan 2 Theta_0) <= 2 N(B)` are NOT proved.  (ii) The cutoff data is packaged as the structure `TauCeti.BoundedCutoff A U tau` and is consumed, not constructed: the instance from `specProjection hA (Icc (-T) a)` for a self-adjoint `LinearPMap` -- whose four fields are `specProjection_mem_domain`, `norm_sub_smul_le_of_mem_specRange`, `specProjection_apply_domain` and the `proj_inter` product with `specProjection hA (Iic a)` -- is left to be built, together with `tendsto_specProjection_Icc` for the hypothesis of the `_of_tendsto` forms.  Until that is done the pole-exclusion theorem is conditional on a family of cutoffs being supplied.

**THE CUTOFF IS NOW CONSTRUCTED, 2026-08-09 (Claude Opus 5).  THE POLE-EXCLUSION THEOREM IS UNCONDITIONAL.  ROW STATUS STILL UNCHANGED.**

The gap recorded above -- `TauCeti.BoundedCutoff` was consumed but never produced -- is closed.  `ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/SpectralCutoff.lean` builds the Appendix's family `1_{[-tau, alpha]}(A_0)` out of the spectral measure that already existed in `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure{,/Construction}.lean`:

* `specProjection_eq_starProjection_specRange` -- the spectral projection IS the Mathlib `starProjection` onto its range, which is what lets the block algebra (written against `Submodule.starProjection`) talk about spectral subspaces at all.
* `reducesSubspace_specRange` -- a spectral subspace reduces the operator: both projections preserve `D(A)` and both summands are invariant.  Built from `specProjection_mem_domain` and `apply_mem_specRange`.
* `spectralCutoff hA c (hcT : |c| <= T) : BoundedCutoff A (specRange hA (Iic c)) T` with `toProj = specProjection hA (Icc (-T) c)`.  Its range lies in `specRange hA (Iic c)` because spectral projections multiply (`proj_inter` at `Icc (-T) c subset Iic c`); it lies in `D(A)` by `mem_domain_of_mem_specRange_of_bounded`; `A` is bounded by `T` on it by `norm_sub_smul_le_of_mem_specRange` at `c = 0`; and it is invariant by `specProjection_apply_domain`.
* `tendsto_spectralCutoff` -- `1_{[-(|c|+n), c]}(A) x -> x` for `x` in the spectral subspace, from `tendsto_specProjection_Icc` composed with `n |-> |c| + n` and the product rule `proj (Icc (-T) T) * proj (Iic c) = proj (Icc (-T) c)` for `c <= T`.

Consequently `norm_offDiagonalPart_apply_le_specRange` and `diagonalBlockBound_mul_le_norm_diagonalPart_apply_specRange` state, **with no cutoff hypothesis of any kind**: for `A` self-adjoint, `U = 1_{(-inf, c]}(A)`, quadratic form at most `a` on `U` and at least `b` on `U-perp`, `B` bounded and fully off-diagonal, and `Z` a self-adjoint involution commuting with `A + B` on `D(A)`,

    ||sin 2 Theta_0 x|| <= (2 ||B|| / sqrt(delta^2 + 4 ||B||^2)) ||x||    and    (delta / sqrt(delta^2 + 4 ||B||^2)) ||x|| <= ||cos 2 Theta_0 x||

for every `x` in `U`, `delta = b - a`.  All axiom-clean.

**PIECE 2 (THE KY FAN AND UI-NORM ENDPOINT) IS STILL OPEN, AND IT CANNOT LIVE IN `ForTauCeti`.**  Its two ingredients are on the wrong side of the import firewall: `ApproximateLeadingSingularFamily` and `exists_approximateLeadingSingularFamily` are in `DavisKahan/Sources/DavisKahan1970/Ideals/SpectralSelection.lean`, and the paired-inner-product-to-Ky-Fan step used by the bounded proof is likewise in `DavisKahan`.  A `ForTauCeti` module may not import either.  The unbounded endpoint therefore belongs in `DavisKahan`, consuming the `ForTauCeti` engine -- the same shape as the bounded `TanTwoThetaBranchFreeInfinite.lean`.

One structural fact found while scoping it, which removes the approximation lemma the plan expected to need: the adjoint of the compressed cross block `X = S . Omega` is `Omega . S`, so the family's `adjoint_residual` field, `||X* y_k - q_k x_k|| <= eps`, IS the leakage bound `||Omega r_k|| <= eps` with `r_k = S y_k - q_k x_k` (using `Omega x_k = x_k`).  No simultaneous near-maximiser lemma has to be built: one `eps` drives both the geometric error and the error beside `A_0`, and freezing `tau` first and then sending `eps -> 0` is the whole device.

**THE OPERATOR-NORM CASE OF THE UNBOUNDED RESIDUAL `tan 2Theta` THEOREM IS PROVED, 2026-08-09 (Claude Opus 5).  THE ARBITRARY-UI-NORM CASE IS NOT.  ROW STATUS UNCHANGED.**

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedResidual.lean` (in `DavisKahan.Sources.DavisKahan1970.All`, hence in the default build) proves, for `A` self-adjoint and possibly unbounded, `X_0 = 1_{(-inf, c]}(A)`, form bounds `A <= a` on `X_0` and `A >= b` on `X_1`, `delta = b - a > 0`, and `B` bounded and FULLY OFF-DIAGONAL (the source's `H_0 = H_1 = 0`, so `B` is the residual `R`):

    delta * ||sin 2Theta_0 x|| <= 2 ||B|| * ||cos 2Theta_0 x||    and    kappa ||x|| <= ||cos 2Theta_0 x||,   kappa = delta / sqrt(delta^2 + 4 ||B||^2),

for every `x` in `X_0`; equivalently `delta |tan 2 theta| <= 2 ||B||`.  Sharp constant `2`, residual on the right (not the perturbation form `2 N(E)`), and branch-free STRUCTURALLY -- the sign of `cos 2 theta` is inside the diagonal block and only its magnitude survives, so no acute/obtuse selection occurs anywhere.  This is the Ky Fan prefix at `nu = 1`.  Axiom-clean.

The tangent inequality is the pole-exclusion bound rearranged: `c^2 + s^2 = n^2` with `s <= (2 beta / D) n`, `D^2 = delta^2 + 4 beta^2`, is EQUIVALENT to `delta s <= 2 beta c`.  So the pole exclusion already contained the operator-norm theorem.

**WHY `nu >= 2` DID NOT LAND, PRECISELY.**  The bounded infinite-dimensional argument (`DoubleAngle/TanTwoThetaApproximatePair.lean` + `Sources/DavisKahan1970/TanTwoThetaBranchFreeInfinite.lean`) cannot be transferred, and the reason is visible in its own error constant:

    approximatePairErrorCoefficient A H T = (||A|| + ||H||) * (3 + 2 ||T||)

-- proportional to `||A||`.  With `A` unbounded that coefficient is infinite.  Tracing where `||A||` enters: the per-pair estimate pairs equation (7.6) at the family's right vector `x_k` against the family's LEFT vector `y_k`, and the left residual `e_k = S x_k - q_k y_k` produces the term `<A (S x_k), e_k>`.  Now `S x_k` lies in `X_1`, where `A` is bounded BELOW by `b` and not above, and no cutoff of `A_0` controls it.  The cutoff device that works on the `A_0` side has no counterpart on the `A_1` side.

The repair, which I believe is correct but did not build: never use the family's left vectors.  Take `y_k := S x_k / ||S x_k||` EXACTLY, as the Appendix's own construction does, so that `<A (S x_k), y_k> = ||S x_k|| <A y_k, y_k>` with no residual at all and the `A_1` side is reached only through the form bound.  The family is then used for three things only: orthonormality of the right vectors, the composite `X* X x_k approx q_k^2 x_k` from its two residual fields, and the value `q_k = a_k(X)`.

Two consequences the plan for steps 6--8 did not account for, both real:

* The plan's `<D_0 x_j, D_0 x_k> = d_k^2 delta_{jk}` holds EXACTLY only for exact singular vectors, which need not exist.  With an approximate family the `D_0` Gram carries an error too, since `<D_0 x_j, D_0 x_k> = delta_{jk} - <G x_j, G x_k>`, and the `y_k` Gram error is the same quantity.
* That error is `O(eps) / (q_j q_k)`.  The structure field `selected_large` gives only `q_k > eps`, so the naive bound is `O(1/eps)` -- it does NOT tend to zero.  Splitting the indices at `q_k >= sqrt(eps)` is also insufficient (error `O(1)`).  The split must be at `q_k >= eps^(1/3)`: retained indices then carry Gram error `O(eps^(1/3))`, and dropped indices contribute at most `f(q_k) <= eps^(1/3)/kappa` to the left-hand side, so both halves vanish together.

After that the remaining chain is: the finite-dimensional Gram/polar correction on the `D_1` side (uniform because `d_k >= kappa`), two applications of `sum_abs_le_kyFanApproximationGauge_of_orthonormal`, then `eps -> 0` at frozen `tau`, then `tau -> infinity` via DK-5.1-lem.

**THE APPENDIX TANGENT CUTOFF / FAN PASSAGE IS PROVED, 2026-08-09 (Claude Opus 5, auditing external commit `fd91e376`).  THE ROW STATUS STILL DOES NOT MOVE, AND THE REASONS ARE ENUMERATED BELOW.**

The standing `next_action` on this row -- "complete the arbitrary-ideal tangent cutoff/Fan passage" -- is discharged for the single-angle tangent.  `DavisKahan/TanTheta/Theorem63UnboundedInfiniteTrial.lean` (in `DavisKahan.TanTheta.All`, hence the default build) proves, all three axiom-clean and all elaborated here rather than inferred from their names:

* `theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing` -- closed unbounded self-adjoint ambient operator (`DKClosedOperator`), **arbitrary complete trial subspace `Z` with no finite-dimensionality and no compactness hypothesis**, arbitrary `KyFanDominantIdealFamily`, the printed reducing-subspace hypotheses (`hVdom`, `hVcomm`, the form lower bound `hUnwanted` on `V-perp`), and the tangent representative EXHIBITED rather than assumed;
* `theorem6_3_unbounded_infiniteTrial_ideal_of_reducing` -- the same with a supplied representative;
* `theorem6_3_unbounded_infiniteTrial_ideal_exists` -- the spectral-gap specialization at `V = specSubspace (Iic alpha)`.

This is the exact combination the Appendix advertises ("The tan theta theorem requires more care because we must both use the technique of Theorem 5.2 and allow for noncompact Theta"): unbounded ambient AND noncompact angle.  The previously compiled endpoints `theorem6_3_unbounded_ideal(_directedTangent)(_of_reducing)` all carry `[FiniteDimensional C Z]`, so they covered only the compact half.

IT PARALLELS THE BOUNDED FAMILY RATHER THAN SUBSUMING IT.  The new module re-proves the finite-projector passage one level up, over `Theorem63TrialData` (its own `exists_finiteDimensional_superset_compression_leak`, `approximationSingularValue_sineBlock_lt_one_infiniteData`, `all_kyFan_core_of_formBounds_infinite`), and instantiates that at `UnboundedTrialBlock`.  The bounded-ambient endpoints in `Theorem63InfiniteTrial.lean` (`theorem6_3_all_kyFan_core_infiniteTrial`, `theorem6_3_infiniteTrial_spectral_exists`, `_of_formBounds_exists`) are NOT re-derived from it and remain separate proofs over `T : H ->L[C] H`.  Mathematically the abstract core covers both; as source code the two coexist, and unifying them is a cleanup, not mathematics.

**WHAT IS STILL MISSING IN THIS APPENDIX, MEASURED 2026-08-09.**

1. **Equations (6.7)--(6.11) are not formalized as displayed identities.**  The compiled endpoint is proved by a DIFFERENT route: min--max localization plus almost-invariant spectral-band enlargement (`ForTauCeti BorelCalculus/AlmostInvariant`), with the leakage comparison `kyFan_k(residual F) <= kyFan_k(residual Z) + k*eps`.  The paper's own route is the nu-projector `Pi` from (1.13), the spectral cutoff `Omega(tau)`, the enlarged projector `Upsilon_tau`, the two selection inequalities (6.7) and (6.8), the truncated Sylvester display (6.10) and the Gram estimate (6.11).  Nothing in the repository carries those numbers.  (1.13) itself is no longer the obstacle: as of 2026-08-09 its supremum form is compiled as `TauCeti.DavisKahan1970.equation1_13_reSum`, together with the approximate attaining family `ApproximationNumber.exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner` that is what actually produces the paper's `Pi` (see S1-ui-norms); what remains missing here is the displayed chain (6.7)--(6.11) built on top of it.  The theorem is proved; the paper's displayed chain is not.
2. **Proposition 6.1 has no common-domain or unbounded form.**  The Appendix says explicitly that "the hypotheses of Proposition 6.1 and Theorem 6.1 may be relaxed similarly".  Theorem 6.1 has been relaxed (`Theorem6_1_commonDomain`, `Theorem6_1_commonCore`, and their real companions).  Proposition 6.1 has not: its only source-facing input record is `PaperSymmetricSinThetaProblem` (`Sources/DavisKahan1970/SineTheta/Symmetric.lean`), whose fields are `A B : E ->L[C] E` -- bounded operators -- with both gap hypotheses phrased through `ClosedOperator.ofBounded`.  There is no `PaperCommonDomainSymmetric...` analogue.
3. **The tangent passage is complex-scalar only**, which is the row's recorded `scope_gap` and is unchanged: the three new endpoints are `InnerProductSpace C`.  The SINE portion of the appendix does have real forms, so the row is not uniformly complex-only, which is why the gap is recorded here rather than by flipping the status.
4. **The unbounded double-angle endpoint remains at nu = 1.**  See the entries above: `tanTwoTheta_unbounded_residual_opNorm` is the operator norm, residual form; the Ky Fan `nu >= 2` and arbitrary-unitarily-invariant-norm cases are open, with the obstruction (the `A_1`-side cutoff that does not exist) recorded above.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 17 is UPHELD: the status
`compiled_specialization` was right and its principal recorded reason was not.  The bounded Ritz
compression is now stated in `scope_gap` and promoted to item (a) of `next_action`.

**M32, THE SECTION 6 SCALAR TRANCHE, 2026-08-09 (Claude Opus 5).**  **THE SCALAR BLOCKER STAYS ON THIS ROW.  THE TANGENT HALF OF THE APPENDIX IS STILL COMPLEX ONLY, AND HERE IS THE MEASURED ENTRY POINT FOR THE LIFT.**

The SINE half is confirmed real again by elaboration today: `Theorem6_1_real_commonDomain`, `Theorem6_1_real_commonCore`, `Theorem6_2_real_commonDomain`, `Theorem6_2_real_commonCore` are all `[InnerProductSpace ℝ]`, `[CompleteSpace]`, free of `[FiniteDimensional]`, membership concluded, all axiom-clean.  The TANGENT half -- `theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing`, `theorem6_3_unbounded_infiniteTrial_ideal_of_reducing`, `theorem6_3_unbounded_infiniteTrial_ideal_exists` -- is `InnerProductSpace ℂ` throughout and was NOT lifted.

WHAT THE LIFT ACTUALLY NEEDS, measured by reading the proof rather than guessing.  The Appendix Ky Fan passage `Theorem63TrialData.all_kyFan_core_of_formBounds_infinite` -- the cutoff/Fan argument itself -- consumes ONLY bounded data: the four fields of `Theorem63TrialData Z V` (`action : Z →L[ℂ] H`, `compression : Z →L[ℂ] Z`, `residual : Z →L[ℂ] H`, and the block identity), the form bound `hMupper` on `compression`, and the crossed form bound `hcross` on `action`.  The unbounded operator appears in exactly one place, `crossed_lower_of_reducing`, which manufactures `hcross` from the reducing hypotheses.  So the real lift decomposes into four independent pieces, none of which touches the cutoff argument:
  (i) a real `Theorem63TrialDataReal Z V` with the same four bounded fields over `ℝ`;
  (ii) its complexification to `Theorem63TrialData (complexifySubmodule Z) (complexifySubmodule V)`, conjugating `Z →L[ℝ] Z` and `Z →L[ℝ] E` through `complexifySubmoduleEquiv Z` -- the same adapter and the same two transports (`theorem63DirectedSineBlock_complexify_equiv`, `theorem63Residual_complexify_equiv`) that `Sources/DavisKahan1970/DirectedReal.lean` already performs for the bounded ambient case, generalized from `theorem63Compression T Z` to an arbitrary bounded compression field;
  (iii) the two form-bound transports, for which the bounded case already has `re_inner_compressOperator_le` and `le_re_inner_of_mem_complexifySubmodule`;
  (iv) a real `UnboundedTrialBlockReal` over a real `ClosedOperator`, its `ofUnbounded` instance, and a real `crossed_lower_of_reducing`.  Only (iv) is genuinely new closed-operator work; `DavisKahan/SpectralTheory/ClosedOperator/Complexification.lean` already complexifies a real closed operator and its domain.
The endpoint should be stated at `PaperUnitaryInvariantNorm` scope and the transport done at the finite Ky Fan level, for the reason recorded on `DK-6.3-thm` and `S2-tan-theta`: `KyFanDominantIdealFamily` instances cannot be compared across scalar fields.

**ITEMS (c) AND (d) DISCHARGED, 2026-08-11 (Claude Opus 5, coordinator-verified).**  Item (d) required no work -- it had been done on 2026-08-09 and both `scope_gap` and `next_action` went on advertising it.  Item (c) is new: `Proposition6_1_commonDomain`.

**FOUR RECORDED CLAIMS ON THIS ROW WERE WRONG, all in the direction of overstating the work.**  (i) `the endpoint belongs at PaperUnitaryInvariantNorm scope rather than over KyFanDominantIdealFamily` -- FALSE as landed: it is over `KyFanDominantIdealFamily R`, and nothing is compared across fields, only approximation numbers cross.  (ii) `the work is a real Theorem63TrialData, plus its complexification, plus a real crossed_lower_of_reducing` -- NO real duplicates were ever written: `Theorem63TrialData` (`Theorem63TrialData.lean:67`), `Theorem63TrialData.ofUnbounded`, `UnboundedTrialBlock` and `crossed_lower_of_reducing` (`Theorem63Unbounded.lean:120`) all sit inside `section ScalarGeneric` with `[RCLike K]`, so the real instances ARE those declarations at `K = R`.  (iii) `the four bounded fields of Theorem63TrialData` -- it has SIX fields, three operators (`action`, `compression`, `residual`) and three properties.  (iv) `lean_declarations` omitted two real endpoints that exist, are axiom-clean and are in the default build; both are now listed.

REUSE, not rebuilding: the paper's argument was untouched for item (c).  Both one-sided applications already ran through `UnboundedSinThetaData`, `unbounded_adjoint_residual_block_identity` and `davisKahan1970_sylvester_complex` -- closed-operator theorems that the BOUNDED file reached only via `ClosedOperator.ofBounded`.  Lemma 6.1, the Lemma 6.2 contraction and the literal `sin Theta` identification are reused verbatim.  DELIBERATELY NOT DONE: rewriting `Symmetric.lean` to derive the bounded endpoint from the new one -- a real convergence cleanup, but it churns `SymmetricReal.lean` and the `FullSineTheta` surface for no mathematical gain.
- **Next action:** Items (a), (b) and (e) only -- see `scope_gap`.  ITEMS (c) AND (d) ARE BOTH DISCHARGED and have been struck: (d) was already done on 2026-08-09 and this field went on listing it for two days; (c) landed 2026-08-11 as `Proposition6_1_commonDomain`.  Item (b) should NOT be dispatched as a routine mission -- see the measured obstruction on `S2-unbounded-scope`.  Optionally, a REAL common-domain Proposition 6.1, which does not yet exist.

#### Lemma 6.3: Finite-rank near-maximizer leakage estimate

- **Kind:** `lemma`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** A nearly Ky-Fan-optimal finite-rank compression has small off-block trace norm.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage`, `TauCeti.DavisKahan.Experimental.Frontier.Section6Appendix.lemma6_3_singularValue_leakage`, `TauCeti.DavisKahan.Experimental.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage_of_energySplit`, `TauCeti.DavisKahan.Experimental.Frontier.Section6Appendix.paperHilbertSchmidtEnergy_domain_projection_add_real`, `TauCeti.DavisKahan.Experimental.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage_real`, `TauCeti.DavisKahan.Experimental.Frontier.Section6Appendix.lemma6_3_singularValue_leakage_real`
- **Assessment:** The surrounding approximation-number infrastructure exists, but no exact source declaration was found.

CORRECTED 2026-08-04: the row listed no declarations. The frontier manifest maps it to node `s6-lemma6-3-approx`, whose declaration lives in `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean` -- inside the default build despite the `Experimental.Frontier` namespace. It resolves and is axiom-clean (`#print axioms`).

STATUS CORRECTED 2026-08-07 (Fable 5): `partial_or_wrapper_missing` -> `compiled_exact`.  The next_action ('state and prove the source lemma') predates the 2026-08-04 correction that located the declaration; the lemma IS stated and proved, in the default build, axiom-clean, in BOTH the source's forms: `lemma6_3_approximationNumber_leakage` (near-Ky-Fan-optimal prefix square energy forces off-block operator norm below eta, with the source-faithful block hypothesis K P = Q K P -- the module docstring documents why the earlier K P = Q K stating was wrong) and the finite-dimensional singular-value specialization `lemma6_3_singularValue_leakage`.  The compiled statement generalizes the source only by not assuming K compact (the rank hypotheses on the projections carry the finiteness), which is scope-widening, not scope-narrowing.

**M32, THE SECTION 6 SCALAR TRANCHE, 2026-08-09 (Claude Opus 5).**  **THE REAL-SCALAR AXIS IS CLOSED, BY PROOF, AND THE ROUTE WAS NOT THE ONE THE BLOCKER PREDICTED.**  The blocker's standing ROUTE note says a real wrapper 'should go through' the complexification route 'rather than by reproving over `RCLike`, since several proofs use the complex continuous functional calculus essentially'.  MEASURED for this lemma: the proof uses no functional calculus at all.  Of its eight supporting declarations, seven are scalar generic verbatim -- they consume only `approximationSingularValue`, `paperHilbertSchmidtEnergy_eq_sum_range_of_rank_le`, `approximationNumber_comp_le_norm_mul` and `starProjection_norm_le`, all of which are already `RCLike`.  Exactly ONE step was complex-only: the Pythagorean splitting `paperHilbertSchmidtEnergy_domain_projection_add`, and only because the column-energy bridge `paperHilbertSchmidtEnergy_eq_basisEnergy` (`Ideals/HilbertSchmidtBasis.lean`) is stated over `ℂ`.

So `Section6AppendixLeakage.lean` was generalized to `RCLike 𝕜` (`approximationEnergy` and its five lemmas, plus the new engine `lemma6_3_approximationNumber_leakage_of_energySplit`, which takes the splitting for the one operator that needs it as a hypothesis), and only the splitting was transported.  `Section6AppendixLeakageReal.lean` proves `paperHilbertSchmidtEnergy_domain_projection_add_real` by reading the complex splitting at `complexify L` and `complexifySubmodule P`: complexification preserves the whole approximation singular-value sequence hence the energy (`paperHilbertSchmidtEnergy_complexify`), the orthogonal projection onto a complexified real subspace is the complexification of the real one (`starProjection_complexifySubmodule`), and complexification carries `1 - P` to `1 - complexify P`.  `lemma6_3_approximationNumber_leakage_real` and the finite-dimensional `lemma6_3_singularValue_leakage_real` are then the ℝ instances of the same engine the ℂ forms use, word for word the complex statements with `InnerProductSpace ℂ` replaced by `InnerProductSpace ℝ`, at arbitrary dimension.  Both axiom-clean (`[propext, Classical.choice, Quot.sound]`), both in the default build.
- **Next action:** Nothing outstanding.  The lemma is reusable for cutoff passages exactly as the audit hoped, and now over real as well as complex scalars.

### Section 7

#### Section 7, equations (7.1)–(7.5): Reflection proof of the sine double-angle theorem

- **Kind:** `proof_package`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Reflect the perturbation by 2P-1, identify U squared and sin(2 Theta), and reduce the result to the symmetric sine theorem.
- **Current Lean references:** `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_eq_perturbationDefect`, `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_le_two_mul`, `TauCeti.DavisKahan1970.sinTwoTheta_reflectedOverlap_norm`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative`
- **Assessment:** The reflection identities and finite theorem exist; the exact full proof package is under repair.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The reflection-defect identity and the gap-hypothesis residual theorem are compiled and axiom-clean; a source wrapper preserving both conclusions is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

ROW WAS STALE; CORRECTED 2026-08-07 (Fable 5).  The requested 'source wrapper preserving both residual and perturbation conclusions' has existed since the SinTwoTheta facade landed (DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean, `namespace TauCeti.DavisKahan1970`): the mirror-defect identities of the reflection proof (equations (7.1)-(7.3): `sinTwoTheta_mirrorDefect_eq_perturbationDefect`, `_le_two_mul`, and the gauge form), the double-angle identification (7.4)-(7.5) (`sinTwoTheta_reflectedOverlap_norm`), and BOTH conclusions at source-general scope -- arbitrary complete Hilbert space, unbounded closed self-adjoint operator, arbitrary Ky-Fan-dominant ideal family, representative freedom: `unbounded_sinTwoTheta_uiNorm_representative` (perturbation form, sharp factor two) and `unbounded_sinTwoTheta_residual_uiNorm_representative` (residual form, constant one).  All resolve from `DavisKahan.All` and are axiom-clean (verified by elaborator probe 2026-08-07).

**M37, 2026-08-09 (Claude Opus 5).  STALE BLOCKER ENTRY REMOVED.**  The 2026-08-07 correction on this row already recorded that the requested source wrapper exists and that the row's `next_action` is 'Nothing outstanding for the reflection proof package'; the `blocked_by` reference to `exact-source-wrappers` was simply not removed with it.  Re-measured 2026-08-09 by elaborating all five declarations against `DavisKahan.All`: every one resolves, including both conclusions at source-general scope (`unbounded_sinTwoTheta_uiNorm_representative`, sharp factor two, and `unbounded_sinTwoTheta_residual_uiNorm_representative`, constant one).  The blocker is retired; its text is preserved on `S1-block-residual`.
- **Next action:** Nothing outstanding for the reflection proof package.

#### Section 7, equation (7.6) and following argument: Singular-vector proof of the tangent double-angle theorem

- **Kind:** `proof_package`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The off-diagonal block equation and paired singular vectors yield Ky Fan and UI-norm bounds for tan(2 Theta).
- **Current Lean references:** `TauCeti.DavisKahan1970.tanTwoTheta_uiNorm`, `TauCeti.DavisKahan1970.tanTwoTheta_kyFan`, `TauCeti.DavisKahan1970.tanTwoTheta_uiIdeal_infinite`, `TauCeti.DavisKahan1970.tanTwoTheta_kyFan_infinite`, `TauCeti.DavisKahan1970.tanTwoTheta_sharp_opNorm`, `TauCeti.DavisKahan1970.tanTwoTheta_spectral_repulsion`, `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_residual_opNorm`, `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_residual_div`
- **Assessment:** The operator-norm theorem is compiled in finite dimensions; the arbitrary UI-norm singular-vector argument remains uncertified.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The off-diagonal weighted-sine tangent bound is compiled and axiom-clean; the exact source norm scope and the infinite-dimensional approximation passage are absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

ROW WAS STALE; CORRECTED 2026-08-07 (Fable 5).  The requested 'exact source norm scope and infinite-dimensional approximation passage' have existed since the TanTwoTheta facade landed (DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean): `tanTwoTheta_uiNorm` is equation (7.6) at the source norm scope -- every rectangular unitarily invariant norm, proved by the paper's paired-singular-vector argument -- and `tanTwoTheta_uiIdeal_infinite` / `tanTwoTheta_kyFan_infinite` are the infinite-dimensional sharp ideal forms via compression to the finite carrier (the paper's own passage), with `tanTwoTheta_sharp_opNorm` the pole-free sharp subspace theorem carrying the Section 8 acute branch and `tanTwoTheta_spectral_repulsion` the branch-keeping mechanism.  The facade's docstring records the audited boundary: the sharp infinite-dimensional ideal form requires a finite-dimensional invariant subspace (principal angles attained), the unbounded companions cover genuine spectral subspaces at the extended-cosine denominator, and the UNRESTRICTED sharp infinite-dimensional statement is excluded as refuted (the genuine unbounded Sylvester equation has a nonzero commutator defect; `doubleAngleTangent_sylvesterEquation` carries it explicitly).  Excluding an unsupported statement is completing the surface, not a gap.  All declarations resolve from `DavisKahan.All` and are axiom-clean (elaborator probe 2026-08-07).

**UNBOUNDED COMPANION, 2026-08-08 (Claude Opus 5).**  The branch-free unbounded form of equation (7.6) -- `A (S x) - S (A x) = C (B x) - B (C x)` on `D(A)`, for `S` and `C` the odd and even blocks of the reducing reflection -- and an explicit pole-exclusion bound `|cos 2 Theta_0| >= delta / sqrt(delta^2 + 4 ||B||^2)` now exist in `ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/{ReflectionBlocks,UnboundedReflection,UnboundedPole}.lean`.  They are the unbounded, residual-form analogue of this row's argument and are recorded on `DK-6-appendix`; the Ky Fan and unitarily-invariant-norm endpoint for the unbounded case is still open, so nothing on this row changes.

**OPERATOR-NORM UNBOUNDED RESIDUAL COMPANION, 2026-08-09 (Claude Opus 5).**  `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_residual_opNorm` and `..._div` (`Sources/DavisKahan1970/TanTwoThetaUnboundedResidual.lean`) give the operator-norm case of this row's theorem for UNBOUNDED self-adjoint `A`, in residual form with the sharp constant `2` and structural branch-freeness, together with the explicit pole exclusion `|cos 2 Theta_0| >= delta / sqrt(delta^2 + 4 ||B||^2)`.  The arbitrary-UI-norm (Ky Fan `nu >= 2`) case in the unbounded setting is still open; the obstruction is recorded on `DK-6-appendix`.  Nothing on this row changes: the bounded results here are unaffected.

**M30 REFLECTION REALIZATION 2026-08-09 (GPT-5.6 Sol).**  The dimension-free branch-free version of the printed Section 7 argument is now explicit in `DavisKahan/DoubleAngle/ReflectionTangentKyFan.lean` and `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean`.  It works with approximate singular families of the actual rectangular tangent corner and signed-cosine polar isometries, so principal angles may cross `pi/4`.  The source realization proves the lower residual corner first and obtains the upper orientation by adjoint invariance with no additional factor two.

**M37, 2026-08-09 (Claude Opus 5).  STALE BLOCKER ENTRY REMOVED.**  As on `DK-7-sin2-proof`, the 2026-08-07 correction had already recorded that equation (7.6) is compiled at the source norm scope (`tanTwoTheta_uiNorm`, by the paper's paired-singular-vector argument) with the infinite-dimensional sharp ideal forms beside it, and had set `next_action` to 'Nothing outstanding at the source's own scope'; only the `blocked_by` entry was left behind.  Re-measured 2026-08-09 by elaboration against `DavisKahan.All`: all eight declarations resolve.  The blocker is retired; its text is preserved on `S1-block-residual`.
- **Next action:** Nothing outstanding at the source's own scope.  The facade docstring records the deliberate exclusions (finite-carrier condition for the sharp ideal form; refuted unrestricted statement).

### Section 8

#### Theorem 8.1: Branch selection and spectral repulsion

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Under tan(2 Theta) hypotheses, the closed quarter-angle condition is equivalent to the selected spectral ordering; a canonical reducing subspace exists, is unique, and satisfies the operator, ordered-eigenvalue and every-symmetric-gauge repulsion inequalities on both blocks.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch`, `TauCeti.DavisKahan1970.Section8.theorem8_1_eq_canonicalBranch_of_maximalAngle_le`, `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn`, `TauCeti.DavisKahan1970.Section8.Theorem81Conclusion`, `TauCeti.DavisKahan1970.Section8.canonicalLowBranch`, `TauCeti.DavisKahan.realSpectrum_add_offDiagonal_subset_exterior_of_form_gap`, `TauCeti.DavisKahanExt.re_inner_le_of_mem_boundedSelfAdjointSpectralSubspace_Iic`, `TauCeti.DavisKahanExt.le_re_inner_of_mem_boundedSelfAdjointSpectralSubspace_Iic_orthogonal`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.theorem8_1_upperCompressionRepulsion_canonicalBranch`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.theorem8_1_lowerCompressionRepulsion_canonicalBranch`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSandwichApproximation_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSandwichApproximation_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_angle_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_angle_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperWeightedWeakMajorization_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerWeightedWeakMajorization_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_source`, `TauCeti.singularValues_adjoint_sandwich_weaklyMajorized`, `TauCeti.approximationNumber_adjoint_sandwich_weaklyMajorized`, `TauCeti.DavisKahan1970.Section8.approximationNumber_eq_eigenvalues_of_isPositive`, `TauCeti.DavisKahan1970.Section8.approximationNumber_upperBlockShift_eq_zero_of_le`, `TauCeti.DavisKahan1970.Section8.approximationNumber_lowerBlockShift_eq_zero_of_le`, `TauCeti.DavisKahan1970.Section8.approximationNumber_cosineBlock_eq_principalCosines`, `TauCeti.DavisKahan1970.Section8.approximationNumber_lowerCosineBlock_eq_principalCosines`, `TauCeti.DavisKahan1970.Section8.norm_cosineBlock_eq_principalCosines_zero`, `TauCeti.DavisKahan1970.Section8.norm_lowerCosineBlock_eq_principalCosines_zero`, `TauCeti.DavisKahan1970.Section8.cos_arccos_approximationNumber_cosineBlock`, `TauCeti.DavisKahan1970.Section8.maximalAngle_le_pi_div_six_iff`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_of_rotatedBlockData`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData`, `TauCeti.DavisKahan1970.Section8.Theorem81ConclusionReal`, `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch_real`, `TauCeti.DavisKahan1970.Section8.theorem8_1_eq_of_maximalAngle_le_real`, `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn_real`, `TauCeti.DavisKahan.Experimental.Foundation.realSpectrum_subset_Iic_of_re_inner_le_generic`, `TauCeti.DavisKahan.Experimental.Foundation.realSpectrum_subset_Ici_of_le_re_inner_generic`, `TauCeti.DavisKahan.Experimental.Foundation.spectrumIn_Iic_of_re_inner_le_generic`, `TauCeti.DavisKahan.Experimental.Foundation.spectrumIn_Ici_of_le_re_inner_generic`
- **Assessment:** Theorems 8.1's conclusion is packaged as `Theorem81SourceConclusion` and proved sorry-free in `DavisKahan/Experimental/Frontier/Section8.lean`; `#print axioms` gives [propext, Classical.choice, Quot.sound]. The status stays `candidate_under_repair` because that axis is fidelity to the printed statement, which compiling does not establish -- not because anything fails to build.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_exact`. All five declarations are compiled and axiom-clean. They resolve only outside the default build, which is what `proved_outside_build` records; the mathematics itself matches the printed theorem.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**2026-08-05 (second session): both promotion-blocking admissions are out of this row's closure.** `directRotation_minimal` was orphaned -- nothing outside its own file referenced it, and the complex statement is already proved in production as `spectraDirectRotation_minimal`; `SpectraBridge/DirectRotationAPI.lean` imported that module only for `IsAcute` and now takes it from `BoundedOperator/Compat`. `projectionDifference_ideal_intervalExterior`, `ideal_sinTheta` and `ideal_sinTwoTheta` moved into `Experimental/InfiniteDimensional/SinTheta/IdealIntervalExterior.lean`, leaving `SinTheta/General.lean` and `InfiniteDimensional/DoubleAngle.lean` sorry-free. Measured closures: 175/188/199 modules, 24/41/50 Experimental, 0 tactic sorries each. WHAT STILL BLOCKS THE ROW: `check_library_structure` rule 2 forbids a production module importing `Experimental`, so promotion means RELOCATING those closures out of `Experimental/`. That is a design decision, not a mechanical step -- take it deliberately. Rule 3 now reports 49 violations (was 6) precisely because 34 modules became admission-free; the checker is enumerating what ought to move.

**GUARDED BY `lake build` 2026-08-06.** This row was `proved_outside_build` only because its modules sat under `Experimental/`, where no default target reaches them. The mathematics never changed. Two admissions were first removed from the import closures (one was orphaned; the other moved to `SinTheta/IdealIntervalExterior.lean`), after which `check_library_structure` rule 3 began enumerating the modules that had become admission-free -- i.e. the checker produced the promotion worklist. 84 modules then moved by `git mv` with **no namespace or declaration renamed**, the precedent being `Geometry/Polar/DirectRotationSquare.lean`, which lives in production while declaring into `DavisKahan.Experimental`. So the fully-qualified names in this row are unchanged.

The move had to be the DOWNWARD CLOSURE of the flagged modules, not the flagged modules alone: they import admission-free modules held under `Experimental/` only because something *above* those carried a `sorry`, so moving the flagged set alone would have violated rule 2. Rule 3 went 49 -> 13 violations.

**BLOCKER CLEARED 2026-08-06: the promotion happened.**  `section8-promotion-out-of-experimental` described the theorems as living under `DavisKahan.Experimental.Frontier`, untouched by `lake build`.  They no longer do: `DavisKahan/Frontier/Section8.lean` and `DavisKahan/Sources/DavisKahan1970/Section8/**` are production, reached from `DavisKahan.All`, and the Experimental copies are gone (their leftover build products were purged the same day).  Re-verified by the elaborator: both headline declarations resolve against `DavisKahan.All` and `#print axioms` gives exactly [propext, Classical.choice, Quot.sound].  The census declaration probe is at 156/156.  The blocker entry is removed because no row is blocked by it.

**FIDELITY BUG FOUND AND THE ROW DOWNGRADED 2026-08-07 (Claude Opus 5).**  This row read `compiled_exact` / "Nothing outstanding" while the production source file it points at, `DavisKahan/Sources/DavisKahan1970/Section8/SourceSurface.lean`, says in its own module docstring that the complete historical Theorem 8.1 and Theorem 8.2 are NOT promoted.  Both statements cannot be true.  The source file is the one that is right: `theorem8_1_selectedBranch_and_spectralRepulsion` is an `alias` for `theorem81CoreConclusion`, which takes a `SpectralContinuationWitness` plus `hsmall`, `h0` and `h1` -- the branch selection, the contour smallness, and the spectral orientation are all supplied BY THE CALLER, and they are exactly what the paper proves.  Likewise `theorem8_2_perturbationHalfGap_selectedBranch` requires a `PerturbationHalfGapBridge`, whose field `contour_selects_quarter_branch` is the conclusion.  A declaration compiling says nothing about whether its hypotheses are the printed ones; that is the lesson this row records.

**REPAIRED 2026-08-07 (Claude Opus 5): the headline theorem now takes only the printed hypotheses.**  `theorem8_1_canonicalBranch` assumes exactly: `A` self-adjoint, `P` reduces `A`, the `P` block below `alpha`, the `Pperp` block above `alpha+delta`, `H` self-adjoint and FULLY OFF-DIAGONAL relative to `P`.  No contour, no `SpectralContinuationWitness`, no `hsmall`, no caller-supplied orientation.  It proves: full spectral repulsion (`realSpectrum (A+H) subseteq Iic alpha union Ici (alpha+delta)` -- continuous spectrum included, not merely eigenvalues); the canonical branch `Q` as the genuine spectral subspace of `A+H` for `Iic alpha`; both sharp ordered form bounds on `Q` and `Qperp`; both restricted-spectrum containments; and `IsQuarterAcute P Q`, i.e. STRICTLY inside the quarter turn, which is stronger than the printed closed `Theta <= pi/4`.  `theorem8_1_eq_canonicalBranch_of_maximalAngle_le` is the converse: a reducing subspace satisfying the printed CLOSED condition equals `Q`.  `theorem8_1_maximalAngle_le_iff_spectrumIn` is the printed `iff` between the closed quarter-angle condition and the spectral orientation.  All axiom-clean.

Two supporting seams were new mathematics, not bookkeeping.  (1) The sharp form bounds: with the gap, the indicator of `Iic alpha` is continuous ON THE SPECTRUM, so the spectral projection is a continuous functional calculus and `(alpha - t) chi(t) >= 0` on the spectrum gives the bound with NO loss.  The pre-existing band estimate `norm_comp_boundedPVM_proj_sub_smul_le` loses a factor of two and cannot close the gap at all.  (2) Uniqueness needs a reducing projection to commute with the branch projection; that is `Commute.cfcHom`, available precisely because (1) made the projection a continuous calculus.

PART (i) IS ALSO DONE.  `theorem8_1_upperCompressionRepulsion_canonicalBranch` and its lower companion instantiate the compression-repulsion cores at `canonicalLowBranch`, so no abstract data record and no continuation witness appears in their hypotheses either -- the caller supplies only the printed configuration.

WHAT WAS STILL MISSING AT THAT POINT (superseded later the same day; see the `compiled_exact` note below): parts (ii) and (iii).  (ii) is the finite-dimensional ordered eigenvalue inequalities, which should follow from the compression inequalities via `LinearMap.IsSymmetric.eigenvalue_mono` (ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean).  (iii) is the printed "every symmetric gauge" inequality, which must go through the finite symmetric-gauge / majorization / Ky Fan layer -- substituting the operator norm would be a weakening, not a proof.

**SOURCE-VERIFIED AGAINST THE FULL TRANSCRIPTION 2026-08-07 (Claude Opus 5).**  The printed proof of the quarter-angle bound is finite-dimensional plus "the infinite-dimensional case follows by approximation".  `theorem8_1_canonicalBranch` is dimension-free and gives the STRICT bound `IsQuarterAcute P Q`, so the Lean development is stronger than the printed argument here, not weaker.  The printed converse is exactly the direction formalized by `theorem8_1_eq_canonicalBranch_of_maximalAngle_le`.

**PARTS (ii) AND (iii) LANDED, BOTH BLOCKS, AND THE ROW IS NOW `compiled_exact` 2026-08-07 (Claude Opus 5).**

Part (ii).  `theorem8_1_upperApproximationRepulsion_source` and
`theorem8_1_lowerApproximationRepulsion_source`.  The route recorded in the previous
`next_action` was not the one taken, and the difference matters: it proposed
`LinearMap.IsSymmetric.eigenvalue_mono`, which is finite-dimensional and would have forced a
subspace transfer of the whole development.  `approximationNumber_mono_of_form_le` does the
same Weyl step for POSITIVE operators in ARBITRARY dimension, by factoring through square
roots, so no transfer and no finite-dimensionality hypothesis is needed.  That is what
delivers the printed clause's "and natural infinite-dimensional extensions" rather than only
its finite reading.  The two blocks share the step
`theorem8_1_{upper,lower}SandwichApproximation_source`, which is part (i) plus form
monotonicity and nothing else; part (ii) then applies the coarse cosine-sandwich bound
`a_n(D* M D) <= ||D||^2 a_n(M)`.

Part (iii).  `theorem8_1_upperSymmetricGaugeRepulsion_source` and its lower companion,
quantified over EVERY `FiniteSymmetricGauge` -- not the operator norm, not Frobenius, not
Ky Fan k.  They are corollaries of the strictly stronger weak majorizations
`theorem8_1_{upper,lower}WeightedWeakMajorization_source`,

    a(A_1 - alpha)  <<w  (i |-> a_i(Lambda_1 - alpha) * a_i(C_1)^2),

which chain the SAME Weyl step of part (i) into `approximationNumber_adjoint_sandwich_weaklyMajorized`.
Part (iii) is therefore NOT derived from part (ii)'s conclusion, which has already discarded
every cosine but the largest; the two clauses share only the earlier step.  The generalized
von Neumann / rearrangement / Ky Fan content of the printed proof is absorbed into the generic
sandwich majorization theorem, which is proved by the Ky Fan maximum principle plus Abel
summation and needs no alignment unitary.

The lower block is a MIRROR, not a second proof.  The reflection `A |-> -A`,
`alpha |-> -(alpha + delta)` exchanges the two sides of the printed gap and carries
`A_1 - alpha` to `(alpha + delta) - A_0` and `C_1` to `C_0`, which is why `lowerBlockShift`
carries the shift constant `alpha + delta`.  Positivity of the perturbed lower block comes
from `branch_form_low` of the canonical branch, so no branch bound is re-proved.

THE SOURCE DICTIONARY IS COMPILED, NOT PROSE.  Three identifications, each its own theorem:
(a) `approximationNumber_eq_eigenvalues_of_isPositive` -- for a positive operator the
approximation numbers ARE the sorted eigenvalues, which is the printed `alpha_k` and
`lambda_k`; every block here is positive because of the printed gap.
(b) `approximationNumber_{upper,lower}BlockShift_eq_zero_of_le` -- extending a compression by
zero only appends zeros, so the ambient sequence is the printed finite eigenvalue list
followed by a zero tail, which changes neither a prefix sum nor a symmetric gauge.
(c) `approximationNumber_cosineBlock_eq_principalCosines` and its lower companion -- the
cosine block's singular values ARE `TauCeti.principalCosines`, the repository's principal-angle
cosines, defined as the singular values of the cross projection.  No new theta was invented:
this is the paper's own equation (1.16), `Theta_j = arccos (C_j C_j*)^{1/2}`, which DEFINES the
angles as arccosines of exactly these numbers.  `cos_arccos_approximationNumber_cosineBlock`
records the round trip with `theta_i` in `[0, pi/2]`, and
`norm_cosineBlock_eq_principalCosines_zero` reads the printed bound norm `||C_1||_1` as the
largest principal cosine, which is the printed meaning of replacing every `cos^2 theta_k` by
the largest one in part (ii).

ORDERING, HANDLED ON BOTH SIDES AT ONCE.  `approximationNumber` and `principalCosines` are
indexed decreasingly; the paper prints `lambda_1 <= lambda_2 <= ...` increasing and (Section 1,
after (1.16)) `theta_1 >= theta_2 >= ...` decreasing, so the printed `cos^2 theta_k` is
INCREASING in k and the printed right-hand side pairs k-th smallest with k-th smallest.  That
is the same multiset of products as pairing largest with largest.  The reindex is compiled,
not asserted: `theorem8_1_{upper,lower}SymmetricGaugeRepulsion_angle_rev_source` apply `Fin.rev`
to BOTH sides simultaneously and are the printed increasing reading; they follow from the
decreasing statements by `FiniteSymmetricGauge.perm` alone.

Audit: `DavisKahan/Frontier/Section8Audit.lean`, 42 targets, every one
[propext, Classical.choice, Quot.sound].

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 21 is UPHELD for this row: it was
`compiled_exact` with `blocked_by: []` while every declaration on it is `InnerProductSpace C`, which is
the defect for which the sine rows were graded.  The `real-scalar-infinite-dimensional-scope` blocker
and a `scope_gap` are added; the STATUS DELIBERATELY DOES NOT MOVE, because this census's established
convention for a complex-only row whose mathematics is otherwise exact is `compiled_exact` plus that
blocker (see `DK-3.1-prop`, `DK-6.1-thm`, `S2-sin-theta`).  Everything else on this row was
independently re-confirmed by the 2026-08-09 audit: (a) both directions over every reducing `M`, (b) an
explicit construction with strict `Theta < pi/4` and uniqueness rather than an existential, (i)/(ii)/(iii)
both sides each, and Krein's completion PROVED rather than assumed.

**REAL THEOREM 8.1 IS COMPLETE FOR 8.1(a) AND 8.1(b), 2026-08-09.**  Existence landed in commit 9173ad4e and uniqueness plus the printed characterization in cd11f08f (joncrall with GPT-5.6 Sol); this note and the declaration list were added by the coordinator (Claude Opus 5) at integration, because NEITHER COMMIT TOUCHED THE CENSUS and every gate passed while this row still asserted that no declaration on it covered a real Hilbert space.  That is the documented failure mode of `probe_census_declarations.py`: it can only check the declarations a row NAMES, so a row whose list is incomplete has nothing to disagree with.

The uniqueness proof does NOT replay the complex cfc argument: it complexifies both candidate reducing subspaces, applies the dimension-free complex uniqueness theorem to identify each with the same canonical branch, and descends the equality through injectivity of `complexifySubmodule`.  The form-bound-to-spectrum implications were factored out into `DavisKahan/SpectralTheory/FormSpectrumBounds.lean` as four `RCLike`-generic lemmas rather than duplicated over R, and both the real and complex source theorems consume them; those four are now listed on this row.

STATUS LEFT AT `compiled_exact` PENDING A HUMAN CALL on whether the surviving complex-only (ii)/(iii) family is a narrowing worth recording in the status field.  The row carried `compiled_exact` with a real-scalar gap BEFORE this work, which the completion handoff cites as its example of a status that overstates; the gap is now strictly smaller but not empty.
- **Next action:** Transport parts (ii) and (iii) to real scalars, or record them as complex-only by design.  8.1(a) and 8.1(b) need nothing further: characterization, existence and uniqueness are compiled over both R and C at unrestricted dimension.  The `..._of_rotatedBlockData` aliases remain listed as INTERNAL infrastructure: they take an abstract quadratic-data record and are not evidence about the printed theorem.

#### Theorem 8.2: Smallness selects the acute branch

- **Kind:** `theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** If the perturbation norm or the residual norm is below half the gap, and the unperturbed block's spectrum lies in the enlarged central interval, then the sine double-angle estimate is accompanied by Theta < pi/4.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_source`, `TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_source`, `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed`, `TauCeti.DavisKahan1970.Section8.theorem8_2_krein_completion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source`, `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source`, `TauCeti.DavisKahan1970.Section8.subspaceGap_eq_directedGap_of_finrank_eq`, `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_source_maximalAngle_lt`, `TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_source_maximalAngle_lt`, `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_maximalAngle_lt`, `TauCeti.DavisKahan1970.Section8.theorem8_2_source`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.theorem8_2_perturbationHalfGap_source_angle_lt`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.theorem8_2_residualHalfGap_source_angle_lt`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.residual_eq_comp_subtypeL`, `TauCeti.DavisKahan.Experimental.Frontier.Krein.exists_selfAdjoint_completion_eq_norm_restriction`, `TauCeti.DavisKahan1970.Section8.PerturbationHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.ResidualHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.theorem82_branch_of_residualHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_selectedBranch`, `TauCeti.DavisKahan1970.Section8.subspaceGap_eq_directedGap_of_crossedDefects`, `TauCeti.DavisKahan1970.Section8.maximalAngle_lt_pi_div_four_of_crossedDefects`
- **Assessment:** `theorem8_2_perturbationHalfGap_selectedBranch` and `theorem8_2_residualHalfGap_selectedBranch` are proved sorry-free in `DavisKahan/Experimental/Frontier/Section8.lean`; `#print axioms` on the perturbation form gives [propext, Classical.choice, Quot.sound]. The half-gap bridges (`perturbationHalfGapBridge_of_sourceHypotheses`, `residualHalfGapBridge_of_sourceHypotheses`) are proved too.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. All four declarations are compiled and axiom-clean, outside the default build. The audit of the two half-gap branches against the printed Theorem 8.2 has not been done, so this is not yet claimed as exact.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**2026-08-05 (second session): both promotion-blocking admissions are out of this row's closure.** `directRotation_minimal` was orphaned -- nothing outside its own file referenced it, and the complex statement is already proved in production as `spectraDirectRotation_minimal`; `SpectraBridge/DirectRotationAPI.lean` imported that module only for `IsAcute` and now takes it from `BoundedOperator/Compat`. `projectionDifference_ideal_intervalExterior`, `ideal_sinTheta` and `ideal_sinTwoTheta` moved into `Experimental/InfiniteDimensional/SinTheta/IdealIntervalExterior.lean`, leaving `SinTheta/General.lean` and `InfiniteDimensional/DoubleAngle.lean` sorry-free. Measured closures: 175/188/199 modules, 24/41/50 Experimental, 0 tactic sorries each. WHAT STILL BLOCKS THE ROW: `check_library_structure` rule 2 forbids a production module importing `Experimental`, so promotion means RELOCATING those closures out of `Experimental/`. That is a design decision, not a mechanical step -- take it deliberately. Rule 3 now reports 49 violations (was 6) precisely because 34 modules became admission-free; the checker is enumerating what ought to move.

**GUARDED BY `lake build` 2026-08-06.** This row was `proved_outside_build` only because its modules sat under `Experimental/`, where no default target reaches them. The mathematics never changed. Two admissions were first removed from the import closures (one was orphaned; the other moved to `SinTheta/IdealIntervalExterior.lean`), after which `check_library_structure` rule 3 began enumerating the modules that had become admission-free -- i.e. the checker produced the promotion worklist. 84 modules then moved by `git mv` with **no namespace or declaration renamed**, the precedent being `Geometry/Polar/DirectRotationSquare.lean`, which lives in production while declaring into `DavisKahan.Experimental`. So the fully-qualified names in this row are unchanged.

The move had to be the DOWNWARD CLOSURE of the flagged modules, not the flagged modules alone: they import admission-free modules held under `Experimental/` only because something *above* those carried a `sorry`, so moving the flagged set alone would have violated rule 2. Rule 3 went 49 -> 13 violations.

**BLOCKER CLEARED 2026-08-06: the promotion happened.**  `section8-promotion-out-of-experimental` described the theorems as living under `DavisKahan.Experimental.Frontier`, untouched by `lake build`.  They no longer do: `DavisKahan/Frontier/Section8.lean` and `DavisKahan/Sources/DavisKahan1970/Section8/**` are production, reached from `DavisKahan.All`, and the Experimental copies are gone (their leftover build products were purged the same day).  Re-verified by the elaborator: both headline declarations resolve against `DavisKahan.All` and `#print axioms` gives exactly [propext, Classical.choice, Quot.sound].  The census declaration probe is at 156/156.  The blocker entry is removed because no row is blocked by it.

**FIDELITY BUG FOUND AND THE ROW DOWNGRADED 2026-08-07 (Claude Opus 5).**  This row read `compiled_exact` / "Nothing outstanding" while the production source file it points at, `DavisKahan/Sources/DavisKahan1970/Section8/SourceSurface.lean`, says in its own module docstring that the complete historical Theorem 8.1 and Theorem 8.2 are NOT promoted.  Both statements cannot be true.  The source file is the one that is right: `theorem8_1_selectedBranch_and_spectralRepulsion` is an `alias` for `theorem81CoreConclusion`, which takes a `SpectralContinuationWitness` plus `hsmall`, `h0` and `h1` -- the branch selection, the contour smallness, and the spectral orientation are all supplied BY THE CALLER, and they are exactly what the paper proves.  Likewise `theorem8_2_perturbationHalfGap_selectedBranch` requires a `PerturbationHalfGapBridge`, whose field `contour_selects_quarter_branch` is the conclusion.  A declaration compiling says nothing about whether its hypotheses are the printed ones; that is the lesson this row records.

**SOURCE-VERIFIED AGAINST THE FULL TRANSCRIPTION 2026-08-07 (Claude Opus 5).**  The printed Theorem 8.2 adds `||H||_1 < delta/2` OR `||R||_1 < delta/2` to the sin2theta hypotheses AND assumes the spectrum of `A_0` lies in `[beta - delta/2, alpha + delta/2]`.  That last hypothesis was missing from this row's summary: it is what makes `[beta - delta/2, alpha + delta/2]` the right interval for the spectral projector along the path.  The conclusion is `Theta < pi/4`, strict.

**BOTH ALTERNATIVES LANDED FROM THE PRINTED HYPOTHESES, AND THE PRINTED `Theta < pi/4` IS NOW
COMPILED UNDER THE PAPER'S OWN STANDING CONVENTION 2026-08-07 (Claude Opus 5).**

Perturbation alternative: `theorem8_2_perturbationHalfGap_source`, by the printed connectedness
bootstrap, from `||H|| < delta/2` plus the printed placement `spectrum(A_0)` in
`[beta - delta/2, alpha + delta/2]` and the sin2theta configuration.  No contour, no
`SpectralContinuationWitness`, no projection-Lipschitz constant, no half-gap bridge appears among
the hypotheses.  Residual alternative: `theorem8_2_residualHalfGap_source`, by the printed
one-sentence Krein reduction -- `Krein.exists_selfAdjoint_completion_eq_norm_restriction` replaces
`H` by a self-adjoint `H'` with the same first block column and `||H'|| = ||R||`, so
`A' := A + H - H'` leaves `A' + H' = A + H` and `A'|P = A|P` and every printed hypothesis
transfers verbatim.  `R` is the source residual (1.8) exactly, and `residual_eq_comp_subtypeL`
proves the Section 1 identity `R = H E_0` from invariance alone.  `theorem8_2_branch_source_directed`
is the printed disjunction.  The two half-gap bridge records survive as internal conveniences and
are listed as such; their field `contour_selects_quarter_branch` is the conclusion, so they must
never appear in a source-facing statement.

THE `Theta` CONVENTION, AND A SOURCE FINDING.  The four theorems above conclude
`directedGap P Q < sqrt 2 / 2`.  That is what the printed argument actually delivers: the paper's
step "beta <= A_0 <= alpha implies P = P Q(1), we have theta(1) >= Theta" controls only how `P H`
sits inside the band subspace `Q(1) H`, which is a DIRECTED comparison.  The paper's `Theta` is
the symmetric object -- Section 1's dictionary after (1.17) reads `||P - Q|| = ||sin Theta||` --
and `Theta` is only defined at all when equation (1.5) holds,

    dim P H = dim Q H     and     dim P-perp H = dim Q-perp H,

because `Theta_j = arccos (C_j C_j*)^{1/2}` is built from the entries of a unitary satisfying
(1.4), which forces (1.5).  So (1.5) is the printed standing convention that makes the printed
conclusion meaningful, and it is what the formalization adds -- not `IsQuarterAcute P Q`, which
would be assuming the conclusion.  In its finite form (1.5) is `finrank P = finrank Q`, its second
half being automatic, and `subspaceGap_eq_directedGap_of_finrank_eq` then identifies the symmetric
and directed gaps.  `theorem8_2_{perturbationHalfGap,residualHalfGap,branch}_source_maximalAngle_lt`
are the printed `Theta < pi/4`, and `theorem8_2_source` is the whole printed theorem: both
`sin 2Theta` estimates -- inherited from the maintained sin2theta development and restated at
8.2's own hypotheses as `theorem8_2_sinTwoTheta_{perturbation,residual}_source` -- together with
the strict quarter angle, under either printed smallness alternative.

FINDING, RECORDED AND NOT PAPERED OVER: the printed conclusion read with the CARDINAL form of
(1.5) is FALSE in infinite dimensions.  Counterexample, satisfying every printed hypothesis of
Theorem 8.2.  Let `E` be a separable infinite-dimensional Hilbert space with orthonormal basis
`e_0, e_1, ...`, put `H := E (+) E`, and let `A` be `0` on the first summand and `10` on the
second; take `K = 0`, `beta = alpha = 0`, `delta = 1`.  Then `Q := E (+) 0` has
`spectrum(Lambda_0) = {0}` in `[beta, alpha]` and `spectrum(Lambda_1) = {10}` outside
`(beta - delta, alpha + delta)`; `P := span{e_1, e_2, ...} (+) 0` reduces `A` with
`spectrum(A_0) = {0}` in `[beta - delta/2, alpha + delta/2]`; and `||K|| = 0 < delta/2`.  Both
halves of (1.5) hold as cardinals: `dim P = dim Q = aleph_0` and
`dim P-perp = dim Q-perp = aleph_0`.  Yet `e_0` lies in `Q` and is orthogonal to `P`, so
`||P - Q|| = 1` and the symmetric `Theta` is `pi/2`, not below `pi/4`.  Equal (infinite)
dimension does not force the two directed gaps to agree.  In finite dimensions `P <= Q` with
equal rank gives `P = Q`, so the finite form of (1.5) is not a lazy restriction but the correct
repair; the dimension-free statement is correspondingly kept in its directed form and is NOT
superseded.  The earlier `P = bottom`, `Q = top` example recorded in
`Section8Perturbation.lean` is the degenerate finite instance of the same phenomenon.

Audit: `DavisKahan/Frontier/Section8Audit.lean`; every Theorem 8.2 target reports
[propext, Classical.choice, Quot.sound].

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreements 19, 20 and 21 are ALL UPHELD, and the
status is LOWERED `compiled_exact` -> `compiled_specialization`.

**(19) THE RECORDED INFINITE-DIMENSIONAL COUNTEREXAMPLE ABOVE IS NOT A COUNTEREXAMPLE, AND THE
NARROWING'S RECORDED JUSTIFICATION IS INVALID.**  The example -- `H = E (+) E`, `A = 0 (+) 10`,
`Q = E (+) 0`, `P = span{e_1, e_2, ...} (+) 0` -- is claimed above to satisfy "every printed hypothesis
of Theorem 8.2 together with the cardinal form of (1.5)".  It does not.  Checked against the
transcription 2026-08-09: (3.5) is `dim(P H cap Qperp H) = dim(Pperp H cap Q H)`, and L961 reads "We
shall assume (3.5) as well as (1.5) except where stated otherwise", so (3.5) is a STANDING assumption
of everything after Section 3, Theorem 8.2 included.  In the example
`P H cap Qperp H = (span{e_1,...} (+) 0) cap (0 (+) E) = 0` while
`Pperp H cap Q H = (span{e_0} (+) E) cap (E (+) 0) = span{e_0} (+) 0`, so `0 != 1` and (3.5) FAILS.
The example is a correct witness that the CARDINAL form of (1.5) alone does not force the two directed
gaps to agree -- which is worth keeping and is exactly the phenomenon the source's own bilateral-shift
Remark exhibits (see `DK-3.2-prop`) -- but it licenses nothing about Theorem 8.2.

WHAT THE REAL JUSTIFICATION IS.  Under (3.5), `dim Null(C_0) = dim Null(C_0^*)`, which by the
transcription's own discussion (L832--834) is precisely the condition under which `S_0` and `S_1` have
the same singular values including the leading 1s; so `||P - Q|| = ||S_0||` and the symmetric and
directed gaps coincide.  Finite dimension with `finrank P = finrank Q` is a SUFFICIENT condition for
(3.5) -- it is the paper's own Remark after Proposition 3.2: "Since we are assuming (1.5), (3.5) will
hold automatically if either `dim P H` or `dim Pperp H` is finite" -- so `[FiniteDimensional]` is a
correct but strictly stronger stand-in for the printed hypothesis, not a repair forced by a
counterexample.  Whether the printed `Theta < pi/4` holds in infinite dimensions under (1.5)+(3.5) is
therefore OPEN and is recorded in `next_action`; nothing in the build settles it either way.

**(20) `compiled_exact` ALSO OVERSTATED THE NORM AXIS**, and one name in the prose above is wrong.
`theorem8_2_sinTwoTheta_{perturbation,residual}_source` conclude at the operator norm only.  And
`perturbationHalfGapBridge_of_sourceHypotheses` / `residualHalfGapBridge_of_sourceHypotheses` are NOT
in `TauCeti.DavisKahan1970.Section8`, where the prose above puts them: `#check` there fails with
`unknownIdentifier`, and they live in `TauCeti.DavisKahan.Experimental.Frontier.Section8`
(`DavisKahan/Frontier/Section8.lean:804,820`).  Both also take an extra quantitative smallness
hypothesis `D.radius * ||E|| / D.margin^2 < sqrt 2 / 2` that the prose above does not mention.  They
remain internal conveniences and, as recorded, must never appear in a source-facing statement.

**(21) SCALARS.**  Every declaration on this row and on `DK-8.1-thm` is `InnerProductSpace C`, which is
the same defect for which `S2-sin-two-theta` and `S2-sin-theta` were graded.  The
`real-scalar-infinite-dimensional-scope` blocker is added to both rows so the grading is consistent.

NONE OF THIS TOUCHES THE MATHEMATICS RECORDED ABOVE, which is sound and axiom-clean; what changes is
the census's judgement of it against the printed statement.

**THE DIMENSION AXIS IS CLOSED UNDER THE PAPER'S OWN STANDING ASSUMPTION, 2026-08-10 (Claude Opus 5, coordinator-verified).**  `maximalAngle_lt_pi_div_four_of_crossedDefects` proves the printed `Theta < pi/4` from `CrossedDefectsEquivalent P Q` -- which IS (3.5), in its constructive form -- with NO `[FiniteDimensional]` and NO `finrank` anywhere.  The existing finrank forms are untouched and remain available.  The underlying geometry is `Frontier.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent`, `RCLike`-generic at unrestricted dimension, resting on new reusable `Submodule` lemmas in `ForTauCeti/Analysis/InnerProductSpace/Projection/Gap.lean`.

**THE RECORDED ROUTE FOR THIS ITEM WAS HEAVIER THAN NECESSARY AND SHOULD NOT BE FOLLOWED.**  The `next_action` pointed at the transcription's singular-data argument via the Halmos generic decomposition and crossed sine blocks as adjoint/polar partners.  MEASURED: the result needs NONE of that.  The engine is Cauchy-Schwarz plus a density argument -- with `c = sqrt(1 - ||P_Vperp P_U||^2)`, Pythagoras gives `c||u|| <= ||P_V u||` on `U`, the identity `<P_U a, u> = <a,a>` for `a = P_V u` propagates the SAME constant, `P_V '' U` is dense in `V` exactly when `Uperp inf V = bot`, and the bound is a closed condition -- with the defect case handled by ONE fixed vector.  A future agent formalizing the generic decomposition for this would be building infrastructure the result does not use.

NOTE ON THE RIGHT HYPOTHESIS: each direction of the gap inequality uses only ONE crossed intersection, so the natural hypothesis is the IFF `U inf Vperp = bot <-> Uperp inf V = bot`, which is strictly WEAKER than (3.5).  The reusable lemma is stated at that weaker hypothesis (`Submodule.projectionGap_eq_directedProjectionGap_of_inf_orthogonal_eq_bot_iff`) and (3.5) is applied on top.

ALSO: a SECOND sufficient condition for the two directed gaps to agree already existed and is unrelated -- `subspaceGap_eq_directedGap_reflection` (`DavisKahan/SpectralTheory/ReflectionRestriction.lean`) gets the symmetry from a unitary that SWAPS the pair.  Both now reduce through `Submodule.projectionGap_eq_max_directedProjectionGap`.  The pre-existing `subspaceGap_eq_directedGap_of_finrank_eq` (`Frontier/Section8SourceTheorem82.lean:156`) is the third, and carries `[FiniteDimensional C H]`.
- **Next action:** ITEM (1) IS DONE as of 2026-08-10 -- `maximalAngle_lt_pi_div_four_of_crossedDefects` proves the printed `Theta < pi/4` under `CrossedDefectsEquivalent` (which IS (3.5)) with NO `[FiniteDimensional]` and NO `finrank`.  See this row's notes.  REMAINING: Three items.  (1) THE SUBSTANTIVE ONE: restate the printed `Theta < pi/4` under the Section 3 standing assumption (3.5) -- `dim(P H cap Qperp H) = dim(Pperp H cap Q H)` -- instead of `[FiniteDimensional C H]`, and prove `subspaceGap P Q = directedGap P Q` from (3.5) rather than from `subspaceGap_eq_directedGap_of_finrank_eq`.  The route is the transcription's L832--834 argument: (3.5) says `dim Null(C_0) = dim Null(C_0^*)`, which is exactly when `S_0` and `S_1` carry the same singular data.  If that turns out to be false in infinite dimensions, the counterexample must satisfy (3.5) -- the one recorded in the notes does not, and its refutation is written up there so it is not re-used.  (2) Restate the inherited `sin 2theta` conclusion at every source unitarily invariant norm under 8.2's own hypotheses; only the operator norm is compiled.  (3) Real scalars, through the complexification route -- note the audit's structural warning that 8.1(a)/(b) are not a mechanical transport, since one must show the complex branch IS the complexification of a real reducing subspace.

### Section 9

#### Section 9, problem setup: Fourth-derivative Rayleigh–Ritz model

- **Kind:** `numerical_model`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** The free-beam fourth derivative on L2(0,1), perturbed by multiplication by epsilon t, with the two-dimensional linear trial eigenspace.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamOperator`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamOperator_isSelfAdjoint`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.realSpectrum_beamOperator_subset_gap`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.realSpectrum_beamOperator_subset_sharp`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTrial_orthonormal`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.inner_centeredAffineLp`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.inner_centeredAffineLp_mul`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.inner_mul_centeredAffineLp_mul`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamRitz_matrix`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamResidualGram_matrix`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamFiniteDataCertificate`, `TauCeti.DavisKahan1970.Section9.CenteredAffine`, `TauCeti.DavisKahan1970.Section9.ritz_matrix_from_affine_moments`, `TauCeti.DavisKahan1970.Section9.FreeBeamFiniteDataCertificate`
- **Assessment:** A source-facing candidate now reconstructs the affine trial basis through exact unit-interval moments and packages the remaining free-beam analytic facts behind an explicit certificate. The closed fourth-derivative operator and the bound alpha_3 > 500 are not yet proved.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The finite-moment layer is compiled and axiom-clean, but every source conclusion is stated relative to `FreeBeamFiniteDataCertificate`, for which no value is ever constructed. The analytic model -- the closed fourth-derivative operator with the source's boundary conditions -- does not exist.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

BLOCKER CLEARED 2026-08-04: `free-beam-third-eigenvalue` is resolved. The paper's `alpha_3 > 500` is now the unconditional theorem `FreeBeam.Classical.five_hundred_lt_pow_four_of_characteristic_eq_zero`, proved from `cos beta * cosh beta < 1` on `(0, 4.73]` with no certificate and no existence hypothesis. What still blocks this row is only `free-beam-closed-operator` -- tying the characteristic roots to the spectrum of an actual self-adjoint operator on `L^2(0,1)`.

WHERE THE alpha_3 BOUND CAME FROM (blocker `free-beam-third-eigenvalue`, deleted 2026-08-04 once resolved). The plan of record was to construct `FirstPositiveRootCertificate` -- localize the FIRST root, then apply `positive_root_fourth_power_gt_five_hundred`. That turned out to be unnecessary and strictly harder: localizing a first root requires proving one exists, which needs an intermediate-value argument and a second numerical bound at 4.74. It is enough that the characteristic function has NO root at or below 4.73, which makes every positive root exceed 4.73 whether or not a smallest one is exhibited. `FirstPositiveRootCertificate` and `PositiveRootLocalization` are now dead weight, retained only because they record the reduction; consumers should use `five_hundred_lt_pow_four_of_characteristic_eq_zero`.

The new mathematics is `Section9/FreeBeamRootExclusion.lean`: `cos b * cosh b < 1` on all of `(0, 4.73]`, split three ways. On `(0, pi/2]` it is calculus -- `f = cos*cosh` has `f 0 = 1`, `f'` vanishing at 0, and `f'' = -2 sin*sinh < 0`, so `f'` is strictly decreasing from 0 and `f` from 1. On `[pi/2, 3pi/2]` the cosine is nonpositive. On the remaining `(3pi/2, 4.73]` -- a window of width 0.0177 -- it is numerical: `cos b = sin(b - 3pi/2) <= b - 3pi/2 < 0.017612` using `Real.pi_gt_d6`, and `cosh b <= cosh 4.73 < 56.66` via `exp 4.73 = (exp 1)^4 * exp 0.73` with `Real.exp_one_lt_d9` and six Taylor terms. Product `< 0.99790`; the true value is `0.99765`, so the margin is two parts in a thousand and every bound is needed to five digits.

THE ANALYTIC MODEL EXISTS, 2026-08-07 (Fable 5).  The closed self-adjoint free-beam operator is now CONSTRUCTED, not assumed: `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamOperator` (DavisKahan/SpectralTheory/FormMethod/BeamFormSpace.lean, BeamSpectrum.lean), the form-method realization on the weak-second-derivative pair space over L2(0,1].  Proved, all axiom-clean and guarded by `lake build`: self-adjointness, nonnegativity, Rellich compactness of the form embedding (no weak topology: rank-two affine part plus the compact second-primitive operator from ForTauCeti/MeasureTheory/IntervalSecondPrimitive*), kernel = the affine plane (both inclusions), and `realSpectrum_beamOperator_subset_gap`: the real spectrum lies in {0} union (500, infinity).  The alpha_3 > 500 bound is `eigenvalue_gt_five_hundred` / the gap theorem -- about the genuine operator.  The chain: representation theorem for weak second derivatives (bump family t^(k+2)(1-t)^2), eigen-bootstrap to classical modes via the interval ODE classification (FreeBeamModeUniqueness.lean), natural boundary conditions from the vanishing boundary form against Hermite cubics, the characteristic equation, and the unconditional root exclusion.

**THE ANALYTIC MODEL NOW EXISTS (2026-08-07, Opus 5).**  The blocker
`free-beam-closed-operator` is resolved and deleted.  `beamOperator`
(DavisKahan/SpectralTheory/FormMethod/BeamFormSpace.lean) is the self-adjoint,
nonnegative fourth-derivative realization on `L^2(0,1]`, built by inhabiting the
abstract form method on the weak-second-derivative pair space; its form embedding is
compact and dense, its kernel is exactly the affine plane in both directions, and
`realSpectrum_beamOperator_subset_gap` proves
`realSpectrum(beamOperator) subset {0} union (500, infinity)` -- the paper's alpha_3 > 500
for the genuine operator, not for a certificate field.

**THE MOMENTS ARE NOW INTEGRALS.**  `TrialSubspace.lean` declared its three bilinear
forms on `CenteredAffine` as finite data, noting that "a later integration lemma may
identify these forms with actual Lebesgue integrals on the unit interval".  Those lemmas
are `inner_centeredAffineLp`, `inner_centeredAffineLp_mul` and
`inner_mul_centeredAffineLp_mul` (BeamSection9.lean).  Consequently `beamTrial_orthonormal`
shows the two trial functions are an orthonormal pair of *zero modes of the operator*,
`beamRitz_matrix` shows the diagonal matrix of (9.5) is the genuine compression of
multiplication by `eps t` to that kernel, and `beamResidualGram_matrix` shows
`residualGram eps` is the genuine Gram matrix of the residual.

**ON INSTANTIATING THE RECORD.**  The 2026-08-04 warning under
`section9-certificate-discharge` stands and was respected: `FreeBeamFiniteDataCertificate`
is trivially instantiable, so `beamFiniteDataCertificate` is NOT the evidence for this
row.  The evidence is the four operator-level theorems above.  The constructed value is
recorded because its `third_eigenvalue` field is supplied by an actual nonzero point of
`beamOperator.realSpectrum` with `500 <` discharged from the proved gap -- which is the
only reading under which that (otherwise dead) field says anything.

**SKELETON RETIRED 2026-08-07.**  `DavisKahan/Experimental/Frontier/Section9Analytic.lean`
is deleted.  It was a sorried semantic-model skeleton (`FreeBeamAnalyticModel`,
`freeBeamClosedFourthDerivative`, `RepresentsFreeBeamProblem`, `actualSinThetaOne`, ...)
whose every declaration is superseded by the `FreeBeam.Model` namespace; no Lean file
referenced it outside its own `Frontier/All.lean` import.  After the deletion the only
`sorry`s left anywhere under `DavisKahan/` and `ForTauCeti/` are the two long-standing
unguarded `Experimental/InfiniteDimensional` items.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 23 is UPHELD on all three of its points
and the status is LOWERED `compiled_exact` -> `compiled_specialization`, with the
`real-scalar-infinite-dimensional-scope` blocker added.

WHAT WAS OVER-CLAIMED.  The `next_action` read "Nothing outstanding".  The three measured narrowings
are in `scope_gap` above.  None of them is a doubt about the mathematics recorded here, which is
substantial and axiom-clean -- the operator is genuinely constructed, its kernel is exactly the affine
plane in both directions, the form embedding is compact, the moments are genuine `L^2` integrals, and
`alpha > 500` for every nonzero real spectral point is unconditional and STRONGER than the printed
`alpha_3 > 500`.  What is over-claimed is `compiled_exact` against a printed model that is real, is the
closure of a classical differential operator, and asserts an infinite increasing sequence of positive
eigenvalues.

The existence of `alpha_3` is the sharpest of the three, because it is what turns
`beamFiniteDataCertificate` from a theorem into a conditional: the row above says the certificate "is
now inhabited", and it is, but only given a nonzero real spectral point that nothing supplies.  The
compactness of the form embedding, already proved here, should make it reachable -- see
`next_action`.

**AXIS (3), REAL SCALARS: MEASURED AND DELIBERATELY NOT ATTEMPTED, 2026-08-09 (Claude Opus 5, M34).**  Moving this row to real scalars would be a REDEFINITION of the model, not a transport, and it is the wrong thing to do at this point.  Three measurements support that.

(i) THE COMPLEXIFICATION ROUTE THAT CLOSED THE OTHER REAL-SCALAR ROWS IS UNAVAILABLE HERE.  Every one of those transports goes through `TauCeti.RealComplexification E` and `complexify`, which presents the complex space AS the complexification of a named real space.  `BeamL2 := Lp C 2 unitIocMeasure` is not presented that way, and there is no isometry `RealComplexification (Lp R 2 mu) ~= Lp C 2 mu` anywhere in `DavisKahan/` or `ForTauCeti/` -- verified by search: the string `Lp R` does not occur in either package, and the only `RealComplexification` isometries in the tree are the conjugation of `FunctionalCalculus.lean` and the submodule equivalence of `Complexification/SubmoduleEquiv.lean`.  Supplying that isometry is an `Lp`-complexification contribution in its own right, of Tau Ceti scope, not Davis--Kahan work.

(ii) THE COST IS THE WHOLE MODEL.  `BeamL2` is the ambient space of `BeamPairSpace`, `beamOperator`, its self-adjointness, the Rellich compactness of the form embedding, the affine-plane kernel in both directions, `realSpectrum_beamOperator_subset_gap`, `FreeBeamModeUniqueness`, the boundary-form computation, `beamTrial_orthonormal`, the three moment integrals, `beamRitz_matrix` and `beamResidualGram_matrix`.  Redoing all of it over `R` re-proves the same mathematics with a different scalar and changes no conclusion: the operator, its spectrum, its kernel, its Ritz data and its residual Gram matrix are real objects already.

(iii) CLEARING THIS AXIS WOULD NOT CHANGE THE ROW.  Axes (1) (the positive spectrum is not proved nonempty, so `alpha_3` is not exhibited) and (2) (form realization versus the closure of the classical fourth-derivative operator on the free-end domain) are untouched by the scalar question and are the substantial gaps; the row stays `compiled_specialization` either way.  Section 9 is also explicitly outside the migration gate in `AGENTS.md` ("Migration must not wait for Section 9 examples").

The blocker reference is therefore RETAINED and honest -- the printed space is the real `L^2(0,1)` and the compiled one is complex -- but this axis should be the last of the three to be worked, and only after the `Lp` complexification isometry exists for an independent reason.
- **Next action:** Three items, in increasing order of difficulty.  (1) EXISTENCE OF `alpha_3`: prove the positive real spectrum of `beamOperator` is nonempty (and in fact an unbounded increasing sequence).  The compactness of the form embedding is already proved here, so the resolvent is compact and the spectrum is a sequence of eigenvalues; what is needed is that the kernel is not everything, which the affine-plane kernel computation already gives.  This is what would let `beamFiniteDataCertificate` drop its `alpha in realSpectrum` hypothesis.  (2) Identify `beamOperator` with the closure of the classical `(d/dt)^4` on the four free-end boundary-condition domain; at present the boundary conditions are DERIVED for eigenfunctions from the vanishing boundary form, which is weaker.  (3) Real scalars: `BeamL2` is `Lp C 2`, the paper's space is real `L^2(0,1)`.  MEASURED 2026-08-09 (M34) and deliberately deferred: the complexification route that closed every other real-scalar row needs `Lp C 2 mu` presented as `RealComplexification (Lp R 2 mu)`, and no such isometry exists in this repository or is used from Mathlib, so this axis is a redefinition of the whole model rather than a transport -- see the notes.  Everything else on this row is done: the operator, its kernel, its spectral gap, the orthonormal trial pair, and the identification of the finite moments with genuine `L^2` integrals are compiled and in the default build, and the sorried `Section9Analytic` skeleton has been deleted.

#### Equations (9.1)–(9.4): Initial sine and sine-double-angle bounds

- **Kind:** `numerical_claims`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Compute R*R and derive the operator- and two-singular-value bounds for sin Theta and sin(2 Theta).
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.initial_residual_gram_from_affine_moments`, `TauCeti.DavisKahan1970.Section9.residualGram_eigenvalueHigh_charAt`, `TauCeti.DavisKahan1970.Section9.equation_9_1`, `TauCeti.DavisKahan1970.Section9.equation_9_4`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamSinTheta_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamSinTwoTheta_lt`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamPerturbation_comp_trialIncl_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamSpecProjection_lowSet_eq_singleton`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamSinTwoThetaSum_lt`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamKyFanTwo_gaugeReal_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTrialVec_span_eq_top`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.exists_beamTrialVec_repr`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamResidual_gram`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamGram_orthogonal_direction`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamResidualRankOne_rank_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamResidual_sub_rankOne_apply`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamResidual_orthogonal_norm_sq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamResidual_sub_rankOne_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.approximationSingularValue_one_beamResidual_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.kyFanTwo_beamResidual_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamSinThetaSum_le`, `TauCeti.DavisKahan1970.Section9.equation_9_2`, `TauCeti.DavisKahan1970.Section9.equation_9_3`
- **Assessment:** The residual Gram matrix, its two characteristic roots, exact radical bounds, and the printed rational relaxations are represented. The actual sine and double-angle theorem outputs are still bridge hypotheses pending integration with the maintained theorem APIs.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The arithmetic is compiled and axiom-clean; the printed conclusions are certificate fields rather than applications of the source-facing sine and tangent theorems.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**(9.1) AND (9.2) ARE NOW DERIVED, NOT ASSUMED (2026-08-07, Opus 5).**

* `beamSinTheta_le` is equation (9.1) for `beamOperator`: the sine of the angle between
  the affine trial subspace and the exact low spectral subspace of `beamOperator + eps t`
  is at most `residualTopSingularValue eps / 500`.  Every input is proved: the trial space
  is the operator's kernel, the gap comes from the selecting set `Ici 500` (so the
  spectrum-avoidance hypothesis is discharged by the set-localization lemma, not assumed),
  and the residual bound `norm_beamPerturbation_comp_trialIncl_le` is the exact `t^2`-moment
  inequality.  Its constant is sharp: the discriminant of the difference form vanishes
  identically, which is why the proof needs the exact `(11 + sqrt 76)/30` and not a
  convenient over-estimate.
* `beamSinTwoTheta_lt` is equation (9.2).  The `sin 2Theta` theorem needs form bounds on the
  free beam's low spectral block, and the set-based localization lemma provably cannot
  supply them (`B subset Icc beta alpha` and `B^c cap Ioo (beta-delta) (alpha+delta) = empty`
  are jointly unsatisfiable).  They come from the operator instead:
  `realSpectrum_beamOperator_subset_sharp` sharpens the gap from the paper's rounded 500 to
  500.5 by using `4.73 < beta` directly (`4.73^4 = 500.5466...`), every nonzero point below
  500.5 is then a resolvent point, so the spectral measure of `Iic 500.5 \ {0}` vanishes and
  `beamSpecProjection_lowSet_eq_singleton` collapses the whole low projection onto the
  kernel eigenvalue `{0}`.  Both form bounds are then 0.  The sharpened gap is also exactly
  what makes the printed *strict* inequality come out: `4 eps/1001 < 2 eps/500`.

**WHAT IS LEFT ON THIS ROW.**  Equations (9.3) and (9.4) are the two-term Ky Fan sums.  Both
need the ideal-gauge forms of the same two theorems (`sinTheta_unbounded_gauge_of_spectrum_gap`,
`sinTwoTheta_addBounded_gauge_of_spectrum_gap`), which are already proved; what is missing is
the gauge arithmetic.  (9.4) needs only `kyFan_2 gauge (eps t) <= 2 eps`.  (9.3) is the harder
one: it needs the Ky Fan 2 gauge of the rank-two residual to be at most
`residualKyFanTwo eps`, i.e. *both* singular values of the residual Gram matrix, where (9.1)
needed only the top one.

**(9.4) ALSO DERIVED (2026-08-07, Opus 5).**  `beamSinTwoThetaSum_lt`.  The ideal-gauge
form of the double-angle theorem was already proved; what was missing was the gauge
arithmetic.  `beamKyFanTwo` is the two-term Ky Fan family over the beam space; every
bounded operator is a member (the gauge is a finite sum of approximation numbers, so it
never reaches infinity), and `beamKyFanTwo_gaugeReal_le` bounds it by twice the operator
norm because both summands are.  Three of this row's four bounds are now derived.

**WHAT (9.3) STILL NEEDS, precisely.**  `sinTheta_unbounded_gauge_of_spectrum_gap` with the
same data as (9.1) reduces it to `kyFan_2 gauge (residual) <= residualKyFanTwo eps`, i.e.
`a_0 + a_1 <= residualTopSingularValue eps + residualBottomSingularValue eps`.  `a_0` is
`norm_beamPerturbation_comp_trialIncl_le`, already proved.  `a_1` needs an explicit rank-one
approximant, which needs the top eigendirection of the residual Gram matrix: with
`c = -(sqrt 75 + sqrt 76)` the eigenvector is `phi_1 + c phi_2` in the orthonormal trial
basis, and the eigenvalue identity reduces to `(sqrt 75 + sqrt 76)(sqrt 75 - sqrt 76) = -1`,
so the radical arithmetic is clean.  The Lean cost is the rank-one operator and the fact
that `{phi_1, phi_2}` spans `beamTrial` (equivalently `finrank beamTrial = 2`).  Note that
no shortcut through `a_1 <= a_0` works: `2 * residualTopSingularValue / 500` exceeds the
printed `109/50000 * eps`.

**(9.3): THE TWO PIECES THE PREVIOUS NOTE NAMED AS "THE LEAN COST" ARE NOW PROVED (2026-08-07, Claude Opus 5).**  The bound itself is NOT yet proved and this row stays `partial_or_wrapper_missing`; what changed is that the two facts the route needs, and only those, are compiled and axiom-clean.

* `beamTrialVec_span_eq_top` and `exists_beamTrialVec_repr`: `{phi_1, phi_2}` spans the trial subspace, i.e. `finrank beamTrial = 2` and every trial vector is `alpha phi_1 + beta phi_2`.  Proved without any change-of-basis radical arithmetic: `beamTrial` is a span of two elements so `finrank <= 2` by `rank_span_le`, the two trial vectors are orthonormal hence independent so `finrank >= 2`, and `Submodule.eq_top_of_finrank_eq` closes it.
* `beamGram_orthogonal_direction`: the radical identity `c^2 (11 - sqrt 75) + 2c + (11 + sqrt 75) = (1 + c^2)(11 - sqrt 76)` for `c = -(sqrt 75 + sqrt 76)`, i.e. the statement that the direction `c phi_1 - phi_2` orthogonal to the top eigenvector carries exactly the LOWER Gram eigenvalue.  This is `(sqrt 75 + sqrt 76)(sqrt 75 - sqrt 76) = -1` in disguise.  `nlinarith` does not find it; it is closed by `linear_combination` with the explicit coefficients `(eps^2/30)(-sqrt 75 - sqrt 76)` on `sqrt 75 ^ 2 = 75` and `(eps^2/30)(sqrt 75 + sqrt 76)` on `sqrt 76 ^ 2 = 76`.
* `beamResidual` and `beamResidual_gram` restate the Gram matrix of (9.1) as inner products of the residual viewed as an operator `beamTrial -> BeamL2`, which is the form the approximation-number argument consumes.

WHAT REMAINS, and it is now purely mechanical assembly: define the rank-one approximant `K x = <w, x> (1 + c^2)^-1 R w` with `w = phi_1 + c phi_2`, show `rank K <= 1`, show `(R - K)(alpha phi_1 + beta phi_2) = ((c alpha - beta)/(1 + c^2)) R (c phi_1 - phi_2)`, and combine with `beamGram_orthogonal_direction` and Cauchy--Schwarz `|c alpha - beta|^2 <= (1 + c^2)(|alpha|^2 + |beta|^2)` to get `||R - K|| <= residualBottomSingularValue eps`, hence `a_1(R) <= residualBottomSingularValue eps` by `ContinuousLinearMap.approximationNumber_le_norm_sub`.  Then `a_0 + a_1 <= residualKyFanTwo eps` with `a_0` from `norm_beamPerturbation_comp_trialIncl_le`, and `sinTheta_unbounded_gauge_of_spectrum_gap` at `beamKyFanTwo` with the (9.1) data gives (9.3).  An attempt at this assembly was made in the same session and NOT completed: the obstacles were purely tactic-level (`simp` normalising `<x,x>` to `||x||^2` before the sesquilinear expansion, and `match_scalars`/`field_simp` on the complex coefficient identity), not mathematical.

**(9.3) IS PROVED 2026-08-07 (Claude Opus 5).  ALL FOUR OF (9.1)--(9.4) ARE NOW DERIVED FROM THE GENUINE FREE-BEAM OPERATOR, AND THIS ROW IS UPGRADED TO `compiled_exact` / `proved_in_build` WITH NO BLOCKER.**

`beamSinThetaSum_le` : `beamSinThetaSum eps <= residualKyFanTwo eps / 500`, where `beamSinThetaSum` is the two-term Ky Fan gauge of `beamTrialIncl* . F_1`, the same object (9.1) bounds in operator norm.  Axiom-clean: [propext, Classical.choice, Quot.sound].  Nothing is stated relative to `FreeBeamFiniteDataCertificate` or `TheoremOutputCertificate`; the warning recorded on the `section9-certificate-discharge` blocker is respected.

The route was the one this row's own notes specified, and it worked as specified.

* `beamResidual eps := beamPerturbation eps . beamTrialIncl`, viewed as an operator `beamTrial -> BeamL2`; `beamResidual_gram` restates the (9.1) Gram matrix as its inner products.
* `beamTrialVec_span_eq_top` / `exists_beamTrialVec_repr`: `finrank beamTrial = 2` and every trial vector is `alpha phi_1 + beta phi_2`.
* `beamGramTopVector := phi_1 + c phi_2` with `c = -(sqrt 75 + sqrt 76)`, and `beamResidualRankOne` the residual composed with the orthogonal projection onto it; `beamResidualRankOne_rank_le` gives rank at most one from `range <= span {v}` and `rank_span_le`.
* `beamResidual_sub_rankOne_apply`: the error is EXACTLY `((c alpha - beta)/(1 + c^2))` times the residual of the orthogonal direction `c phi_1 - phi_2`.  This is an identity, not an estimate.
* `beamResidual_orthogonal_norm_sq` + `beamGram_orthogonal_direction`: that direction carries `(1 + c^2)` times the LOWER Gram eigenvalue.  The radical content is `(sqrt 75 + sqrt 76)(sqrt 75 - sqrt 76) = -1`; `nlinarith` does not find it and `linear_combination` with explicit coefficients on `sqrt 75 ^ 2 = 75` and `sqrt 76 ^ 2 = 76` does.
* `norm_beamResidual_sub_rankOne_le`: Cauchy--Schwarz `|c alpha - beta|^2 <= (1 + c^2)(|alpha|^2 + |beta|^2)` turns the identity into `||R - K|| <= residualBottomSingularValue eps`.  This is the sharp Eckart--Young step for this residual.
* `approximationSingularValue_one_beamResidual_le` then follows from `ContinuousLinearMap.approximationNumber_le_norm_sub`, and `kyFanTwo_beamResidual_le` adds it to `norm_beamPerturbation_comp_trialIncl_le` for `a_0`.
* `beamSinThetaSum_le` finishes by `sinTheta_unbounded_gauge_of_spectrum_gap` at `beamKyFanTwo` with the same data (9.1) uses, transporting the residual gauge across the isometric spectral inclusion by `kyFanApproximationGauge_comp_le` and `kyFanApproximationGauge_adjoint`.

The printed decimal is NOT restated here: `initial_kyFanTwo_exact_lt_printed` already proves `residualKyFanTwo eps / 500 < 109/50000 * eps`, and (9.1), (9.2) and (9.4) likewise stop at the exact bound.  Combining the two is a one-line `lt_of_le_of_lt` at any consumer; it is not done inside `BeamSection9.lean` because that would require importing `Section9/NumericalBounds.lean` and add a new `GENERIC_IMPORTS_SOURCE` finding to a module already carrying baseline ones.

A LEAN-LEVEL NOTE THAT COST TIME AND SHOULD BE REUSED: on a `Submodule`'s induced inner-product space, `rw`/`simp` with `inner_smul_left` / `inner_smul_right` / `inner_self_eq_norm_sq_to_K` silently fail to match, while `inner_add_left` / `inner_add_right` succeed.  Push the computation to the ambient space with `Submodule.coe_inner` (whose orientation is submodule-inner = ambient-inner-of-coercions, so the FORWARD direction is the one that fires) and everything works.  Plain `simp` is also wrong here: it rewrites `<x,x>` to `||x||^2` before the sesquilinear expansion.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 25 is UPHELD: the row is titled for
equations (9.1)--(9.4) and listed the source-facing wrappers for only (9.1) and (9.4).
`Section9.equation_9_2` and `Section9.equation_9_3`
(`DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:239,246`) are both load-bearing and
both resolve from `DavisKahan.All`; verified by elaboration 2026-08-09 and now listed.  No status
change: the beam-side derivations `beamSinTwoTheta_lt` and `beamSinThetaSum_le` were already on the row
and the row's judgement was already correct.
- **Next action:** Nothing.  (9.1), (9.2), (9.3) and (9.4) are all derived from `beamOperator` with no certificate field in any statement, and all are in the default build.

#### Equations (9.5)–(9.7): Rayleigh–Ritz tangent refinements

- **Kind:** `numerical_claims`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** Use the compressed trial operator and orthogonal residual to obtain sharper tan Theta and tan(2 Theta) bounds.  (9.5), both sentences of (9.6), and the bound-norm sentence of (9.7) are now unconditional theorems about the genuine perturbed beam, with no certificate record in any statement.  What is absent is the 2-norm sentence of (9.7) -- `tan 2theta_1 + tan 2theta_2` -- which needs the arbitrary-unitarily-invariant-ideal form of the unbounded residual tan(2 Theta) theorem; that endpoint is not proved anywhere in the repository (see DK-6-appendix).  The row is therefore a specialization, not conditional.
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.recentered_residual_gram_from_affine_moments`, `TauCeti.DavisKahan1970.Section9.equation_9_5_low`, `TauCeti.DavisKahan1970.Section9.equation_9_6`, `TauCeti.DavisKahan1970.Section9.equation_9_7`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamResidual_inner_trial`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamRitzResidual_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamRitz_form_le`, `TauCeti.DavisKahan1970.Section9.equation_9_5_high`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamPerturbed_specProjection_Ioo_eq_zero`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTanTheta_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTanTheta_lt_printed`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamRitzResidual_sq_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamRitzResidual_vecOne_add_vecTwo_eq_zero`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTrialBlock_residual_vecOne_add_vecTwo`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTrialBlock_residual_vecTwo`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTrialBlock_residual_rank_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.approximationSingularValue_one_beamTrialBlock_residual_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.kyFanTwo_beamTrialBlock_residual_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTanThetaSum_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTanThetaSum_lt_printed`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamComparison_reduces`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamRitzOffDiagonal_isOddFor`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamRitzOffDiagonal_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamComparison_form_le_of_mem_beamTrial`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamComparison_form_ge_of_mem_orthogonal`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowReflection_comm`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTanTwoTheta_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTanTwoTheta_lt_printed`
- **Assessment:** The Ritz compression, rank-one recentered residual, singular-value scalars, exact tangent envelopes, and decimal corollaries are present as a candidate. The unbounded tan-theta and tan-two-theta instantiations remain to be connected.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The exact radical arithmetic is compiled and axiom-clean; the tangent and double-angle theorems are not yet instantiated in place of the certificate fields.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**FRESH AUDIT 2026-08-07 (Claude Opus 5).  THE RECORDED `next_action` IS WRONG: THIS IS NOT THEOREM INSTANTIATION.**

The target is exact and identified.  `tangentThetaExactBound eps = ((sqrt 15/15)/500 * eps) / (1 - (ritzHighCoefficient/500) * eps)`, which is `(eps * sqrt 15/15) / (500 - ritzHigh eps)`.  So the intended instantiation is: residual norm = `orthogonalResidualSingularValue eps = |eps| sqrt 15/15`, gap `delta = 500 - ritzHigh eps`, compression form bound `alpha = ritzHigh eps`.  The endpoint that would consume that data exists and is strong enough: `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_ideal_directedTangent`, which gives `delta * N.gauge (tanTheta) <= N.gauge D.residual` for every Fan-dominant unitary-invariant ideal, with the tangent representative exhibited rather than assumed.

WHAT ACTUALLY BLOCKS IT is its hypothesis

    specProjection hA (Set.Ioo alpha (alpha + delta)) = 0

which is a genuine spectral gap for the PERTURBED operator `beamPerturbed eps`, i.e. no spectrum in `(ritzHigh eps, 500)`.  Equations (9.1), (9.2) and (9.4) never needed such a thing: they are stated against a spectral *set* (`beamHighSet = Ici 500`, `beamLowSet = Iic 500.5`) and the corresponding restriction's spectrum lies inside that set by construction, so `beamHigh_spectrum_avoids` and `beamLow_semibounded{Below,Above}` are free.  There is no set-localized tangent endpoint, and there cannot be a free one: the tangent theorem needs the two spectra separated, not merely one of them localized.

The gap is TRUE and the reason is Rayleigh--Ritz.  `beamPerturbation eps` is a positive perturbation (`0 <= eps t <= eps` on the unit interval), so eigenvalues only increase; `realSpectrum_beamOperator_subset_sharp` puts the unperturbed spectrum in `{0} u (500.5, inf)`, so the third eigenvalue of `beamPerturbed eps` is still above `500`, while the two low ones are at most the Ritz values `ritzLow eps <= ritzHigh eps` by the Rayleigh--Ritz upper bound.  Hence `(ritzHigh eps, 500)` is spectrum-free.

FORMALIZING THAT is the real remaining work on this row, and it is new analysis, not instantiation: a min--max / Rayleigh--Ritz upper bound for the second eigenvalue of an unbounded self-adjoint operator, plus monotonicity of the spectrum under a positive bounded perturbation.  Its natural owner is `SelfAdjointSpectralTheory` (`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/`), not Section 9 -- it is exactly the "unbounded self-adjoint spectrum" material the roadmap assigns there.

The beam-specific half is separately available and is the recommended next step: build `UnboundedTrialBlock (beamPerturbed eps) beamTrial` whose `operator` is the Ritz compression (`beamRitz_matrix` already proves it is `diag (ritzLow eps) (ritzHigh eps)`, giving `hCompression` immediately) and whose `residual` is the Rayleigh--Ritz residual `(1 - P_Z) . H|_Z`, whose Gram matrix is `orthogonalResidualGram eps = (eps^2/30) [[1,-1],[-1,1]]` and whose norm is therefore exactly `orthogonalResidualSingularValue eps`.  That computation is the direct analogue of the (9.3) work on DK-9.1-9.4 and needs the orthonormal expansion `starProjection x = <phi_1,x> phi_1 + <phi_2,x> phi_2`, which follows from `beamTrialVec_span_eq_top`.

**PART (a) OF THE ROUTE IS PROVED 2026-08-07 (Claude Opus 5).**  Both pieces of trial-block data that `theorem6_3_unbounded_ideal_directedTangent` consumes now exist for the genuine beam, axiom-clean and in the default build.  The row stays `partial_or_wrapper_missing` because part (b), the perturbed spectral gap, is untouched.

* `norm_beamRitzResidual_le` : `||R x - P_Z (R x)|| <= orthogonalResidualSingularValue eps * ||x||`, i.e. the Rayleigh--Ritz residual norm is exactly `|eps| sqrt 15 / 15`, the operator-norm content of the RECENTERED Gram matrix `orthogonalResidualGram eps = (eps^2/30)[[1,-1],[-1,1]]` whose nonzero eigenvalue is `eps^2/15`.  Proved WITHOUT computing the orthogonal projection: the projection is the nearest point of the trial subspace (`Submodule.starProjection_minimal` + `ciInf_le`), so testing against the explicit competitor `ritzLow eps * alpha * phi_1 + ritzHigh eps * beta * phi_2` suffices, and the resulting form collapses to `(eps^2/30) |alpha - beta|^2 <= (eps^2/15)(|alpha|^2+|beta|^2)`.  The one non-ring input is `sqrt 3 ^ 2 = 3`, supplied to `linear_combination` with the explicit coefficient `-(eps^2/36)(|alpha|^2+|beta|^2)`; the recentering identities `a00 - ritzLow^2 = a11 - ritzHigh^2 = eps^2/30` are exactly what that coefficient encodes.
* `beamRitz_form_le` : `re <R x, x> <= ritzHigh eps * ||x||^2` for `eps >= 0`, which is the `hCompression` hypothesis verbatim.  It is `beamRitz_matrix` read in coordinates: the compression is diagonal with entries `ritzLow eps` and `ritzHigh eps`, and `ritzHigh_sub_ritzLow` orders them.
* `beamResidual_inner_trial` packages the Ritz matrix as the four inner products both computations consume, including the transposed vanishing entry obtained from `beamPerturbation_isSelfAdjoint`.

WHAT REMAINS IS EXACTLY PART (b), and nothing else: assemble `UnboundedTrialBlock (beamPerturbed eps) beamTrial` from these (its `operator` is the compression and its `operator_apply`/`residual_apply` fields are the projection identities, with `A.toLinearMap` on the trial reducing to `beamPerturbation eps` by `beamOperator_apply_trial`), and prove `specProjection (beamPerturbed eps) (Ioo (ritzHigh eps) 500) = 0`.

**PART (b) IS DISCHARGED AND (9.6) IS DERIVED ON THE GENUINE OPERATOR.  ROW WAS STALE; CORRECTED 2026-08-09 (Claude Opus 5).  STATUS `partial_or_wrapper_missing` -> `compiled_specialization`.**

The `next_action` above says part (b), the perturbed spectral gap, "is untouched" and is "the genuinely new piece".  It was proved at commit `b5442743` and the census was never updated:

* `beamPerturbed_specProjection_Ioo_eq_zero (eps) (0 <= eps) : specProjection (beamPerturbed_isSelfAdjoint eps) (Ioo (ritzHigh eps) 500) = 0` (`SpectralTheory/FormMethod/BeamSection9.lean`), proved through `specProjection_Ioo_eq_zero_of_rayleighRitz` at the trial subspace -- which is exactly the Rayleigh--Ritz second-eigenvalue bound the row asked for, and it landed in `SelfAdjointSpectralTheory`, the owner the row named.
* `beamTanTheta_le (eps) (0 < eps) (eps < 100) : beamTanTheta eps <= tangentThetaExactBound eps` and `beamTanTheta_lt_printed`, giving the printed decimal `tan theta_1 < 0.0005164 eps / (1 - 0.0015774 eps)` (`SpectralTheory/FormMethod/BeamTangent.lean`).  `beamTanTheta eps` is `||theorem63DirectedTangent beamTrial (specSubspace (beamPerturbed eps) (Iic (ritzHigh eps)))||` -- the tangent between the affine trial subspace and the EXACT low spectral subspace of `A + eps t`.  No certificate field occurs in the statement and the only hypotheses are the paper's `0 < eps < 100`.  Both axiom-clean and in the default build.

(9.5) is likewise on the genuine operator: `equation_9_5_low` / `equation_9_5_high` give the two Ritz values in the paper's closed form, and `beamRitz_matrix` proves the compression really is `diag (ritzLow eps) (ritzHigh eps)`.

**WHAT IS LEFT, PRECISELY -- AND IT IS WHY THE ROW IS NOT `compiled_exact`.**

* **(9.7) entirely.**  There is no `beamTanTwoTheta` anywhere in the repository.  `equation_9_7` is still the conditional scalar wrapper `(h : tanTwoTheta_1 <= tangentTwoThetaExactBound eps) -> ...`, and its only supplier is the never-constructed `TheoremOutputCertificate`.  Producing it needs the double-angle tangent theorem applied to `beamPerturbed eps` with `A_1` replaced by the compression `E_1^* (A+H) E_1`, which is the paper's own extra step at (9.7) and has no operator-level analogue here yet.
* **The second sentence of (9.6) and of (9.7)**: "the same bound applies to `tan theta_1 + tan theta_2` in the 2-norm".  `beamTanTheta_le` instantiates the unbounded Theorem 6.3 at `KyFanDominantIdealFamily.kyFan 1`; the two-term sum needs the same call at `kyFan 2` and a Ky Fan 2 bound on the recentered residual, both of which exist in kind (`kyFanTwo_beamResidual_le` is the analogue already proved for (9.3)) but neither of which is written for the Rayleigh--Ritz residual.

The row therefore keeps `proved_conditional`: two of its three equations are now derived from the operator with no certificate anywhere in the statement, and the third is still stated relative to a record nobody inhabits.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 24 is UPHELD as a VISIBILITY defect,
not a factual one.  The audit objects that a blanket `compiled_specialization` / `proved_conditional`
hides that (9.7) is the sole obstruction.  The row's notes already said exactly that, in detail, and
were re-checked against the build on 2026-08-09 and found correct: `equation_9_5_{low,high}` and
`beamRitz_matrix` give (9.5) on the genuine operator, `beamTanTheta_le` / `beamTanTheta_lt_printed`
give (9.6)'s first sentence unconditionally in `0 < eps < 100`, and `equation_9_7` is still the
conditional scalar wrapper whose only supplier is `TheoremOutputCertificate`.  What was wrong is that
none of this was legible from the row's own header fields, which is what a per-row status read sees.
The `summary` now carries it.  Status and verification were correct on that date and have since
been superseded; see the M26 entry below.

**M26, 2026-08-09 (Claude Opus 5).  THE ROW IS OFF `proved_conditional`: NO STATEMENT ON IT IS RELATIVE TO A CERTIFICATE ANY MORE.**

Both items the previous `next_action` listed are now proved for the genuine operator, and neither manufactures a certificate record.

* **(a) The 2-norm sentence of (9.6).**  `beamTanThetaSum_le` / `beamTanThetaSum_lt_printed` (`SpectralTheory/FormMethod/BeamTangent.lean`) run the same unbounded Theorem 6.3 at `KyFanDominantIdealFamily.kyFan 2` and land on the *same* envelope `tangentThetaExactBound eps`, which is exactly what the paper asserts ("the same bound applies to tan theta_1 + tan theta_2 in the 2-norm").  The reason nothing is lost is `kyFanTwo_beamTrialBlock_residual_le`: the recentered residual is *exactly rank one*, so its second approximation number is zero.  Rank one is proved rather than asserted -- `norm_beamRitzResidual_sq_le` (a refactor of the existing `norm_beamRitzResidual_le`, which is now a corollary of it) gives `||(1 - P_Z) R x||^2 <= (eps^2/30) |alpha - beta|^2` in the orthonormal Ritz coordinates, whose value at `alpha = beta = 1` forces `beamRitzResidual_vecOne_add_vecTwo_eq_zero`; the residual therefore kills `phi_1 + phi_2` (a multiple of the constant function, whose image `eps t` is already affine) and its range is the line through the single column.
* **(b) (9.7), bound norm.**  `beamTanTwoTheta_le` / `beamTanTwoTheta_lt_printed` (`SpectralTheory/FormMethod/BeamDoubleTangent.lean`, new) give `tan 2theta_1 < 0.0010328 eps / (1 - 0.0015774 eps)` with hypotheses `0 < eps < 100` only.  The construction follows the paper literally: `beamComparison eps` is `Ahat = E_0 Ahat_0 E_0* + E_1 Ahat_1 E_1*` -- the free beam plus the block-DIAGONAL part of `eps t`, hence a bounded perturbation and self-adjoint -- and `beamRitzOffDiagonal eps` is the off-diagonal defect `Rhat + Rhat*`.  `norm_beamRitzOffDiagonal_le` proves `||B|| <= eps sqrt15/15` by noting that an off-diagonal operator's norm is the larger of its two blocks, that the lower block IS the Rayleigh--Ritz residual (`norm_beamRitzResidual_le`) and that the upper block is its adjoint (proved by a two-line inner-product argument, not by forming an adjoint).  `beamComparison_form_le_of_mem_beamTrial` and `beamComparison_form_ge_of_mem_orthogonal` are the paper's `Ahat_0 < 0.7887 eps` and `Ahat_1 > 500` -- the latter is the sharp free-beam gap `500.5`, which the positive `E_1* H E_1` cannot lower, exactly the paper's argument.  The reflection is `Z = 2 Q - 1` at `Q = specProjection(A + eps t)(Iic 500)`, and `beamLowReflection_comm` proves it reduces the perturbed operator.

The endpoint consumed is `TauCeti.gap_mul_norm_offDiagonalPart_apply_le_of_tendsto` together with `diagonalBlockBound_mul_le_norm_diagonalPart_apply_of_tendsto` (ForTauCeti `DoubleAngle/UnboundedPole.lean`).  Their `BoundedCutoff` family is *constant* here: the trial subspace is finite-dimensional and inside the domain, so `beamTrial.starProjection` is itself a cutoff and the limiting argument degenerates.  `beamTanTwoTheta eps` is the supremum over the trial subspace of `||sin 2Theta_0 x|| / ||cos 2Theta_0 x||`, the two blocks of `Z`; the pole is excluded before the quotient is formed, by the `diagonalBlockBound` lower bound.

All new results report exactly `[propext, Classical.choice, Quot.sound]` and are in the default build.

**WHY THE ROW IS STILL `compiled_specialization` AND NOT `compiled_exact`.**  The paper's sentence after (9.7), "with the same right side bounding tan 2theta_1 + tan 2theta_2 in the 2-norm", is NOT proved and cannot be with what exists.  `TanTwoThetaUnboundedResidual.lean` states the residual-form unbounded tan(2 Theta) theorem at the OPERATOR NORM only, and its own module docstring records that the arbitrary Fan-dominant ideal endpoint `delta * N(tan 2Theta_0) <= 2 N(R)` is open, blocked by `DK-6-appendix`.  The bounded branch-free ideal theorem does exist but requires `A` bounded, and `Ahat` here is the free beam, which is not.  This is an absence, not a conditional statement: nothing on this row is proved relative to an uninhabited record.
- **Next action:** One item, and it is NOT beam work.  The 2-norm sentence of (9.7) needs the arbitrary Fan-dominant unitarily-invariant-ideal form of the *unbounded, residual-form* tan(2 Theta) theorem, `delta * N(tan 2Theta_0) <= 2 * N(R)`.  Prove that in `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedResidual.lean` (its docstring already scopes the gap and points at `DK-6-appendix`), and the beam instance is then the same three lines as `beamTanTwoTheta_le` at `kyFan 2`, since `norm_beamRitzOffDiagonal_le` already bounds the off-diagonal perturbation and the rank-one recentered Gram already kills the second approximation number.  Do NOT re-attempt the perturbed spectral gap, the Rayleigh--Ritz residual norm, or the comparison operator; all three are proved.

#### Equation (9.8): Comparison with Weinberger bounds

- **Kind:** `comparison_claim`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Derive lower-eigenvalue estimates from a 3x3 comparison matrix and compare individual-vector angle bounds.
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.ArrowheadThreeByThree`, `TauCeti.DavisKahan1970.Section9.tangent_sq_le_of_weinberger_sine_sq`, `TauCeti.DavisKahan1970.Section9.equation_9_8_lower`, `TauCeti.DavisKahan1970.Section9.equation_9_8_upper`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTanPhi_low_lt_printed`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTanPhi_high_lt_printed`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTanPhi_low_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTanPhi_high_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamColumn_tangent_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamColumnResidual_low`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamColumnResidual_high`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_equation_9_8_lower`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_equation_9_8_upper`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_equation_9_8`, `TauCeti.DavisKahan1970.Section9.weinberger_sine_sq_le_of_coupled_energy`, `TauCeti.DavisKahan1970.Section9.naive_second_scalar_lower_bound_tripwire`
- **Assessment:** The exact arrowhead characteristic polynomial and the algebraic conversion of Weinberger sine-square bounds to tangent bounds are represented. The historical lower-root theorem is deliberately an explicit certificate rather than an informal O(epsilon^4) assertion.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The arrowhead algebra is compiled and axiom-clean; the root inequality needs the alpha_3 > 500 spectral bound, which does not exist.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

BLOCKER CLEARED 2026-08-04: `free-beam-third-eigenvalue` is resolved. The paper's `alpha_3 > 500` is now the unconditional theorem `FreeBeam.Classical.five_hundred_lt_pow_four_of_characteristic_eq_zero`, proved from `cos beta * cosh beta < 1` on `(0, 4.73]` with no certificate and no existence hypothesis. What still blocks this row is only `free-beam-closed-operator` -- tying the characteristic roots to the spectrum of an actual self-adjoint operator on `L^2(0,1)`.

**FRESH AUDIT 2026-08-07 (Claude Opus 5).  THE STALE `alpha_3 > 500` PROSE IS CORRECTLY FLAGGED, BUT THE ROW IS NOT MECHANICAL EITHER.**

`equation_9_8_lower` and `equation_9_8_upper` are already proved -- but CONDITIONALLY: each takes `h : tanPhi <= weinbergerLower/UpperTangentExactBound eps` as a hypothesis and converts it to the printed decimal.  Discharging the row means producing those two tangent quantities from the beam problem.

`weinbergerUpperTangentExactBound eps` is DEFINITIONALLY `tangentThetaExactBound eps`, so the upper line of (9.8) is downstream of DK-9.5-9.7 and inherits its blocker exactly: the perturbed spectral gap.  The lower line needs in addition the two low roots of `weinbergerComparisonMatrix eps` as certified eigenvalue bounds, fed through `tangent_sq_le_of_weinberger_sine_sq` (which is proved).  That is Weinberger--Lehmann's method, not Davis--Kahan's, and the distillation says so explicitly: "Rather than formalizing an informal asymptotic remainder, the Lean interface asks for certified roots of its exact characteristic polynomial."

So: `alpha_3 > 500` is indeed no longer the obstacle (`realSpectrum_beamOperator_subset_sharp` supplies it), but the row is blocked behind DK-9.5-9.7 plus certified roots of the arrowhead characteristic polynomial.  Do not attempt it before DK-9.5-9.7.

**THE DIRECT ONE-VECTOR HALF IS PROVED 2026-08-08 (Claude Opus 5), UNCONDITIONALLY AND ABOUT THE GENUINE BEAM.**  The paragraph following (9.8) -- "To estimate phi_k directly by our method, apply Theorem 6.3 with E_0 = e_k", giving `tan phi_k < (eps/sqrt 30)/(500 - alpha_k_hat)` -- is now `beamTanPhi_low_lt_printed` and `beamTanPhi_high_lt_printed`, with no certificate field and no hypothesis beyond `0 < eps < 100`.  `beamTanPhi eps v` is the operator norm of the CONSTRUCTED tangent between the line `C . v` and the EXACT spectral subspace of `beamPerturbed eps` below `500`; the printed decimals are obtained by feeding it to the already-proved scalar wrappers `direct_lower_individual_vector_bound` and `direct_upper_individual_vector_bound`, which until now had no argument to consume.

Route.  `beamColumnBlock` is the one-dimensional trial block at a unit Ritz vector: its compression is the scalar Ritz value `alpha_k_hat` (`beamRitz_matrix`) and its residual is the single Ritz column.  `norm_beamColumnResidual_low` / `_high` prove each column has norm EXACTLY `orthogonalResidualColumnNorm eps = |eps| sqrt 30 / 30`, from `residualGram.a_00 - ritzLow^2 = residualGram.a_11 - ritzHigh^2 = eps^2/30`; the only radical content is `sqrt 75 = 5 sqrt 3`.  The gap is `500 - alpha_k_hat` and the chosen reducing subspace is the spectral subspace of `Iic 500`, whose complement carries form at least `500` for free (`le_re_inner_of_mem_orthogonal_selfAdjointSpectralSubspace_Iic`).  No spectral gap for the perturbed operator is used anywhere on this half.

WHY IT WAS UNREACHABLE BEFORE: not beam analysis, but the narrowed unbounded Theorem 6.3.  At `alpha = ritzLow eps` the interval `(ritzLow eps, 500)` contains the upper Ritz level, so the spectrum-free-interval hypothesis is FALSE while the printed hypothesis holds.  The decoupled `theorem6_3_unbounded_ideal_directedTangent_of_reducing` (see S2-unbounded-scope) is what makes the printed derivation available.

WHAT REMAINS ON THIS ROW is the Weinberger comparison proper: `equation_9_8_lower` and `equation_9_8_upper` are still conditional on `tanPhi <= weinbergerLower/UpperTangentExactBound eps`, needing certified low roots of `weinbergerComparisonMatrix eps` (lower line) and DK-9.5-9.7's envelope (upper line).  The paper's own comparison -- that the direct estimates are SHARPER than (9.8) -- is now formalized on the Davis--Kahan side only.

**ORDERING CONSTRAINT LIFTED 2026-08-09 (Claude Opus 5).**  The instruction above, "Do not attempt it before DK-9.5-9.7", was written when that row's perturbed spectral gap was missing.  It is now proved (`beamPerturbed_specProjection_Ioo_eq_zero`) and the tangent envelope it gates is proved (`beamTanTheta_le`), so the dependency is discharged.

The upper line of (9.8) still needs one connection that the envelope does not supply by itself: `weinbergerUpperTangentExactBound` is definitionally `tangentThetaExactBound`, but `equation_9_8_upper` consumes a bound on Weinberger's `tan phi_k` -- the angle between the individual Ritz vector `e_k` and `Range(F_0)` -- and `beamTanTheta_le` bounds the SUBSPACE tangent.  What this repository has for the individual angles is sharper and is Davis--Kahan's, not Weinberger's: `beamTanPhi_low_lt_printed` / `_high_lt_printed`.  So the remaining work on this row is entirely on the Weinberger side, as recorded: certified low roots of `weinbergerComparisonMatrix eps` for the lower line, and a `tan phi` bound at Weinberger's own (weaker) envelope for the upper one.

**EQUATION (9.8) ITSELF IS PROVED UNCONDITIONALLY 2026-08-09 (OpenAI GPT-5.6 Sol; reviewed and verified against the source by Claude Opus 5).**  `beam_equation_9_8_lower`, `beam_equation_9_8_upper` and `beam_equation_9_8` (`DavisKahan/SpectralTheory/FormMethod/BeamWeinberger.lean`) give both printed decimals for the genuine perturbed beam, for every `0 < eps < 100`, with no hypothesis and no certificate field.

ROUTE -- AND IT IS THE PAPER'S OWN.  Immediately after (9.8) Davis--Kahan write "To estimate phi_k directly by our method, apply Theorem 6.3 with E_0 = e_k", obtain `0.0003652 eps / (1 - ...)`, and conclude "which are sharper than (9.8)".  Those sharper estimates are `beamTanPhi_low_lt_printed` and `_high_lt_printed`: numerator `913/2500000` against (9.8)'s `1291/2500000`, with the denominators `1 - 4227/10^7 eps` and `1 - 7887/(5*10^6) eps` IDENTICAL on both sides.  Deriving (9.8) from them is therefore not a workaround for the Weinberger route -- it is the implication Davis--Kahan themselves assert in the sentence following the equation.

WHAT IS DELIBERATELY NOT CLAIMED, AND WHY IT IS NOT A DAVIS--KAHAN OBLIGATION.  Two results in this passage are attributed to other authors:

(a) Weinberger's angle inequality `sin^2 phi_k <= (alphahat_k - alphacheck_k)/(500 - alphacheck_k)`.  This is an UNNUMBERED intermediate display preceding (9.8), not (9.8) itself.  `weinberger_sine_sq_le_of_coupled_energy` (`Section9/WeinbergerAngle.lean`) formalizes its algebraic core, taking the coupled energy split as a HYPOTHESIS rather than deriving it.

(b) the Lehmann optimality sentence, that the two lower eigenvalues of the 3x3 arrowhead are the best lower bounds deducible from `Ahat_0`, `Rhat* Rhat` and `Ahat_1 > 500`.  The arrowhead algebra is in `WeinbergerComparison.lean`; the optimality claim is Lehmann's.

Davis--Kahan themselves mark this boundary: "Weinberger's use both Rayleigh--Ritz upper and lower bounds, and can exploit independent lower-bound information that our results do not use."  Reproducing (a) and (b) means importing Weinberger 1960 and Lehmann, which is external mathematics -- see `dev/external-literature-references.md`.

TRIPWIRE AGAINST THE TEMPTING FALSE SHORTCUT.  `naive_second_scalar_lower_bound_tripwire` compiles a rational counterexample showing that (a) does NOT follow from "alphacheck_k is some scalar lower bound for lambda_k" plus the exterior threshold.  For `T = diag(0, 10, 100)` with threshold `99`, the orthogonal Ritz vectors `w_1 = (18/35, -6/7, 1/35)` and `w_2 = (3/7, 2/7, 6/7)` are also `T`-orthogonal, with Ritz values `52/7` and `520/7`; the valid bound `alphacheck_2 = 10 = lambda_2` gives `(520/7 - 10)/(99 - 10) = 450/623`, while the actual squared defect of `w_2` is `36/49 > 450/623`.  It holds for `k = 1` and fails for `k = 2` because `P_F w_2` carries a component below `alphacheck_2`.  Do not replace Weinberger's coupled hypotheses by the scalar statement merely because the latter has the right type shape.
- **Next action:** Nothing outstanding for the printed equation: both lines of (9.8) are unconditional theorems about the genuine beam, by the paper's own Theorem 6.3 route.

Two OPTIONAL items remain, neither a Davis--Kahan obligation.  (1) Import Weinberger 1960's coupled variational argument to discharge the hypothesis of `weinberger_sine_sq_le_of_coupled_energy`, which would reconstruct the paper's historical derivation rather than its conclusion.  (2) Certify the two low roots of `weinbergerComparisonMatrix eps` and prove Lehmann's optimality claim for them.  The older conditional wrappers `equation_9_8_lower` / `equation_9_8_upper` are retained as the interface those would feed; they are superseded as the route to (9.8).

#### Section 9, l2 example after (9.8): Residual-infinite limitation example

- **Kind:** `example`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** An l2 trial vector has a useful Rayleigh quotient but lies outside the perturbed operator domain, so residual-based theorems do not apply while lower-bound methods still do.
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_eq_one`, `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_partial_energy`, `TauCeti.DavisKahan1970.Section9.truncatedDiagonalImage_energy`, `TauCeti.DavisKahan1970.Section9.diagonalOperator`, `TauCeti.DavisKahan1970.Section9.geometricTrial_notMem_diagonalDomain`, `TauCeti.DavisKahan1970.Section9.geometricTrial_form_summable`, `TauCeti.DavisKahan1970.Section9.truncatedTrial_mem_diagonalDomain`, `TauCeti.DavisKahan1970.Section9.diagonalOperator_domain`, `TauCeti.DavisKahan1970.Section9.diagonalOperator_isSelfAdjoint`, `TauCeti.DavisKahan1970.Section9.diagonalOperator_isSymmetric`, `TauCeti.DavisKahan1970.Section9.dense_diagonalDomain`, `TauCeti.DavisKahan1970.Section9.geometricTrial_hasSum_sq`, `TauCeti.DavisKahan1970.Section9.geometricTrial_norm_sq`, `TauCeti.DavisKahan1970.Section9.geometricTrial_hasSum_form`, `TauCeti.DavisKahan1970.Section9.geometricTrial_rayleighQuotient`, `TauCeti.DavisKahan1970.Section9.geometricTrial_normalizedForm_apply`, `TauCeti.DavisKahan1970.Section9.geometricTrial_hasSum_normalizedForm`, `TauCeti.DavisKahan1970.Section9.geometricTrial_hasSum_normalizedFormTail`, `TauCeti.DavisKahan1970.Section9.geometricTrial_normalizedForm_zero`, `TauCeti.DavisKahan1970.Section9.geometricTrial_normalizedForm_split`, `TauCeti.DavisKahan1970.Section9.firstEigenvector`, `TauCeti.DavisKahan1970.Section9.firstEigenvector_def`, `TauCeti.DavisKahan1970.Section9.firstEigenvector_apply`, `TauCeti.DavisKahan1970.Section9.norm_firstEigenvector`, `TauCeti.DavisKahan1970.Section9.firstEigenvector_mem_diagonalDomain`, `TauCeti.DavisKahan1970.Section9.diagonalOperator_firstEigenvector`, `TauCeti.DavisKahan1970.Section9.inner_geometricTrial_firstEigenvector`, `TauCeti.DavisKahan1970.Section9.cos_angle_geometricTrial`, `TauCeti.DavisKahan1970.Section9.sin_angle_geometricTrial`, `TauCeti.DavisKahan1970.Section9.geometricTrial_weinberger_sin_sq_le`, `TauCeti.DavisKahan1970.Section9.geometricTrial_weinberger_best_sin_sq_le`, `TauCeti.DavisKahan1970.Section9.geometricTrial_weinberger_best_sin_le`, `TauCeti.LinearPMap.lpDiagonal`, `TauCeti.LinearPMap.lpDiagonal_isSelfAdjoint`, `TauCeti.LinearPMap.lpDiagonal_isSymmetric`, `TauCeti.LinearPMap.dense_lpDiagonal_domain`, `TauCeti.LinearPMap.adjoint_domain_le_lpDiagonal_domain`, `TauCeti.LinearPMap.lpDiagonalDomain`, `TauCeti.LinearPMap.mem_lpDiagonalDomain_iff`, `TauCeti.LinearPMap.lpDiagonal_domain`, `TauCeti.LinearPMap.lpDiagonal_apply`, `TauCeti.LinearPMap.single_mem_lpDiagonal_domain`, `TauCeti.LinearPMap.lpDiagonal_single`
- **Assessment:** The pointwise constant image and divergent finite partial energies are formalized algebraically, together with an explicit finite-support truncation repair that agrees on arbitrary prescribed prefixes.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_specialization`. The sequence lemmas are compiled, axiom-clean and unconditional, but stated for coordinate sequences rather than in the abstract operator setting the source example describes.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**ROW WAS STALE; CORRECTED 2026-08-09 (Claude Opus 5).  THE OPERATOR LIFT ASKED FOR IN `next_action` IS DONE.**

The row listed only the three coordinate-sequence lemmas and asked, optionally, to "lift them from coordinate sequences to the abstract operator setting".  The lift exists, in the same module (`Sources/DavisKahan1970/Section9/DomainLimitation.lean`, reached from `DavisKahan.All` through `Section9/All.lean`), and every piece is axiom-clean:

* `DomainLimitationSpace := lp (fun _ : Nat => R) 2` and `diagonalDomain d`, the MAXIMAL domain `{x : (d n * x n) in l^2}` as a genuine `Submodule`;
* `diagonalOperator (d : Nat -> R) : DomainLimitationSpace ->l. [R] DomainLimitationSpace`, the unbounded diagonal operator as a Mathlib `LinearPMap` -- the canonical carrier this repository has settled on;
* `geometricTrial hmu0 hmu1 : DomainLimitationSpace`, the source's `e = (1, mu, mu^2, ...)`, together with `geometricTrial_notMem_diagonalDomain`: the trial VECTOR is genuinely outside the operator's domain, because its image is the constant sequence.  That is the source's actual claim, and it is now about an operator and a vector rather than about two sequences;
* `geometricTrial_form_summable`: the quadratic form `sum d_n |x_n|^2` converges on the same vector -- the asymmetry the paragraph exists to exhibit;
* `truncatedTrial_mem_diagonalDomain` and `truncatedTrial_eq_geometricTrial_of_lt`: the "arbitrarily small change remedies this" repair, in the domain and agreeing on every prescribed prefix.

**WHAT IS GENUINELY ABSENT, AND WHY THE ROW STAYS `compiled_specialization`.**  The second half of the same paragraph is not formalized at all:

* the Rayleigh quotient `alphaHat = e^*(A+H)e / e^*e = 1 + mu`.  `geometricTrial_form_summable` shows the numerator converges but never evaluates it; the arithmetic is `(1/(1-mu)) / (1/(1-mu^2)) = 1 + mu`;
* self-adjointness of `diagonalOperator` on its maximal domain, which is what makes "the Rayleigh quotient is useful" mean anything and is a prerequisite for any spectral statement about it;
* Weinberger's conclusion `sin^2 theta <= (1 + mu - alphaCheck_1)/(alphaCheck_2 - alphaCheck_1)` and its best-lower-bound consequence `sin theta <= mu / sqrt(1 - mu)`, which is the point of the paragraph -- the residual-based theorems do not apply while a lower-bound method still does.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 26 --
"does not record that `alphahat = 1 + mu` (L2761) is absent" -- IS WRONG, AND THE ROW WAS ALREADY
RIGHT.  Re-read 2026-08-09: the paragraph above beginning "WHAT IS GENUINELY ABSENT" opens with exactly
that item -- "the Rayleigh quotient `alphaHat = e^*(A+H)e / e^*e = 1 + mu`.
`geometricTrial_form_summable` shows the numerator converges but never evaluates it; the arithmetic is
`(1/(1-mu)) / (1/(1-mu^2)) = 1 + mu`" -- and `next_action` repeats it as the first of its three
remaining items.  No change to this row; the finding is recorded here only so the same objection is not
raised a fourth time.

**ALL THREE REMAINING ITEMS ARE COMPILED, 2026-08-10 (Claude Opus 5, coordinator-verified).  THE ROW IS COMPLETE.**

(1) RAYLEIGH QUOTIENT: `geometricTrial_rayleighQuotient` proves the quotient is `1 + mu`, from `hasSum_geometric_of_lt_one` twice -- no partial-sum manipulation.  (2) SELF-ADJOINTNESS: proved as REUSABLE infrastructure, not locally.  New module `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean` gives `lpDiagonal_isSelfAdjoint` over general index type and `RCLike` scalars, by exactly the recorded recipe: test against `lp.single 2 i 1`, read the i-th coordinate of the adjoint image off as `d_i y_i`, conclude that sequence lies in `l^2`, which IS the maximal domain condition.  Section 9's `diagonalDomain` and `diagonalOperator` are now DEFINED AS those declarations at `K = R`, `iota = N`, so the reusable theorem applies to the census-pinned operator rather than to a look-alike.  (3) WEINBERGER: `geometricTrial_weinberger_sin_sq_le` and `geometricTrial_weinberger_best_sin_le` give `sin^2 theta <= (1 + mu - a1)/(a2 - a1)` and `sin theta <= mu / sqrt(1 - mu)`.  `theta` is the honest `InnerProductGeometry.angle`, and `sin_angle_geometricTrial` proves `sin theta = mu`, the source's parenthetical.

NO NARROWING; IF ANYTHING THE HYPOTHESES ARE WEAKER THAN THE SOURCE'S.  The source says `take a small mu << 0.6`; the compiled statements require only `0 < mu < 1`.  (0.6 is the golden-ratio conjugate 0.618..., the threshold below which `mu / sqrt(1 - mu) < 1` and the bound is INFORMATIVE -- a remark about usefulness, not a hypothesis the mathematics needs.)

THE WEINBERGER ESTIMATE ALREADY EXISTED and was grounded on rather than reproved: `weinberger_sine_sq_le_of_coupled_energy` (`Section9/WeinbergerAngle.lean:50`).  Its energy arguments are supplied as the GENUINE normalized energies of this example -- `1 - mu^2` and `mu + mu^2`, computed by `geometricTrial_normalizedForm_zero` and `geometricTrial_hasSum_normalizedFormTail` -- not as asserted numbers.

A COORDINATOR PREMISE WAS WRONG: the brief said to put the diagonal operator in `ForTauCeti`'s `LinearPMap` diagonal/multiplication layer `if it has no such theorem`.  THERE IS NO SUCH LAYER -- none of the 25 modules under `ForTauCeti/.../LinearPMap/` concerns multiplication operators, and the only diagonal layer in `ForTauCeti` is the BOUNDED `diagOpLp` in `ApproximationNumber/DiagonalSequence.lean`, which requires a uniformly bounded multiplier and so cannot serve the unbounded case.  The module was created.

RECORDED, not a regression: this work moves the per-declaration `@[expose]` count from 162 to 164 (two documented api-design carve-outs, `lpDiagonalDomain` and `lpDiagonal`, without which `lpDiagonal_domain`/`lpDiagonal_apply` are not provable as exported theorems).  `check_expose_ratchet.py --check` exits 1 BOTH BEFORE AND AFTER -- the count was already 16x its baseline of 10 at HEAD -- so this is drift in a long-broken ratchet, not a new failure.  The submission ladder was likewise already stale at HEAD (96 findings, 97 after).  Both are recorded for adjudication rather than absorbed silently.
- **Next action:** Nothing outstanding.

#### Equations (9.9)–(9.11) and final bounds: Individual eigenvector identification inside a cluster

- **Kind:** `numerical_claims`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Reduce the full eigenproblem to a two-dimensional Schur complement, then combine tan(2 Theta) and tan Theta bounds to control each eigenvector angle omega_k.
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.half_tanTwoPsi_ratio_lt_of_eigenvalue_upper`, `TauCeti.DavisKahan1970.Section9.block_eigenproblem_iff`, `TauCeti.DavisKahan1970.Section9.schur_complement_reduction`, `TauCeti.DavisKahan1970.Section9.individual_angle_le_exact_envelope`, `TauCeti.DavisKahan1970.Section9.final_lower_individual_angle_bound`, `TauCeti.DavisKahan1970.Section9.NumericalExampleCertificate`, `TauCeti.DavisKahan1970.Section9.norm_lower_coordinate_le`, `TauCeti.DavisKahan1970.Section9.schurCoefficient_nonneg`, `TauCeti.DavisKahan1970.Section9.schurCoefficient_le`, `TauCeti.DavisKahan1970.Section9.lower_coordinate_eq_zero_of_residual_eq_zero`, `TauCeti.DavisKahan1970.Section9.individual_angle_le_exact_envelope_of_tangents`, `TauCeti.DavisKahan1970.Section9.individual_angle_le_exact_envelope_of_subspace`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.rank_beamLowFiveHundred_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.finiteDimensional_beamLowFiveHundred`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.finrank_beamLowFiveHundred`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowFiveHundred_eq_specRange_ritzHigh`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowOperator`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowOperator_isSymmetric`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowEigenbasis`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowEigenvector`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowEigenvalue`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamPerturbed_apply_beamLowEigenvector`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowEigenvector_orthonormal`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowEigenvalue_lt_five_hundred`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_lower_block_equation`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_lower_block_form_ge`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_norm_residual_column_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_norm_orthogonal_part_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_starProjection_ne_zero`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_tan_eta_le`, `TauCeti.DavisKahan1970.Section9.arccos_ratio_lt_pi_div_four`, `TauCeti.DavisKahan1970.Section9.half_tan_two_arccos_ratio`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamRitzColumnMap`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamRitzColumnMap_vecTwo`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamRitzColumnMap_vecOne_sq_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_ritz_compression_vecOne`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_ritz_compression_vecTwo`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_ritz_coordinate_identity`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTrial_starProjection_eq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamTrial_starProjection_sq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_residual_at_starProjection`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_angle_of_ritz_coordinates`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.two_coordinate_schur_identity`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_ritz_scalar_data`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.inplane_ratio_bound`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.schur_gap_bound_of_sum_nonneg`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.schur_gap_bound_of_sum_nonpos`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_individual_angle_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_individual_angle_le_printed`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowEigenvector_individual_angle_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_eigenvalue_le_ritzHigh`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beam_individual_envelope_lt_pi_div_four`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowEigenvector_not_both_near`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamLowEigenvector_ritz_pairing`
- **Assessment:** Equation (9.9) is represented as an explicit block linear map, and equations (9.10)-(9.11) by a generic Schur reduction. The rank-one correction is decomposed into its shifted diagonal and off-diagonal parts, with the exact sqrt(3)/30 coefficient. The final scalar combination producing sqrt(7)/10 and the printed bounds is present. The operator-order resolvent sandwich and actual angle identifications remain certificate fields.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The block reduction and Schur complement are compiled and axiom-clean; the rank-one resolvent order argument that would replace the last certificate fields is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**FRESH AUDIT 2026-08-07 (Claude Opus 5).**  The scalar geometry is complete and correct: `Section9/SchurComplement.lean` has (9.9) as a block map and (9.10)-(9.11) as the Schur reduction for arbitrary modules, `Section9/RankOneCorrection.lean` has the shifted diagonal and off-diagonal parts with the exact `sqrt 3 / 30` coefficient, and `IndividualAngles.combined_individual_coefficient` proves the Euclidean combination is exactly `sqrt 7 / 10`.

`individual_angle_le_exact_envelope` is, like (9.8), CONDITIONAL: it consumes tangent bounds and produces the individual-angle envelope.  Its inputs are the same tangent quantities DK-9.5-9.7 must supply, so this row is downstream of DK-9.5-9.7 too, and the operator-order resolvent sandwich is what would turn the Schur reduction from a scalar identity into a statement about the actual eigenvectors of `beamPerturbed eps`.

RE-RANKED: this row is NOT independently attackable ahead of DK-9.5-9.7.  Its own hard content -- the resolvent order comparison under a positive rank-one perturbation, whose owner would be SelfAdjointSpectralTheory -- sits on top of tangent bounds that do not yet exist for the beam.

**UPDATE 2026-08-08 (Claude Opus 5).**  Two of the three quantities that `individual_angle_le_exact_envelope` used to take as hypotheses are now derived.

* The Pythagorean combination `omega^2 <= psi^2 + eta^2` is no longer assumed.  It follows from the *exact* spherical right-triangle identity `cos omega = cos eta * cos psi`, which holds because the Ritz vector lies in the trial subspace while the out-of-plane part of the eigenvector does not.  Both are proved in `ForTauCeti/Analysis/InnerProductSpace/SphericalPythagoras.lean` and consumed by `individual_angle_le_exact_envelope_of_subspace`.  The inequality is exact on `[0, pi/2]^2`; it is NOT a small-angle approximation.
* The two angle bounds are derived from the tangent bounds the reduction actually produces (`psi <= tan(2 psi)/2` on `[0, pi/4)` and `eta <= tan eta` on `[0, pi/2)`), so no angle is assumed to satisfy a numerical bound.
* `SchurComplement.lean` gained the quantitative half of (9.9)-(9.11) in a form that never inverts anything: testing the lower block equation against the complementary coordinate and using a form lower bound `beta > lam` on the lower block gives `(beta - lam)*‖y‖ <= ‖B x‖`, the nonnegativity and the upper bound `(beta - lam)*(-re <B x, y>) <= ‖B x‖^2` for the Schur coefficient, and the nondegeneracy `B x = 0 -> y = 0` behind `x_k != 0`.  These are exactly the conjugated-resolvent-sandwich consequences the earlier note asked for, obtained WITHOUT constructing `(A_1 - lam)^{-1}` and without needing `A_1` as a self-adjoint partially defined operator on the orthogonal complement.  The generic sandwich in `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/ResolventSandwich.lean` is therefore not on the critical path for this row.

STILL MISSING, and the reason the status does not move: nothing here is yet attached to `beamPerturbed eps`.  The remaining work is the beam block realization -- the two isolated eigenpairs below 500 (the low spectral subspace is known to be two-dimensional, but its eigenbasis is not constructed), the block decomposition over `beamTrial + beamTrialᗮ`, and the identification of the in-plane rotation `psi_k` with the exact 2x2 Jacobi angle of the reduced matrix, whose tangent is `tan(2 psi_k) = 2 q_k / (alphaHat_2 - alphaHat_1)` exactly (the Section 7 tan(2 Theta) machinery is not needed for a 2x2).

**M26, 2026-08-09 (Claude Opus 5).  NOT ATTEMPTED; ONE UPSTREAM FACT CORRECTED.**  The 2026-08-07 note says this row 'is NOT independently attackable ahead of DK-9.5-9.7' because its inputs 'sit on top of tangent bounds that do not yet exist for the beam'.  Those tangent bounds now DO exist: `beamTanTheta_le`, `beamTanThetaSum_le`, `beamTanPhi_low_le`, `beamTanPhi_high_le` and `beamTanTwoTheta_le` are all proved for `beamPerturbed eps`, and `DK-9.5-9.7` is off the certificate blocker.  So the sequencing objection is gone; what remains is this row's own beam realization, untouched.  Concretely still absent: (i) an orthonormal eigenbasis `f_1, f_2` of `beamPerturbed eps` restricted to `beamLowFiveHundred eps` -- the subspace is known to be two-dimensional, but no eigenvectors are constructed, and constructing them needs the restriction to be exhibited as a self-adjoint operator on a two-dimensional space and diagonalised; (ii) the block equations (9.9) against `beamTrial + beamTrialᗮ` for each `f_k`, i.e. the concrete `b`, `w`, `y`, `lam` that `norm_lower_coordinate_le` and `schurCoefficient_le` consume; (iii) the identification of the in-plane angle `psi_k` with the exact 2x2 Jacobi angle of the reduced matrix and the bound `tan(2 psi_k) <= eps^2/(15 (500 - lam_k))`, which in the paper also needs Theorem 8.1 to place `psi_k < pi/4` and the Weinberger--Lehmann lower bounds `alphaCheck_k <= lam_k`; (iv) the out-of-plane bound `tan eta_k <= ||B||/(500 - lam_k)`.  Only after (i)--(iv) does `individual_angle_le_exact_envelope_of_subspace` apply.  No part of this was written, and nothing on this row was changed.

**M29, 2026-08-09 (Claude Opus 5).  THE BEAM BLOCK REALIZATION: THREE OF THE FOUR PIECES LANDED.**  New module `DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean`, 27 declarations, all axiom-clean.

*Correction to the M26 note.*  `finrank (beamLowFiveHundred eps) = 2` was NOT already proved.  What existed was `finrank_beamTrial = 2` together with `beamPerturbed_finrank_le` and `beamTrial_finrank_le`, both of which take `[FiniteDimensional C W]` as a hypothesis and therefore cannot even establish that the spectral range is finite-dimensional.  That gap is now closed: `rank_beamLowFiveHundred_le` promotes the Rayleigh--Ritz cap from finite subspaces to the whole spectral range by testing arbitrary finite linearly independent families, `finiteDimensional_beamLowFiveHundred` and `finrank_beamLowFiveHundred` follow, and `beamLowFiveHundred_eq_specRange_ritzHigh` identifies the low spectral subspace with the spectral range below `ritzHigh eps` -- so `A + eps t` has no spectrum at all in `(ritzHigh eps, 500]`, and `beamLowEigenvalue_lt_five_hundred` gives every low eigenvalue strictly below `500`.

(i) DONE.  `beamLowOperator` exhibits the restriction of `A + eps t` to the low spectral subspace as a symmetric endomorphism of a two-dimensional space; `beamLowEigenbasis` diagonalises it; `beamLowEigenvector` / `beamLowEigenvalue` are honest eigenpairs of the unbounded operator (`beamPerturbed_apply_beamLowEigenvector`), orthonormal in the ambient space.

(ii) DONE for the lower block.  `beam_lower_block_equation` splits the exact eigenvalue equation along `beamTrial + beamTrial^perp` and produces exactly the `b + w = lam . y` shape that `norm_lower_coordinate_le` consumes, with `b` the Rayleigh--Ritz residual column at the trial coordinate; `beam_lower_block_form_ge` supplies `beta = 1001/2`; `beam_norm_residual_column_le` supplies `||b|| <= orthogonalResidualSingularValue eps * ||x||`; `beam_starProjection_ne_zero` is the nondegeneracy.  The *upper* block, needed only for (iii), is not written.

(iv) DONE.  `beam_tan_eta_le` proves `tan eta <= orthogonalResidualSingularValue eps / (1001/2 - lam)`, i.e. `tanEtaCoefficient * eps / (500.5 - lam)`.  The coefficient matches `tanEtaCoefficient = sqrt 15 / 15` exactly and the denominator is better than the printed `500 - lam`, so this is the `htaneta` input of `individual_angle_le_exact_envelope_of_subspace` with room to spare.

(iii) NOT WRITTEN.  **It is NOT gated on external mathematics**, and the route recorded in the M26 note is wrong in two ways.

* The recorded bound `tan(2 psi_k) <= eps^2/(15 (500 - lam_k))` is dimensionally inconsistent with `halfTanTwoPsiCoefficient = sqrt 3 / 30`.  The correct statement is `tan(2 psi_k)/2 <= (sqrt 3/30) eps/(500 - lam_k)`, i.e. `tan(2 psi_k) <= sqrt 3 eps/(15 (500 - lam_k))`.
* The claim that placing `psi_k < pi/4` needs Theorem 8.1 and the Weinberger--Lehmann lower bounds is false as a *necessity* claim.  The branch is decided by `schurCoefficient_nonneg` alone.

The route, entirely inverse-free and using only facts already in the build.  Write `e_1, e_2` for the orthonormal Ritz vectors, `alphaHat_1 = ritzLow eps < alphaHat_2 = ritzHigh eps`, `gamma = alphaHat_2 - alphaHat_1 = eps/sqrt 3`, and `r_j` for the residual column at `e_j`, with `r_1 + r_2 = 0` (`beamRitzResidual_vecOne_add_vecTwo_eq_zero` -- this is the exact rank-one structure of `orthogonalResidualGram`) and `||r_1|| = orthogonalResidualColumnNorm eps = |eps|/sqrt 30`.  Let `f` be a unit eigenvector, `lam` its eigenvalue, `x = P f`, `y = f - x`, `d_j = alphaHat_j - lam`.

1. Testing the eigenvalue equation against `e_j` and using symmetry gives the EXACT pair `d_j <e_j, x> = -<r_j, y>`.  With `r_2 = -r_1` and `rho = <r_1, y>` this reads `<e_1,x> = -rho/d_1`, `<e_2,x> = rho/d_2`; `rho != 0` because `x != 0` (`beam_starProjection_ne_zero`), so `d_1, d_2 != 0`.
2. Hence `B x = (<e_1,x> - <e_2,x>) r_1 = -rho u r_1` with `u = 1/d_1 + 1/d_2`, so `-re <B x, y> = u |rho|^2` and `||B x||^2 = u^2 |rho|^2 eps^2/30`.  `schurCoefficient_nonneg` gives `u >= 0`; `schurCoefficient_le` gives `beta - lam <= u eps^2/30`, i.e. `u >= 30 (beta - lam)/eps^2`.
3. The in-plane angle at `e_1` has `tan psi = |d_1|/|d_2|`, so `tan(2 psi)/2 = d_1 d_2 / ((d_2 - d_1)(d_1 + d_2)) = 1/(gamma u) <= eps^2/(30 (beta - lam) gamma) = (sqrt 3/30) eps/(beta - lam)`.  The printed coefficient comes out exactly, with no slack spent, precisely because the rank-one residual shifts both diagonal entries of the reduced matrix by the same amount, leaving the reduced gap equal to `gamma`.  A cruder route through `||B||` and a triangle inequality overshoots the printed constant by about 1.4 percent, which the `500 -> 500.5` denominator improvement (0.1 percent) cannot absorb; the exact identity is therefore required, not an optimization.
4. The branch.  `d_2 = d_1 + gamma`, so `u > 0` forces either `0 < d_1 < d_2` (then `psi < pi/4` at `e_1`) or `d_1 < 0 < d_2` with `|d_1| > d_2` (then `psi < pi/4` at `e_2`).  No angle theorem, no Theorem 8.1 and no eigenvalue lower bound is needed to place the angle below `pi/4`.

What the *eigenvalue-ordered* pairing `e_1 <-> lam_1`, `e_2 <-> lam_2` additionally needs is `lam_1 < alphaHat_1 < lam_2`.  The left half is the Rayleigh--Ritz upper bound.  The right half is a Lehmann-type lower bound available from `finrank_le_of_le_specRange_Iic` applied with the ONE-dimensional trial space `C . e_1`: the form on `(C . e_1)^perp` is at least `alphaHat_2 - (eps^2/30)/(1001/2 - alphaHat_2)`, which exceeds `alphaHat_1` for `0 < eps < 100` with wide margin.  That is a dimension count, not Weinberger's angle theorem -- which this repository correctly refuses to claim (see `dev/external-literature-references.md`) and which is not needed here.

**M31, 2026-08-09 (Claude Opus 5).  PIECE (iii) LANDED; THE ROW IS DISCHARGED FOR THE GENUINE OPERATOR.**  New module `DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean` (24 declarations) plus two general `Real.arccos` facts added to `Section9/IndividualAngles.lean`.  Every new declaration is axiom-clean (`[propext, Classical.choice, Quot.sound]`), the default build is green at 9562 jobs, and nothing here constructs a resolvent or instantiates a certificate record.

The route recorded in the M29 note survived elaboration step for step, with no correction needed to the mathematics.  What is now proved for `beamPerturbed eps` itself:

* `beam_ritz_coordinate_identity` -- the exact upper-block relation `(alphaHat_j - lam) <e_j, f> = -<r_j, f - P f>`, from symmetry of the operator and the splitting along `beamTrial + beamTrial^perp`.  Combined with `beamRitzColumnMap_vecTwo` (`r_1 + r_2 = 0`) both trial coordinates are governed by the single scalar `rho = <r_1, y>`.
* `two_coordinate_schur_identity` -- the *division-free* replacement for `u = 1/d_1 + 1/d_2`: `d_1 d_2 ||c||^2 = (d_1 + d_2) S`, where `c` is the residual coefficient and `S = -re <B x, y>` the Schur coefficient.  This is why no inverse is ever formed.
* `beam_ritz_scalar_data` -- assembles `|d_j| |<e_j,f>| = |rho|`, the identity above, `0 <= S` from `schurCoefficient_nonneg` and `30 (beta - lam) S <= ||c||^2 eps^2` from `schurCoefficient_le`, with `beta = 1001/2`.
* `inplane_ratio_bound` -- the scalar core.  With `p >= q` the two Ritz coordinates in decreasing order, `tan(2 psi)/2 = p q/(p^2 - q^2) <= gamma/(10(beta - lam)) = (sqrt 3/30) eps/(beta - lam)`, exactly `halfTanTwoPsiCoefficient`.  As predicted, no slack is spent.
* `beam_individual_angle_le` and `beam_individual_angle_le_printed` -- the `sqrt 7/10` envelope for a single exact eigenvector, the second with the printed denominator `500 - lam` (which is weaker than the `500.5 - lam` actually available).  Each carries the *branch*: either `lam <= ritzLow eps` and the lower Ritz vector is inside the envelope, or `ritzLow eps < lam` and the upper one is.
* `beamLowEigenvector_ritz_pairing` -- the printed pairing.  Of the two exact eigenvectors of `A + eps t` below `500`, the one with the smaller eigenvalue is within `(sqrt 7/10) eps/(500 - lambda)` of the lower Ritz vector and the one with the larger eigenvalue within the same envelope of the upper Ritz vector.

The eigenvalue-ordered pairing did NOT need the one-dimensional Lehmann bound suggested in the M29 `next_action`.  It follows from the branch information already carried by the single-eigenvector theorem together with Bessel's inequality (`beamLowEigenvector_not_both_near`): two orthonormal vectors cannot both lie within `pi/4` of one unit vector, and the envelope is below `pi/4` on the whole range `0 < eps < 100` (`beam_individual_envelope_lt_pi_div_four`, using `beam_eigenvalue_le_ritzHigh`, itself a by-product of the sign analysis).  `finrank_le_of_le_specRange_Iic` with a one-dimensional trial space was therefore not used, and the `alphaCheck_k <= lam_k` Weinberger--Lehmann lower bounds remain unclaimed and unneeded.

The M29 correction to the printed bound stands and is confirmed by the compiled statement: the in-plane bound is `tan(2 psi_k)/2 <= (sqrt 3/30) eps/(500 - lam_k)`, i.e. `tan(2 psi_k) <= sqrt 3 eps/(15 (500 - lam_k))`; the `eps^2/(15(500 - lambda_k))` recorded in the M26 note is dimensionally wrong and must not be reinstated.

Not claimed: `beamLowEigenvalue` comes from Mathlib's `IsSymmetric.eigenvectorBasis` and is not sorted, so the pairing is stated for an arbitrary pair of distinct indices ordered by their eigenvalues rather than for the literal indices `0, 1`.  That is a labelling convention, not missing mathematics.

`section9-certificate-discharge` is cleared from this row: nothing in the chain above mentions `FreeBeamFiniteDataCertificate` or `TheoremOutputCertificate`, and no value of either was constructed for it.  `scripts/check_dependency_layers.py` moves from 6 findings to 7, the new one being `BeamInPlaneAngle` importing `Section9/IndividualAngles` -- the same shape as the existing `BeamEigenbasis -> Section9/SchurComplement` entry, since the beam realization is inherently paper-specific.

---

**RETIRED BLOCKER `section9-certificate-discharge`, removed from the blockers table 2026-08-09 when this, its last row, was discharged.  Its text is preserved verbatim here because the standing warning it carries still applies to anyone tempted to "close" a Section 9 row cheaply.**

_Construct the Section 9 certificates (kind: mixed)_

Section 9 compiles, but every source conclusion is stated relative to `FreeBeamFiniteDataCertificate` (Section9/ExactData.lean) or `TheoremOutputCertificate` (Section9/FullExample.lean), and no value of either type is ever constructed.

**WARNING recorded 2026-08-04: DO NOT 'CLOSE' SECTION 9 BY INSTANTIATING THESE RECORDS.** Both are trivially instantiable and instantiating them would certify nothing.

* `TheoremOutputCertificate` declares `sinTheta1 sinTwoTheta1 ... omega2 : R` as FREE reals and then asserts the paper's bounds about them as fields. Taking `sinTheta1 := residualTopSingularValue eps / 500` and so on satisfies every field by `le_refl`. The record states the paper's conclusions; it does not derive them.
* `FreeBeamFiniteDataCertificate` is worse in one specific way: its field `third_eigenvalue : R` with `500 < third_eigenvalue` is **never projected anywhere in the repository** (verified by grep, 2026-08-04 -- the only occurrences are the two declaration lines). The Section 9 arithmetic hardcodes the literal `500` as the gap instead. So that field is dead: it neither constrains the certificate's users nor connects them to an operator. Its other fields are `0 < eps`, `eps < 100`, and four *definitional* equations (`initial_residual_gram = residualGram eps`, etc.) that hold by `rfl`.

What honest discharge requires is the chain in `DavisKahan/Experimental/Frontier/Section9Analytic.lean`, which is laid out correctly and is entirely `sorry`: a `FreeBeamAnalyticModel` carrying the actual closed operator, `RepresentsFreeBeamProblem` tying it to the fourth-derivative problem, the *actual* angle quantities (`actualSinThetaOne` and its seven siblings are `sorry` DEFINITIONS, not just unproved theorems), and `theoremOutputCertificate_of_model`. That needs `free-beam-closed-operator`. Until then the correct status for these rows is exactly what they carry: `proved_conditional`.

**PARTIALLY DISCHARGED 2026-08-07 (Opus 5), and the warning above was respected.**  The
analytic model exists (`beamOperator`), the finite moments are proved to be genuine L^2
integrals against it, and equations (9.1) and (9.2) are now *derived* from the source-facing
sine and double-angle theorems rather than declared as `TheoremOutputCertificate` fields.
`FreeBeamFiniteDataCertificate` is now inhabited, but -- exactly as this blocker warned --
that inhabitation is not the evidence: the evidence is `beamRitz_matrix`,
`beamResidualGram_matrix`, `beamTrial_orthonormal` and `realSpectrum_beamOperator_subset_gap`,
which say what the record cannot.  What still blocks the four remaining Section 9 rows is
(9.3), (9.4), and the tangent, Weinberger and individual-eigenvector conclusions.

**DK-9.1-9.4 IS FULLY OFF THIS BLOCKER 2026-08-07 (Opus 5).**  (9.3) was the last of its four equations still stated relative to a certificate field; `beamSinThetaSum_le` derives it from `beamOperator` through the second approximation number of the residual, realised by an explicit rank-one approximant.  The blocker now constrains only DK-9.5-9.7, DK-9.8 and DK-9.9-9.11.

**TWO CORRECTIONS 2026-08-09 (Claude Opus 5), from `dev/davis-kahan-1970-final-audit-2026-08-09.md` disagreement 22; both verified, not inferred.**

(1) THE DISCHARGE ROUTE NAMED ABOVE NO LONGER EXISTS.  The paragraph beginning "What honest discharge requires is the chain in `DavisKahan/Experimental/Frontier/Section9Analytic.lean`" points at a file DELETED at commit `95bbd5ea` ("Retire the sorried Section 9 skeleton"), and `DavisKahan/Experimental/Frontier/` now contains only `All.lean` and `README.md`.  It is retained above as the historical record of why the certificates must not simply be inhabited -- that warning still stands and is still the point of this blocker -- but it is NOT the current plan.  The current analytic model is `beamOperator` (`DavisKahan/SpectralTheory/FormMethod/BeamFormSpace.lean`), which is constructed, self-adjoint and axiom-clean, and the remaining conclusions must be derived from IT.

(2) THIS BLOCKER NO LONGER CONSTRAINS `DK-9.8`.  The sentence above says it constrains "DK-9.5-9.7, DK-9.8 and DK-9.9-9.11".  `DK-9.8` correctly carries `blocked_by: []`: `beam_equation_9_8` was elaborated 2026-08-09 and is unconditional in `0 < eps < 100`, mentions no certificate field, and reports `[propext, Classical.choice, Quot.sound]`.  The blocker now constrains exactly `DK-9.5-9.7` and `DK-9.9-9.11`, and what it constrains there is (9.7), the 2-norm tangent sums, and the individual `omega_1, omega_2` bounds -- not (9.1)--(9.6) or (9.8).

**M26, 2026-08-09 (Claude Opus 5): `DK-9.5-9.7` IS NOW OFF THIS BLOCKER TOO.**  (9.7) is derived for the genuine operator by `beamTanTwoTheta_le` / `beamTanTwoTheta_lt_printed` and the 2-norm sentence of (9.6) by `beamTanThetaSum_le`, so no statement on that row is relative to `TheoremOutputCertificate`.  The warning at the head of this blocker was respected: no certificate record was constructed, and the evidence is the operator-level construction `beamComparison` / `beamRitzOffDiagonal` and the norm, form and gap theorems about it.  What is missing on `DK-9.5-9.7` is the 2-norm sentence of (9.7), which is a genuine ABSENCE (the ideal-gauge unbounded residual tan(2 Theta) theorem is unproved, see `DK-6-appendix`) rather than a conditional statement, so it is recorded as a scope gap and not here.  The blocker now constrains exactly `DK-9.9-9.11`.
- **Next action:** Nothing is outstanding for the printed statement.  Optional polish, in order of value: (a) sort `beamLowEigenvalue` so the pairing can be stated for the literal indices `0, 1` instead of an arbitrary ordered pair; (b) restate the envelope in terms of the paper's `omega_k` notation in a Section 9 source-facing wrapper; (c) the general `Real.arccos` facts `arccos_ratio_lt_pi_div_four` and `half_tan_two_arccos_ratio` are reusable and could move to `ForTauCeti` when a trigonometry cluster is next assembled.  Do not build a resolvent and do not manufacture a certificate record.

### Section 10

#### Question 10.1: Sine bounds under arbitrary pairwise spectral distance

- **Kind:** `open_question`
- **Status:** `resolved_by_modern_development`
- **Verification:** `proved_in_build`
- **Mathematics:** Ask for the best UI-norm sine-angle estimate when the two relevant spectra are only known to be at distance delta.
- **Current Lean references:** `TauCeti.DavisKahan1970.Theorem6_2`
- **Assessment:** The paper resolves the square norm; the repository has the sharp pairwise Hilbert–Schmidt theorem. The all-UI-norm version remains a distinct question.

**NORM CLASSES RECORDED 2026-08-07 (Opus 5), closing this row's standing next_action.**

* RESOLVED, under the weak hypothesis Question 10.1 actually asks about (the two spectra
  only known to be at pairwise distance `delta`, with no interval/exterior separation):
  the **Hilbert--Schmidt / Frobenius** class.  `DavisKahan/Sources/DavisKahan1970/SineTheta/Theorem62.lean`
  states Theorem 6.2 with exactly that weaker pairwise spectral-distance hypothesis and
  concludes `frameLowerBound * paperHilbertSchmidtNorm (canonicalSinTheta) <= ...`, over
  `paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct`; the real-scalar form is
  `PaperRealTheorem62Data.result_across`.
* RESOLVED, but under the *stronger* interval/exterior hypothesis, hence not an answer to
  this question: **every** unitarily invariant norm, with constant one -- that is Theorem 6.1
  and its ideal-gauge forms (rows DK-6.1-thm and S2-*).
* OPEN, and this is precisely Question 10.1: any unitarily invariant norm other than the
  Hilbert--Schmidt one under the pairwise-distance hypothesis alone.  The paper poses it and
  the repository does not answer it; the Hilbert--Schmidt proof is a Sylvester/Frobenius
  argument that does not transfer to a general gauge.

This row stays `resolved_by_modern_development`: one norm class is answered, the general
question is not, and it is the paper's own open question rather than proof debt.

**M18 ADJUDICATION 2026-08-09 (Claude Opus 5), against `dev/davis-kahan-1970-final-audit-2026-08-09.md`.**  Disagreement 27 is UPHELD as a CLASSIFICATION point,
and it is worth stating precisely because the status word is `resolved_by_modern_development`.
Theorem 6.2 and inequality (5.1) are IN THE PAPER, so they cannot themselves resolve the paper's own
open question -- Davis and Kahan knew them when they posed Question 10.1, which asks for the best
unitarily-invariant-norm estimate under pairwise spectral distance alone.  What is genuinely modern
here is the SCOPE at which the repository proves the Hilbert--Schmidt answer: over self-adjoint CLOSED
(hence possibly unbounded) operators on arbitrary complete inner product spaces, over real as well as
complex scalars, with Hilbert--Schmidt membership concluded rather than assumed -- see the new row
`DK-5-hermitian-inequalities`, which now claims (5.1) itself.  The status therefore stands, on that
reading and not on the reading the notes above invite.  Either way this row is NOT proof debt: the
general-UI-norm question is the paper's own open question.
- **Next action:** Nothing outstanding: the resolved class (Hilbert--Schmidt under pairwise spectral distance) and the open class (all other unitarily invariant norms under the same hypothesis) are now recorded in the notes with their declarations.  This is the paper's own open question, not proof debt.

#### Question 10.2: Three-way subspace decompositions

- **Kind:** `open_question`
- **Status:** `not_a_completion_obligation`
- **Verification:** `not_applicable`
- **Mathematics:** Seek perturbation estimates for two decompositions into three reducing subspaces using off-diagonal coordinate blocks.
- **Current Lean references:** none identified
- **Assessment:** This is explicitly an open research direction, not a theorem required to formalize the 1970 paper.
- **Next action:** Preserve as a documented research question; do not count as proof debt.

#### Question 10.3: Joint eigenvalue–eigenvector bounds

- **Kind:** `open_question`
- **Status:** `not_a_completion_obligation`
- **Verification:** `not_applicable`
- **Mathematics:** Seek optimal estimates coupling changes in eigenvalues and eigenvectors.
- **Current Lean references:** none identified
- **Assessment:** Open research question.
- **Next action:** Document only.

#### Question 10.4: Perturbation bounds for functional calculus

- **Kind:** `open_question`
- **Status:** `not_a_completion_obligation`
- **Verification:** `not_applicable`
- **Mathematics:** Seek bounds on f(A+H)-f(A) for broader functions, with spectral projections as the motivating discontinuous case.
- **Current Lean references:** none identified
- **Assessment:** Open research question; modern operator-Lipschitz theory is outside the paper-completion target.
- **Next action:** Document connections but do not treat as missing proof.

## Completion interpretation

The completed Section 6 sine-theta surface is not the same as completion of
the whole paper, but the remaining distance is smaller than a raw count of
outstanding rows suggests, and it is not uniform.

A zero `sorry` count is not evidence of completion here. Because the tree is
both sorry-free and axiom-free, unfinished work cannot show up as a `sorry`;
it shows up in exactly three places, which the `verification` axis separates:
a package that does not compile (`not_compiling`), a conclusion stated
relative to a hypothesis record nobody constructs (`proved_conditional`), and
a statement nobody wrote (`absent`). Rows marked `proved_outside_build` and
`partially_in_build` are a fourth, much cheaper case: the mathematics is
already proved and merely sits outside the default build target.

The genuinely hard remainder is Section 8, which is blocked on an
operator-valued contour-integration API that exists nowhere, the Section 9
analytic model, and the Section 3 classification results. The Section 10
questions are part of the source record but are not proof obligations for a
faithful formalization of what the paper proves.
