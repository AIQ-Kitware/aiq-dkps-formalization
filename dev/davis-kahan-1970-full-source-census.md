# Davis--Kahan 1970 full source census

Base commit: `ee44c0d7`.

This is the public, independently worded theorem-by-theorem ledger for the
full paper. The maintained modernized transcription is used only as a local
comparison source and is intentionally not distributed. The JSON file is
authoritative; this Markdown file is generated from it.

## Status summary

| Status | Count |
| --- | ---: |
| `compiled_exact` | 28 |
| `compiled_specialization` | 8 |
| `compiled_general_infrastructure` | 4 |
| `proof_written` | 0 |
| `candidate_under_repair` | 0 |
| `partial_or_wrapper_missing` | 3 |
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
| `proved_in_build` | 42 |
| `proved_conditional` | 3 |
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

### `two-subspace-classification` -- hard_math

**Two-projection canonical decomposition and multiplicity theory**

Section 3's classification results need the Halmos two-subspace canonical form together with spectral multiplicity functions, and the infinite-dimensional existence statement needs cardinal-valued dimension bookkeeping rather than a finite-rank stand-in.

**RE-SCOPED 2026-08-04 (first time).** The multiplicity requirement is an artefact of how the invariant is recorded, not of the mathematics: `genericHalmosCosineSq` is `A (+) A` rather than `A`, so the classification as stated needs multiplicity-halving. The constructive spine through the cosine block on the U-half needs none of it.

**RESOLVED FOR THE CLASSIFICATION 2026-08-04 (second time).** That spine is complete and in the default build: `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, both directions, admission-free, for arbitrary complex Hilbert spaces. The Halmos canonical form is no longer a blocker for anything.

**WHAT STILL BLOCKS.** Only the *phrasing* of Theorem 3.1 in terms of spectral multiplicity functions, which needs Hahn--Hellinger (a translation of the invariant, absent from Mathlib), and the cardinal-valued dimension bookkeeping for the Section 4 infinite-dimensional existence statement. Corollary 3.1 needs neither -- it needs the compact-operator equivalence criterion instead. This blocker should be split along those three lines the next time it is touched.

Gates: DK-3.2-prop (proved_in_build), DK-3.1-thm (proved_in_build)

### `real-scalar-infinite-dimensional-scope` -- mixed

**Real Hilbert spaces at infinite dimension**

AUDIT FINDING 2026-08-07 (Claude Opus 5), by dumping the elaborated signature of every declaration on every `compiled_exact` row and classifying it on two axes.

The transcription's standing assumption 1 (prose/distilled_literature/DavisKahan1970_part_III.tex, 'Standing assumptions from the transcription') reads: 'H is a separable Hilbert space, REAL OR COMPLEX, with finite dimensionality only a special case.'  Assumption 4 adds that all four headline theorems are stated as applicable in infinite as well as finite dimensions.  The same section warns explicitly that a Lean theorem with a finite-dimensional assumption 'is not the unqualified paper theorem merely because its formula and constant match the displayed source inequality'.

MEASURED: 17 of the 30 rows then marked `compiled_exact` had NO declaration covering a real Hilbert space of infinite dimension.  The coverage splits into two shapes.  (a) Infinite dimension but `InnerProductSpace ℂ` only -- Section 3's direct-rotation propositions, Theorem 5.2, all of Section 6, and the two headline sine rows.  (b) `RCLike` (so real and complex) but `[FiniteDimensional]` -- Section 4's propositions and corollary.  A row whose declarations are one of each is still not covering real-and-infinite.

This is a SCOPE gap, not a correctness gap: nothing recorded is wrong, and the complex infinite-dimensional statements are the mathematically substantial ones.  But `compiled_exact` is defined as 'an exact source-facing theorem ... is compiled', and complex-only is not exact against a source that says real or complex.

ROUTE: the repository already intends a 'qualified complexification/restriction route' (dev/targeted-mathematical-repair-2026-07-21.md) and carries `DavisKahan/SpectralTheory/Complexification/`.  A real wrapper should go through that rather than by reproving over `RCLike`, since several proofs use the complex continuous functional calculus essentially.  Section 4's finite-dimensional restriction is a separate question and may be defensible -- the source itself notes that singular-value lists may need spectral multiplicity language for noncompact operators -- so check the printed statement before treating it as a gap.

Gates: S2-sin-theta (proved_in_build), S2-sin-two-theta (proved_in_build), DK-3.1-def (proved_in_build), DK-3.1-prop (proved_in_build), DK-3.3-prop (proved_in_build), DK-3.1-cor (proved_in_build), DK-3.5-prop (proved_in_build), DK-3.2-cor (proved_in_build), DK-4.1-prop (proved_in_build), DK-4.1-cor (proved_in_build), DK-4.2-prop (proved_in_build), DK-4.3-prop (proved_in_build), DK-5.2-thm (proved_in_build), DK-6.1-lem (proved_in_build), DK-6.1-prop (proved_in_build), DK-6.1-thm (proved_in_build), DK-6.2-thm (proved_in_build), DK-6-appendix (proved_in_build), DK-6.3-lem (proved_in_build)

### `section9-certificate-discharge` -- mixed

**Construct the Section 9 certificates**

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

Gates: DK-9.5-9.7 (proved_conditional), DK-9.8 (proved_conditional), DK-9.9-9.11 (proved_conditional)

### `exact-source-wrappers` -- mechanical

**Source-numbered wrappers over already-proved general theorems**

The mathematics is in the build in a more general form; what is missing is a statement carrying the paper's numbering, scope and hypotheses, so the facade can cite it.

Gates: S1-block-residual (proved_in_build), DK-3.1-def (proved_in_build), DK-3.2-def (proved_in_build), DK-3.4-prop (proved_in_build), DK-7-sin2-proof (proved_in_build), DK-7-tan2-proof (proved_in_build)


## Source ledger

### Section 1

#### Section 1, equations (1.1)–(1.8): Two reducing decompositions and the residual

- **Kind:** `construction`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** Block decompositions for A and A+H, trial and exact coordinate maps, and R = (A+H)E0 - E0 A0.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperTheorem61Data`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.UnboundedSinThetaData`
- **Assessment:** The exact notation is distributed across the Section 6 source data records rather than exposed as a Section 1 facade.
- **Next action:** Add source-facing construction aliases only if useful for the full-paper facade.

#### Section 1, equations (1.9)–(1.13): Unitary-invariant norms and Fan dominance

- **Kind:** `framework`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** Norms determined by singular values, contraction laws, Ky Fan prefix norms, and dominance by all prefixes.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperUnitaryInvariantNorm`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.PaperUnitaryInvariantNorm.prefixGauge_le_of_all_kyFan_le_hetero`
- **Assessment:** The source norm correspondence is part of the clean Section 6 surface.
- **Next action:** Retain as shared prerequisite; no new mathematics required.

### Section 2

#### Section 2, sin theta theorem: Single-angle sine theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Interval/exterior spectral separation gives delta times the directed sine norm bounded by the residual norm for every source unitary-invariant norm.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.sinTheta`, `TauCeti.DavisKahan1970.generalizedSinTheta`, `TauCeti.DavisKahan1970.sinTheta_real_exactPaper`, `TauCeti.DavisKahan1970.generalizedSinTheta_real_exactPaper`
- **Assessment:** The definitive source form is Theorem 6.1; real, complex, bounded, unbounded, and arbitrary-representative forms are present.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  FALSE POSITIVE, restored to `compiled_exact`.  `sinTheta_real_exactPaper` and `generalizedSinTheta_real_exactPaper` elaborate over `[InnerProductSpace ℝ]` with `[CompleteSpace]` and NO `[FiniteDimensional]`, i.e. a real Hilbert space of arbitrary dimension.  Their `PaperRealIsometricTheoremData` / `PaperRealTheorem61Data` parameters were checked field by field against the conclusion-as-hypothesis failure mode: every field is a printed hypothesis (self-adjointness of the ambient/trial/complement operators, orthogonal exact decomposition, `0 < gap`, lower frame bound, `FormBoundedSylvesterGap`).  `PaperSinThetaRepresentativeAcross` carries only `operator` plus `SameApproximationSingularSequence operator canonical`, which is the paper's own freedom in naming `sin Theta_0`, and `.canonical` inhabits it with the canonical block, so it generalizes the conclusion rather than assuming it.
- **Next action:** No mathematical gap. Keep the source audit synchronized.

#### Section 2, tan theta theorem: Single-angle tangent theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** One-sided spectral separation plus the Rayleigh–Ritz/off-diagonal condition gives residual and perturbation tangent bounds in every unitary-invariant norm.
- **Current Lean references:** `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`, `TauCeti.DavisKahanExt.tanTheta_spectrum`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_of_formBounds_equalRank`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_equalRank_spectral`, `TauCeti.DavisKahan.Experimental.MathAhead.Section2.theorem63Residual_eq_neg_of_invariant`, `TauCeti.DavisKahan.Experimental.MathAhead.Section2.theorem6_3_perturbation_equalRank`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_infiniteTrial_spectral_exists`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_infiniteTrial_of_formBounds_exists`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_all_kyFan_core_infiniteTrial`, `TauCeti.DavisKahan.Experimental.MathAhead.Section2.theorem6_3_perturbation_infiniteTrial`
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
- **Next action:** Nothing outstanding: residual and perturbation halves are proved at source scope for equal-rank pairs at ARBITRARY trial dimension (finite, infinite, noncompact), arbitrary complete complex Hilbert space, arbitrary Fan-dominant unitarily invariant ideal gauge, with the tangent representative constructed rather than assumed.  The unbounded scope is S2-unbounded-scope's, not this row's.

#### Section 2, sin 2 theta theorem: Double-angle sine theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** A spectral gap between the two exact blocks yields residual and perturbation bounds for sin(2 Theta), with sharp factor two.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm`, `TauCeti.DavisKahan.Experimental.sinTwoTheta_addBounded_of_spectrum_gap`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative`, `TauCeti.DavisKahanExt.sinTwoTheta_perturbation`, `TauCeti.DavisKahanExt.sinTwoTheta_generalSeparation`
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
- **Next action:** Real Hilbert space + arbitrary dimension + EVERY source UI norm.  The operator-norm real case is already covered (`sinTwoTheta_perturbation`, `sinTwoTheta_generalSeparation`, both RCLike and dimension-free).

MEASURED 2026-08-07, and it changes the plan: a proposed bridge
  SameApproximationSingularSequence (sinTwoThetaIdealBlock U V) (sinTwoAngleOperatorC U V)
appears to be FALSE as posed, so do not spend time on it before checking.  Weakest-instance check in C^2 with U = span(e1) and V at angle theta: `sinTwoThetaIdealBlock U V = P_U P_{(U-perp).map J_V}` and the cross block `P_{V-perp} P_U P_V` both have rank at most 1, giving the single nonzero singular value `sin 2theta`; but the ambient `sinTwoAngleOperatorC U V = 2 . S . C` carries `sin 2theta` with MULTIPLICITY 2, one from the U side and one from U-perp.  The norm identity `norm_sinTwoThetaIdealBlock` survives because it only sees the top singular value.  VERIFY THIS COUNTEREXAMPLE before acting on it -- it is a reasoned check, not a compiled one.

If it holds, the two objects are the paper's `Theta_0` and `Theta` respectively, which the source keeps distinct: the sin2theta theorem states BOTH `delta ||sin 2Theta_0|| <= 2 ||R||` AND `delta ||sin 2Theta|| <= 2 ||H||`.  `sinTwoThetaIdealBlock` is the DIRECTED `Theta_0` object; `sinTwoAngleOperatorC` is the ambient `Theta` one.  So the bridge is not merely missing, it is pairing the wrong two objects.

CONSEQUENCE FOR THE PLAN: no new bridge is needed for the `Theta_0` half.  Every existing complex UI-norm sin2theta theorem (`sinTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap`, `sinTwoTheta_addBounded_gauge_of_spectrum_gap`, `sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap`, and the source-facing `unbounded_sinTwoTheta_uiNorm_representative`) already concludes about `sinTwoThetaIdealBlock`.  Lifting THOSE to real scalars needs only the machinery that already exists: complexify the configuration, instantiate the complex result at `KyFanDominantIdealFamily.kyFan (C) k hk` for each k, and finish with `PaperUnitaryInvariantNorm.mul_gauge_le_of_all_mul_kyFan_le` (which is RCLike-generic) plus `PaperUnitaryInvariantNorm.gauge_complexify` on the perturbation/residual side.  That is the same shape that closed the scalar axis for tan 2Theta.

The ambient `Theta` half at UI-norm scope is a separate question and should not be assumed to follow.

#### Section 2, tan 2 theta theorem: Double-angle tangent theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** Fully off-diagonal perturbations across an ordered gap give residual and perturbation tan(2 Theta) bounds with factor two.
- **Current Lean references:** `TauCeti.DavisKahanTheory.partIII_tanTwoTheta_opNorm`, `TauCeti.DavisKahanExt.tanTwoTheta_offDiagonalC_of_weighted_sine`, `TauCeti.DavisKahan.sharp_paperUnitaryInvariantNorm`, `TauCeti.DavisKahan.sharp_paperUnitaryInvariantNorm_selectedBranch`, `TauCeti.DavisKahan.paperFaithful_tanTwoTheta_uiNorm_real`, `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm`, `TauCeti.DavisKahanTheory.paired_singularVector_gap_inequality`, `TauCeti.DavisKahanTheory.singularValue_ne_one`, `TauCeti.DavisKahanTheory.absDoubleAngleTangent_scalar`, `TauCeti.DavisKahanTheory.sum_absDoubleAngleTangent_le`, `TauCeti.DavisKahanTheory.absTanTwoTheta0_offDiagonal_le`, `TauCeti.DavisKahanTheory.sum_absDoubleAngleTangent_le_of_finiteDimensional_invariantSubspace`, `TauCeti.DavisKahanTheory.kyFan_absTanTwoTheta_le_of_finiteDimensional_invariantSubspace`, `TauCeti.DavisKahanTheory.absTanTwoTheta_offDiagonal_mem_and_gauge_le_of_finiteDimensional_invariantSubspace`
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
- **Next action:** The branch axis is closed at every source UI norm for real and complex scalars: `tanTwoTheta_branchFree_paperUINorm`.  What remains for `compiled_exact` is ONE axis, `[FiniteDimensional k U]`: the branch-free chain reaches an arbitrary Hilbert space through the finite-carrier compression `M = U + T''U`, which needs a finite-dimensional trial subspace to reach the intrinsic singular-system layer.  The selected-branch endpoints `sharp_paperUnitaryInvariantNorm` and `paperFaithful_tanTwoTheta_uiNorm` remove that restriction via the Riccati/approximation-number route (`sharp_transformed_prefix`, uniform stable pairs), so the honest remaining work is a branch-free analogue of THAT passage: an operator `2 X |I - X*X|^-1` built from the modulus of `I - X*X` rather than from `I - X*X` itself, with invertibility supplied by the quantitative form of `singularValue_ne_one`.  Do NOT try to recover it from the contractive Riccati API and do NOT route it through Theorem 8.1.

#### Section 2, paragraph after four theorems: Best constants and simultaneous equality

- **Kind:** `source_claim`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** All four constants are optimal in two dimensions, and finite direct sums realize equality simultaneously for all unitary-invariant norms.
- **Current Lean references:** `TauCeti.DavisKahanTheory.sinTheta_constant_optimal`, `TauCeti.DavisKahanTheory.sinTwoTheta_constant_optimal`, `TauCeti.DavisKahanTheory.single_double_sine_tangent_ratios_tendsto_one`
- **Assessment:** Sine sharpness and finite multiplicity are compiled; full quartet simultaneous equality remains in the Part III campaign.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_exact`. The three optimality/ratio witnesses are compiled, axiom-clean, and resolve against the default build. The earlier next_action instruction to "promote them into the build" is discharged -- they already resolve there.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Proved. The constant-optimality and ratio-limit witnesses compile under DavisKahan/Experimental/FiniteDimensional/Sharpness.lean; promote them into the build, then audit the equality models against the exact source claim.

#### Section 2, final paragraphs: Unbounded self-adjoint scope

- **Kind:** `scope_claim`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The four theorem families extend to unbounded self-adjoint operators under bounded perturbation or residual assumptions, with analytic work concentrated in Theorem 5.2 and the Section 6 appendix.
- **Current Lean references:** `TauCeti.DavisKahan1970.canonical_generalizedSinTheta`, `TauCeti.DavisKahan1970.unbounded_sinTheta_opNorm`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_ideal_directedTangent`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_unbounded_ideal`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.Theorem63TrialData.all_kyFan_core_of_formBounds`
- **Assessment:** The sine family is complete in source scope. Tangent has an operator-norm graph-coordinate companion, but the paper claims arbitrary-UI-norm unbounded scope and the cutoff/Ky-Fan passage is not yet formalized.

**THE ARBITRARY-UI-NORM UNBOUNDED TANGENT THEOREM IS DONE, 2026-08-06.** The sine family was already complete in source scope; the tangent family had only an operator-norm graph-angle companion, and the census warned not to credit it as the scope claim. `theorem6_3_unbounded_ideal_directedTangent` (DavisKahan/TanTheta/Theorem63Unbounded.lean, default build, axiom-clean) is the scope claim: closed unbounded self-adjoint ambient operator, arbitrary Fan-dominant unitarily invariant ideal gauge, tangent representative constructed rather than assumed.

HOW THE UNBOUNDED CASE REUSES THE BOUNDED CHAIN. `Theorem63TrialData` records what the tangent argument actually consumes -- a bounded action, compression and residual tied by the block identity -- and `all_kyFan_core_of_formBounds` proves the Ky Fan root from the two printed form bounds alone, with no bounded ambient operator in sight. The crossed action is not extra data: it is P_Vperp o action. For an unbounded operator that is A(P_Vperp z), which is DEFINED because spectral projections preserve the domain (selfAdjointSpectralProjection_mem_domain) and commute with the operator there (selfAdjoint_apply_spectralProjection). Those are the only vectors at which the argument ever evaluates the quadratic form.

WHY THE ARGUMENT GOES THROUGH A THRESHOLD c < alpha+delta RATHER THAN APPLYING THE ENERGY BOUND ONCE: the gap is the OPEN interval, so the endpoint alpha+delta is allowed to carry spectrum and P_{Iic (alpha+delta)} y need not vanish. It does vanish on Iic c for every c < alpha+delta, and the constant follows by taking c up to the endpoint.
- **Next action:** Nothing outstanding for the tangent family. The operator-norm graph-angle companion is retained as `theorem6_3_unbounded_graphAngle_opNorm_companion` and must still not be quoted as the scope claim.

### Section 3

#### Definition 3.1: Direct rotation

- **Kind:** `definition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** A unitary intertwining the two projections whose diagonal cosine blocks are positive and whose off-diagonal sine blocks are adjoints.
- **Blocked by:** `exact-source-wrappers`, `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation`, `TauCeti.DavisKahan.Experimental.spectraCanonicalIntertwiner`, `TauCeti.DavisKahan.Experimental.Frontier.IsPaperDirectRotation`
- **Assessment:** Acute complex and finite constructions exist; exact nonacute source scope is not yet unified.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The direct-rotation construction is compiled and axiom-clean; a source-facing definition covering the paper's existence regimes is still absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

ROW WAS STALE; RESOLVED 2026-08-06.  The requested "source-facing definition" already exists and is guarded: `TauCeti.DavisKahan.Experimental.Frontier.IsPaperDirectRotation` (`DavisKahan/Geometry/Halmos/GenericRotationPredicates.lean`, reached from `DavisKahan.All`) is the paper's definition of a direct rotation for an ARBITRARY pair -- unitary, intertwines the projections, nonnegative diagonal compressions, skew-adjoint crossed blocks -- with no acuteness.  The "source existence regimes" the next action asked to cover are theorems on the numbered rows built on this definition: acute existence/uniqueness/characterisation on DK-3.1-prop (`complex_directRotation`, `complex_directRotation_iff_diagonalBlocks`), the nonacute existence criterion on DK-3.2-prop (`(∃ T, IsPaperDirectRotation U V T) ↔ ...`), and the principal-square-root characterisation on DK-3.3-prop, whose forward-of-nonneg-blocks form consumes exactly this predicate.  Axiom-clean [propext, Classical.choice, Quot.sound].
- **Next action:** Nothing outstanding: the definition is compiled in source form and every Section 3 existence regime is a proved theorem on its own row (DK-3.1-prop, DK-3.2-prop, DK-3.3-prop).

#### Definition 3.2: Acute case

- **Kind:** `definition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Both crossed intersections P ∩ Q-perp and P-perp ∩ Q vanish.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan.IsAcute`
- **Assessment:** The predicate is broadly used but lacks a numbered source alias.

RESOLVED 2026-08-06.  `TauCeti.DavisKahan.IsAcute` IS the source definition -- the projection gap is strictly below one -- compiled, guarded by the default build, axiom-clean, and consumed by every acute-case theorem in the tree.  The conditional next action ("add a source alias only if the facade benefits") is decided in the negative: a numbered alias would duplicate a two-token definition that call sites already read literally, and the api-design rubric asks for lemmas over aliases when nothing is gained.
- **Next action:** Nothing outstanding: the predicate is the printed definition, and the decision against a redundant numbered alias is recorded in the notes.

#### Proposition 3.1: Acute direct rotation existence and uniqueness

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** In the acute case the direct rotation exists, is unique, and positivity of its diagonal blocks characterizes it.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation`, `TauCeti.DavisKahan1970.complex_directRotation_unique`, `TauCeti.DavisKahan1970.complex_directRotation_diagonalBlock`, `TauCeti.DavisKahan1970.complex_directRotation_complementaryDiagonalBlock`, `TauCeti.DavisKahan1970.complex_directRotation_reflectionConjugate`, `TauCeti.DavisKahan1970.complex_directRotation_of_diagonalBlocks`, `TauCeti.DavisKahan1970.complex_directRotation_iff_diagonalBlocks`
- **Assessment:** The main acute construction and uniqueness are present; the exact characterization by positivity needs source-level verification.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. Existence and uniqueness in the acute case are compiled and axiom-clean; the positivity characterization that the printed Proposition 3.1 also asserts is neither proved nor wrapped, so the exact source theorem is not represented.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

PARTIALLY DISCHARGED 2026-08-04, and the residue is now exact. The positivity half is no longer unwrapped: both diagonal compressions of the direct rotation are the *positive* Halmos cosine -- `P_U W P_U = |S| P_U` and `P_Uperp W P_Uperp = |S| P_Uperp` -- and both are proved, in the default build, and axiom-clean. Source aliases added.

**What is genuinely still missing is the characterisation direction, and it is not a wrapper.** The printed clause is that positivity of the diagonal blocks *characterises* the direct rotation. The compiled uniqueness theorem `complex_directRotation_unique` assumes `0 <= re <W x, x>` for **all** `x`, i.e. that the whole Hermitian part is nonnegative. That is strictly stronger than nonnegativity of the two diagonal compressions, which constrains the numerical range only on `U` and on `Uperp` separately and says nothing about mixed vectors. So the source characterisation does not follow from what is compiled; it needs the off-diagonal argument that recovers global numerical-range positivity from the two blocks.

**DISCHARGED 2026-08-05. The characterisation direction is proved, and the row is now exact.** `complex_directRotation_iff_diagonalBlocks` states Proposition 3.1's characterisation clause as a biconditional: `W` is the direct rotation **iff** it is a unitary square root of `J_V J_U` that intertwines the two reflections and whose compressions to `U` and to `U-perp` have nonnegative numerical range.  No condition is imposed on mixed vectors, which is exactly what made the previous residue real.

WHAT THE MISSING STEP TURNED OUT TO BE, and it was one line of algebra, not a wrapper.  The printed hypothesis that `W` carries the pair `(U, U-perp)` onto `(V, V-perp)` had been dropped in the earlier reading.  Restoring it closes everything: `W J_U = J_V W` together with `W^2 = J_V J_U` gives two expressions for `J_V`, and cancelling `W` yields `J_U W J_U = W*`.  So the Hermitian part `W + W*` **commutes with `J_U`**, its quadratic form splits over `U (+) U-perp` with no cross term, and two separate sign conditions add up to global numerical-range positivity -- which is what `complex_directRotation_unique` was already waiting for.  Without the intertwining hypothesis the implication is false: on `U = V` the Hermitian unitary `[[0,b],[b*,0]]` squares to `1 = J_V J_U` and has both diagonal blocks zero, hence nonnegative, yet is not the direct rotation `1`.

THE REUSABLE HALF was extracted to `ForTauCeti`: `Submodule.re_inner_apply_self_nonneg_of_reflectionConjugate` (with `inner_diagonalPart_apply_self` and `diagonalPart_eq_self_of_reflectionConjugate`) says that an operator commuting with a reflection has nonnegative numerical range as soon as its two blocks do.  Nothing in it mentions direct rotations.  All new declarations are in the default build and axiom-clean [propext, Classical.choice, Quot.sound].
- **Next action:** Nothing for the mathematics.  Proposition 3.1 is represented in full: existence (`complex_directRotation`), uniqueness (`complex_directRotation_unique`), the computed diagonal blocks, and the characterisation biconditional `complex_directRotation_iff_diagonalBlocks`.

#### Proposition 3.2: Nonacute existence criterion

- **Kind:** `proposition`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** A direct rotation exists exactly when the two crossed intersections have equal dimension; it is then nonunique.
- **Blocked by:** `two-subspace-classification`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_parameterized_nonuniqueness`
- **Assessment:** No exact general Hilbert-space declaration was found.

CORRECTED 2026-08-04: this row read `not_represented` / `absent` and listed no declarations, but the nonacute existence criterion is stated and **proved sorry-free** in `DavisKahan/Experimental/Frontier/Section3.lean` (verified by `#print axioms`; neither declaration reaches `sorryAx`). It is `proved_outside_build` because the whole `Frontier` tree sits outside the default targets -- see the `frontier-tree-unguarded` blocker.

**2026-08-05 (second session): both promotion-blocking admissions are out of this row's closure.** `directRotation_minimal` was orphaned -- nothing outside its own file referenced it, and the complex statement is already proved in production as `spectraDirectRotation_minimal`; `SpectraBridge/DirectRotationAPI.lean` imported that module only for `IsAcute` and now takes it from `BoundedOperator/Compat`. `projectionDifference_ideal_intervalExterior`, `ideal_sinTheta` and `ideal_sinTwoTheta` moved into `Experimental/InfiniteDimensional/SinTheta/IdealIntervalExterior.lean`, leaving `SinTheta/General.lean` and `InfiniteDimensional/DoubleAngle.lean` sorry-free. Measured closures: 175/188/199 modules, 24/41/50 Experimental, 0 tactic sorries each. WHAT STILL BLOCKS THE ROW: `check_library_structure` rule 2 forbids a production module importing `Experimental`, so promotion means RELOCATING those closures out of `Experimental/`. That is a design decision, not a mechanical step -- take it deliberately. Rule 3 now reports 49 violations (was 6) precisely because 34 modules became admission-free; the checker is enumerating what ought to move.

**IN THE BUILD 2026-08-06.**  `DavisKahan/Experimental/Frontier/{Core,Section3,Section4}.lean` became admission-free and were promoted to `DavisKahan/Frontier/`, reached from `DavisKahan.All` via `DavisKahan.Frontier.All`.  Nothing was renamed -- the `TauCeti.DavisKahan.Experimental.Frontier` namespaces are untouched, exactly as in the 84-module promotion earlier the same day, because the namespace has never been tied to the directory here.  The census declaration probe now resolves 145/145 against `DavisKahan.All`, up from 143/145, and these two declarations are the two that changed.  `check_library_structure` rule 3 drops from 16 violations to 13.
- **Next action:** Nothing outstanding: the criterion and the parameterized nonuniqueness are both proved and both guarded by `lake build`.

#### Proposition 3.3: Principal square-root characterization

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Every direct rotation is a principal square root of the product of the two reflections; conversely a suitable principal square root is a direct rotation.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation_sq`, `TauCeti.DavisKahan1970.complex_directRotation_hermitianPart`, `TauCeti.DavisKahan1970.complex_directRotation_principal_of_sq`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_3_principalSquareRoot_forward`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_3_principalSquareRoot_converse`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_3_principalSquareRoot_iff`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_3_principalSquareRoot_forward_of_nonneg_blocks`
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
- **Next action:** None.  Both directions are compiled in full generality, the printed-hypothesis form of the forward direction needs no side conditions, and the census row is exact.

#### Proposition 3.4: Square as a direct rotation

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** When the cosine block squared is at least one half, U squared is the direct rotation from the reflected subspace to the target subspace.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahanTheory.directRotation_sq`, `TauCeti.DavisKahan1970.complex_directRotation_sq`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_4_square_is_reflected_directRotation`
- **Assessment:** Square identities exist; exact source mapping between Q-minus and Q needs verification.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The square-is-a-direct-rotation content is compiled and axiom-clean; an exact source wrapper is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

ROW WAS STALE; RESOLVED 2026-08-06.  The "absent" exact source wrapper exists and is guarded: `proposition3_4_square_is_reflected_directRotation` (`DavisKahan/Frontier/Section3.lean`, reached from `DavisKahan.All`, axiom-clean): the square of the direct rotation is the direct rotation between the reflected pair `(U, reflectedSubspace V U)` -- the direct-rotation repair this row's next action was waiting on landed with the Frontier promotion, and the wrapper landed with it.  The statement is exact in the FAITHFUL MINIMAL CORRECTION recorded in its docstring, which also records why each correction is forced: the half-angle threshold must be on the cosine SQUARE (`re ⟪x, halmosCosineSq x⟫ ≥ ‖x‖²/2`), not on `|S|` as a literal transcription would have it, and acuteness of the reflected pair is a genuinely independent hypothesis (boundary cosine-square `1/2` satisfies the bound while the reflected pair has gap one).  The two justifying counterexamples are prose in the docstring, not compiled Lean terms; that is hypothesis-shape hardening, not Davis--Kahan content, and is recorded below as optional.
- **Next action:** Nothing that is proof debt.  Optional hardening: compile the two prose counterexamples in the docstring of `proposition3_4_square_is_reflected_directRotation` (concrete two-dimensional pairs), formally pinning the corrected hypothesis shape.

#### Theorem 3.1: Classification of pairs of subspaces

- **Kind:** `theorem`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** Spectral multiplicity functions of the two angle operators classify dimension-compatible subspace pairs up to isometric equivalence.
- **Blocked by:** `two-subspace-classification`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.SameHalmosCosineBlockInvariant`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.exists_cosineBlockEquiv_of_pairEquiv`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_of_cosineBlockEquiv`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.genericTransport`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_of_summandEquivs`, `TauCeti.DavisKahan.Experimental.Frontier.SameSpectralMultiplicity`, `TauCeti.DavisKahan.Experimental.Frontier.sameSpectralMultiplicity_iff_unitarilyEquivalent`, `TauCeti.DavisKahan.Experimental.Frontier.unitarilyEquivalent_of_sameSpectralMultiplicity`, `TauCeti.DavisKahan.Experimental.Frontier.sameSpectralMultiplicity_of_unitarilyEquivalent`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.theorem3_1_spectralMultiplicity_classification`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.twoProjection_operator_classification`
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
- **Next action:** Nothing for Theorem 3.1's statement or for uniqueness: the biconditional is proved in the operator phrasing, the paper's multiplicity phrasing, and -- since 2026-08-06 -- the datum is unique (measure class and level sets both determined by the operator, `operatorUnitaryEquiv_iff_measureEquiv_and_level`).  One follow-up, not blocking and beyond the printed sentence: inhabit `SpectralMultiplicityFoundation` from the now-proved uniqueness (canonical Datum as a quotient by `measureClassSetoid`); parked with the promotion bookkeeping.

#### Corollary 3.1: Compact classification by angle eigenvalues

- **Kind:** `corollary`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** When the cross projection is compact, the decreasing angle eigenvalue lists, including possible zero multiplicity, classify the pair.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.SameCompactAngleData`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.isCompactOperator_genericCosineBlock`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.eigenspace_genericCosineBlock_zero`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.finrank_eigenspace_eq_of_intertwiner`, `TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.sameHalmosTrivialDimensions_orthogonal_right_iff`
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
- **Next action:** Nothing outstanding.  Do NOT 'simplify' the hypothesis back to `P Q P`: that was the bug.  Also note the statement is on `genericCosineBlock`, not the symmetrized `genericHalmosCosineSq`.

#### Proposition 3.5: Angle commutation and eigenspace geometry

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The full angle commutes with both projections, the quarter-turn and direct rotation; its eigenspaces are maximal reducing constant-angle subspaces in the acute case.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.bounded_angle_commute`, `TauCeti.DavisKahan1970.bounded_sinAngleOperatorC_norm`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.IsFixedCosineReducingSubspace`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.fixedCosineSubspace`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.fixedCosineSubspace_isFixedCosineReducing`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.fixedCosineSubspace_maximal`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_5_fixedAngle_maximal`
- **Assessment:** Commutation identities are present, but the maximal eigenspace characterization is not represented.

**ROW WAS STALE.  CORRECTED 2026-08-06: the maximal eigenspace characterisation IS represented, and is proved.**  The note above -- "the maximal eigenspace characterization is not represented" -- was written when the Section 3 frontier was unbuilt and was never revisited.  `proposition3_5_fixedAngle_maximal` states both halves: the fixed-cosine eigenspace `ker (cos^2 Theta - c^2)` is itself a fixed-cosine reducing subspace, and every such subspace is contained in it.  `#print axioms` gives exactly [propext, Classical.choice, Quot.sound] on it and on both halves, and since the Frontier promotion the same day it resolves against `DavisKahan.All`, so `lake build` guards it.  The frontier gate had been reporting `s3-prop3-5` as recursively grounded throughout; the census and the manifest disagreed and the manifest was right.

**A TRANSCRIPTION CORRECTION IS CARRIED, AND IT IS LOAD-BEARING.**  The printed predicate constrains only the source vectors `M cap U` and the target vectors `M cap V`.  That is insufficient for the maximality half: a nonzero vector of the exterior `U-perp cap V-perp` -- which acuteness permits -- spans a subspace that reduces both projections and satisfies the printed conditions vacuously, yet carries cosine square `1`, not `c^2`.  So for `c < 1` the printed predicate admits subspaces not contained in the eigenspace and the proposition as transcribed is false.  `IsFixedCosineReducingSubspace` adds the two complement conditions on `M cap U-perp` and `M cap V-perp`, which is what the paper's own phrasing -- *all nonzero vectors make the fixed angle with the opposite subspace* -- actually says, and which excludes the exterior.  The acuteness and `c <= 1` hypotheses are kept for source correspondence; the proof needs only `0 < c`.

The commutation identities this row already listed (`bounded_angle_commute`, `bounded_sinAngleOperatorC_norm`) are the other clause of the printed proposition and remain the reusable half.
- **Next action:** Nothing outstanding.  Both clauses of Proposition 3.5 are proved and guarded: the commutation identities and the maximal fixed-angle reducing subspace characterisation.  Note the predicate carries a recorded correction to the printed one -- do not 'restore' the source form, which is refuted for c < 1 by an exterior vector.

#### Corollary 3.2: Reversal symmetry

- **Kind:** `corollary`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Swapping P and Q leaves the angle operator unchanged and reverses the quarter-turn operator.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation_reversal`, `TauCeti.DavisKahanTheory.directRotation_symm`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_2_reversal`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_2_reversal_source_form`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_2_sinAngleOperator_symm`
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
- **Next action:** Nothing outstanding: both halves of Corollary 3.2 are proved and guarded by `lake build`.

### Section 4

#### Proposition 4.1: Pointwise and singular-value extremality of the direct rotation

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** For any unitary carrying P to Q, an orthonormal sequence experiences angles at least the principal angles; equivalently the singular values of (1-V)|P are minimized by the direct rotation and equal 2 sin(theta_k/2).
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahanTheory.singularValues_restrictedDisplacement_le`, `TauCeti.DavisKahanTheory.singularValues_restrictedDisplacement_directRotation`, `TauCeti.DavisKahan1970.Proposition4_1`, `TauCeti.DavisKahan1970.Proposition4_1_directRotationValues`, `TauCeti.DavisKahan1970.Proposition4_1_infiniteDimensional`
- **Assessment:** The finite pointwise singular-value theorem is compiled: every singular value of the restricted displacement (1-V)P is minimized by the direct rotation, whose values are the doubled half-angle sines 2 sin(theta_k/2).  A source-numbered wrapper and the infinite-dimensional scope remain open.

**SOURCE WRAPPER ADDED 2026-08-05**, in `DavisKahan/Sources/DavisKahan1970/Section4.lean` (namespace `TauCeti.DavisKahan1970`), so the facade can cite the paper's numbering directly.  The wrappers are `alias`es over the already-compiled general theorems, so they carry the exact statements.  The infinite-dimensional form is proved in `Experimental/MathAhead/Section4/InfiniteProposition41.lean` by a spectral-cutoff min--max argument; it is NOT aliased here, because no production module may import `Experimental` and `lake build` does not yet guard that chain.

**SECTION 4 SCOPE RE-AUDITED 2026-08-07 (Claude Opus 5).**  `DavisKahan/Sources/DavisKahan1970/Section4.lean` used to assert in its module docstring that the finite-dimensional forms "is the scope Section 4 is written at".  The transcription says otherwise: Section 4 opens "We shall make the hypotheses of Theorem 3.1 and Corollary 3.1 (leaving to the reader the modifications entailed in the absence of compactness)" and then states its propositions over infinite orthonormal sequences and infinite sums.  The docstring is corrected and the finite-dimensional aliases are now labelled as specializations.  The infinite-dimensional form was already proved and build-guarded at `DavisKahan/MathAhead/Section4/InfiniteProposition41.lean`; it is now aliased into the source facade as `Proposition4_1_infiniteDimensional`.  Elaborated signature: arbitrary complex Hilbert space, `IsAcute U V`, any unitary `W` with `W * projection U = projection V * W`, concluding that every `approximationNumber` of `sourceRestrictedDisplacement U (spectraDirectRotation U V)` is at most that of `sourceRestrictedDisplacement U W`.  No `[FiniteDimensional]` and no compactness of `P Q-tilde P`, so it is strictly more general than the hypotheses Section 4 inherits from Corollary 3.1.
- **Next action:** Source wrapper done.  What remains is beyond-source hardening: promote `Experimental/MathAhead/Section4/InfiniteProposition41.lean` into the default build so the infinite-dimensional form is guarded.  MEASURED 2026-08-05: its import closure is 24 Experimental modules, of which exactly two carry a real tactic `sorry` -- `InfiniteDimensional/DirectRotation.lean:1203` and `InfiniteDimensional/SinTheta/General.lean:1128`.  Discharge those two or split the dependency; the other three modules that grep as `sorry` mention it only in prose.

#### Corollary 4.1: UI-norm minimality of direct rotation displacement

- **Kind:** `corollary`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The direct rotation minimizes the norm of (1-V)P for every unitary-invariant norm.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahanTheory.uiNorm_restrictedDisplacement_le`, `TauCeti.DavisKahanTheory.directRotation_minimizes_restrictedDisplacement_uiNorm`, `TauCeti.DavisKahan1970.Corollary4_1`, `TauCeti.DavisKahan1970.Corollary4_1_minimizer`
- **Assessment:** Compiled without any angle restriction, for every unitarily invariant norm, over every RCLike field (finite dimension).  The earlier note conflating this row with Proposition 4.4 is resolved: the corollary concerns the restricted displacement and needs no angle hypothesis.

**SOURCE WRAPPER ADDED 2026-08-05**, in `DavisKahan/Sources/DavisKahan1970/Section4.lean` (namespace `TauCeti.DavisKahan1970`), so the facade can cite the paper's numbering directly.  The wrappers are `alias`es over the already-compiled general theorems, so they carry the exact statements.

**SECTION 4 SCOPE RE-AUDITED 2026-08-07 (Claude Opus 5).**  `DavisKahan/Sources/DavisKahan1970/Section4.lean` used to assert in its module docstring that the finite-dimensional forms "is the scope Section 4 is written at".  The transcription says otherwise: Section 4 opens "We shall make the hypotheses of Theorem 3.1 and Corollary 3.1 (leaving to the reader the modifications entailed in the absence of compactness)" and then states its propositions over infinite orthonormal sequences and infinite sums.  The docstring is corrected and the finite-dimensional aliases are now labelled as specializations.  Only the finite-dimensional `Corollary4_1` is aliased; the infinite-dimensional wrapper is a short derivation from `Proposition4_1_infiniteDimensional` and is recorded in `scope_gap` rather than claimed.
- **Next action:** Nothing outstanding at source scope.  CORRECTION 2026-08-05: the previous next_action said `directRotation_minimizes_restrictedDisplacement_uiNorm` 'compiles but only under DavisKahan/Experimental'.  That is stale -- it is in `DavisKahan/FiniteDimensional/DirectRotation.lean`, production, and the census checker verifies this row as proved_in_build.  The source wrapper is now present too.  Beyond-source: the infinite-dimensional ideal-gauge companion (`corollary4_1_restrictedDisplacement_idealGauge`) still lives under Experimental.

#### Proposition 4.2: Basis-angle square-sum extremality

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** For every orthonormal basis of P, the sum of squared displacement sines under V dominates the sum of squared principal sines.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahanTheory.directRotation_minimizes_sum_sq_basis_angles`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.sum_displacementAngleSineSq_ge`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.displacementAngleSineSq_directRotation_eq_of_smul`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.norm_absoluteValue_apply_eq_norm_projection`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.norm_inner_competitor_le`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.sum_displacementAngleSineSq_ge_of_mem`, `TauCeti.DavisKahan.Experimental.MathAhead.Section4.tsum_displacementAngleSineSq_ge_of_mem`
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
- **Next action:** Nothing outstanding.  Proposition 4.2 is proved at arbitrary Hilbert-space generality in three forms -- orthonormal basis, arbitrary finite subfamily, and arbitrary index type with `ENNReal` sums -- with the equality case on a principal vector showing the bound is attained by the direct rotation.  Do NOT restate the right-hand side as `sum_i cost D b_i`: that form is false (notes).

#### Proposition 4.3: Squared displacement UI-norm minimality

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The direct rotation minimizes the UI norm of (1-V*) (1-V).
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahanTheory.directRotation_displacementSquare_kyFan`, `TauCeti.DavisKahanTheory.directRotation_displacementSquare_uiNorm`, `TauCeti.DavisKahanTheory.directRotation_minimizes_displacementSquare_uiNorm`, `TauCeti.DavisKahan1970.Proposition4_3`, `TauCeti.DavisKahan1970.Proposition4_3_kyFan`, `TauCeti.DavisKahan1970.Proposition4_3_minimizer`, `TauCeti.DavisKahan1970.Proposition4_3_infiniteDimensional`
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
- **Next action:** Source wrapper done, and the infinite-dimensional Ky Fan form is proved.  What remains is beyond-source hardening: promote `Experimental/MathAhead/Section4/InfiniteProposition43.lean` (and `InfiniteProposition41.lean`, which it consumes) into the default build.  MEASURED 2026-08-05: the closure is 25 Experimental modules with exactly two real tactic `sorry`s, at `InfiniteDimensional/DirectRotation.lean:1203` and `InfiniteDimensional/SinTheta/General.lean:1128`.  Do NOT attempt pointwise approximation-number domination: it is false (notes), and it would contradict this repository's own refutation of Proposition 4.4.

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
- **Current Lean references:** `TauCeti.DavisKahan1970.bounded_sylvester_neumann_solution`, `TauCeti.DavisKahan1970.banach_sylvester_lower_bound`, `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_uiNorm`
- **Assessment:** The repository has Neumann and ordered-gap engines, but no explicit audited source wrapper for this Banach-space theorem.

CLOSED 2026-08-04: `partial_or_wrapper_missing` -> `compiled_exact`. The previous next_action -- "Add the exact Banach-space statement and derive it from the geometric-series proof" -- had the derivation backwards, and that is why the row stayed open. **The geometric series is what produces a solution; it is not what bounds one.** From `A X = C + X B` and a bounded left inverse, `X = A^{-1} C + A^{-1} X B`, so `||X|| <= ||A^{-1}||(||C|| + rho ||X||) <= (rho+delta)^{-1}(||C|| + rho ||X||)`, and one multiplication by `rho + delta` cancels `rho ||X||` from both sides. That is the whole proof.

So the source statement needs **no inner product, no completeness, no self-adjointness and no Neumann series** -- which is exactly why every other Sylvester lower bound in this repository, all of them proved through coercivity or the spectral theorem, was the wrong thing to try to specialise. New foundation: `ForTauCeti/Analysis/Normed/Operator/SylvesterBoundedInverse.lean`, over Banach spaces and a `NontriviallyNormedField`.

The source's "for any compatible operator norm" clause is carried literally by `banach_sylvester_lower_bound_uiNorm`: it is stated for an arbitrary size function subject to exactly subadditivity and the two one-sided ideal bounds, which is also what a symmetric-norm-ideal gauge supplies, so the unitarily-invariant-norm reading of Theorem 5.1 is the same theorem. `banach_sylvester_lower_bound` is its operator-norm specialisation. Both are admission-free and resolve against `DavisKahan.All`.
- **Next action:** None. If a future consumer wants the bound with `BoundedInverseData` rather than a bare left inverse, `hA.left_inv` is the argument to pass; do not restate the estimate.

#### Theorem 5.2: Semibounded self-adjoint Sylvester theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** For A >= gamma+delta > gamma >= B, a bounded solution of AX=XB+C satisfies the sharp UI-norm inequality.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactSinTheta.directOrderedSylvesterEngine_lowerUpper`, `TauCeti.DavisKahan1970.unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`, `TauCeti.DavisKahan1970.Theorem5_2`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.davisKahan1970_sylvester_real`, `TauCeti.DavisKahan.Experimental.ExactSinTheta.real_unbounded_sylvester_kyFan`
- **Assessment:** The completed Section 6 route contains the needed constant-one engines, while the exact source theorem alias is still in the full Part III repair campaign.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The ordered Sylvester engine and the unbounded interval/exterior UI-norm theorem are compiled and axiom-clean; an exact Theorem 5.2 wrapper is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

**SOURCE WRAPPER ADDED 2026-08-05**: `Theorem5_2`, in `DavisKahan/Sources/DavisKahan1970/Section5.lean`, aliasing `directOrderedSylvesterEngine_lowerUpper`.  That engine is the printed theorem: `SemiboundedBelow A (c + delta)` and `SemiboundedAbove B c` are the source's ordering `A >= gamma + delta > gamma >= B`, `HasClosedSylvesterEquation A B X R` is `AX = XB + C`, and the conclusion `delta * N(X) <= N(R)` carries the sharp constant.  It is more general than the print on the ideal axis (arbitrary `KyFanDominantIdealFamily`, not a fixed UI norm) and admits unbounded closed self-adjoint operators.

THE ORDERED BRANCH IS NOT THE INTERVAL/EXTERIOR BRANCH.  `unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`, also on this row, carries a different separation hypothesis; the wrapper's docstring says so, and the two must not be substituted for one another.

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  FALSE POSITIVE, `scope_gap` removed.  `davisKahan1970_sylvester_real` (`DavisKahan/Sylvester/RealUnbounded.lean:77`) elaborates as an arbitrary real Hilbert-space, arbitrary `KyFanDominantIdealFamily ℝ`, UNBOUNDED (`ClosedOperator`) form of the full Theorem 5.2: self-adjoint `A`, `B`, `0 < delta`, `FormBoundedSylvesterGap A B delta`, `HasClosedSylvesterEquation A B X C`, `N.Mem C`, concluding `N.Mem X` and `delta * N.gauge X <= N.gauge C`.  No new proof was needed -- only the census entry.  `real_unbounded_sylvester_kyFan` is the per-Ky-Fan-level companion.
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
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** Two diagonal block inequalities imply the direct-sum inequality; under equisingularity of paired blocks the converse holds.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.lemma6_1`, `TauCeti.DavisKahan1970.lemma6_1_converse`
- **Assessment:** Both directions are proved; the converse should be added to the exact audit manifest.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.
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
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** Two complementary source gap hypotheses give the full sine-angle inequality with perturbation H.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.Proposition6_1`
- **Assessment:** Complex and real source forms are compiled.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.
- **Next action:** No mathematical gap.

#### Theorem 6.1: Generalized sine theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** A lower frame bound on the trial map and interval/exterior separation give delta epsilon times any equisingular sine representative bounded by the residual.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.Theorem6_1`, `TauCeti.DavisKahan1970.Theorem6_1_real`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`
- **Assessment:** This is the canonical source-general sine theorem.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  FALSE POSITIVE, restored to `compiled_exact`.  Theorem 6.1 has a real infinite-dimensional source theorem already: `Theorem6_1_real` elaborates over `[InnerProductSpace ℝ]`, `[CompleteSpace]`, no `[FiniteDimensional]`, and the common-domain and common-core unbounded variants `Theorem6_1_real_commonDomain` / `Theorem6_1_real_commonCore` do too.  The row's declaration list simply omitted them; the mathematics was never missing.
- **Next action:** No mathematical gap.

#### Theorem 6.2: Pairwise-gap square-norm sine theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Arbitrary pairwise spectral distance gives the sharp Hilbert–Schmidt/square-norm residual bound.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.Theorem6_2`, `TauCeti.DavisKahan1970.Theorem6_2_real`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore`
- **Assessment:** The defect-first pairwise tensor proof is compiled.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  FALSE POSITIVE, restored to `compiled_exact`.  Theorem 6.2 has a real infinite-dimensional source theorem already: `Theorem6_2_real` elaborates over `[InnerProductSpace ℝ]`, `[CompleteSpace]`, no `[FiniteDimensional]`, and the common-domain and common-core unbounded variants `Theorem6_2_real_commonDomain` / `Theorem6_2_real_commonCore` do too.  The row's declaration list simply omitted them; the mathematics was never missing.
- **Next action:** No mathematical gap.

#### Theorem 6.3: Generalized tangent theorem

- **Kind:** `theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** A strict inequality of source-coordinate Hilbert dimensions, the Rayleigh–Ritz residual condition, and a one-sided gap control a directed rectangular tangent representative defined from the singular values of E₀*F₁.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_all_kyFan_core`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem63DirectedTangent`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_all_kyFan_core_directedTangent`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal_directedTangent`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_of_formBounds_equalRank`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_equalRank_spectral`
- **Assessment:** Bounded finite-source Theorem 6.3 proved axiom-clean in DavisKahan.TanTheta.Theorem63FiniteSource (theorem6_3_all_kyFan_core, theorem6_3_generalizedTanTheta_source_ideal); promoted out of Scratch.

**A HYPOTHESIS WITH NO PRODUCER, FOUND AND DISCHARGED 2026-08-05.** Every compiled form of Theorem 6.3 quantified over a `tanTheta0` satisfying `HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0`, and a grep for *producers* rather than consumers showed that nothing anywhere in the repository ever constructed one.  The compiled theorem was therefore a conditional whose antecedent had no witness -- strictly weaker than the printed theorem, which takes the tangent representative for granted.  The row said `proved_in_build`, which was true of the declarations and misleading about the mathematics.

THE WITNESS.  `ExactTanTheta.theorem63DirectedTangent`: diagonal in the right singular basis of the directed sine block, with entries `tan (arcsin s_i)`.  `hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent` proves it has the required approximation numbers.  Two facts do the work: the singular values of a diagonal operator with antitone nonnegative diagonal are the diagonal itself, and `t |-> t / sqrt(1 - t^2)` is increasing on `[0,1)`, so the entries inherit the sine block's ordering.  Post-composition with the inclusion `Z -> H` does not move approximation singular values (`approximationSingularValue_subtypeL_comp`), and above `dim Z` both sides vanish (`approximationSingularValue_eq_zero_of_finrank_le`).

**NO NEW HYPOTHESIS WAS NEEDED.** Finiteness of the entries requires `s_i < 1`, and `theorem63_singularValues_sine_lt_one` -- already in the file -- derives exactly that from the source gap, i.e. from the same `hCompressionUpper` and `hUnwantedLower` Theorem 6.3 assumes.  So `theorem6_3_all_kyFan_core_directedTangent` and `theorem6_3_generalizedTanTheta_source_ideal_directedTangent` carry precisely the printed hypotheses.  Both are in the default build and axiom-clean, and are wrapped in `RemainingSourceSurface` as `theorem6_3_all_kyFan_core_unconditional` and `theorem6_3_generalizedTanTheta_source_ideal_unconditional`.

**THE DIMENSION HYPOTHESIS WAS REDUNDANT, 2026-08-05.** `theorem6_3_generalizedTanTheta_of_formBounds` binds `_hStrictDimension : Module.rank Z < Module.rank V` and never uses it, and the Ky Fan core never took it at all.  The printed inequality does one job -- under the paper's separability convention it forces the trial coordinate space to be finite-dimensional -- and here that is an explicit instance.  `theorem6_3_generalizedTanTheta_of_formBounds_equalRank` and `theorem6_3_generalizedTanTheta_equalRank_spectral` state the theorem without it, which is what the equal-rank Section 2 tangent theorem needs; see S2-tan-theta.
- **Next action:** Both obligations previously recorded here are discharged: the tangent representative exists, and the equal-dimension form is proved (the dimension comparison was redundant, not an obstacle).  What remains is the Appendix arbitrary-ideal **unbounded** passage, which is S2-unbounded-scope's.

### Section 6 appendix

#### Appendix to Section 6, equations (6.7)–(6.11): Unbounded-operator passage

- **Kind:** `appendix`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** Domain invariance, bounded residual, spectral cutoffs, and limiting arguments extend the single-angle theorems to unbounded self-adjoint operators.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan1970.Theorem6_1_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_commonCore`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore`
- **Assessment:** Common-domain and graph-core source forms are compiled. This does not by itself ground the Appendix's full arbitrary-unitarily-invariant tan-theta cutoff/Fan passage, which remains a separate frontier obligation.

**STATUS LOWERED 2026-08-07 (Claude Opus 5): `compiled_exact` -> `compiled_specialization`, on scalar scope, not on any doubt about the mathematics.**  Every declaration on this row is stated for `InnerProductSpace ℂ`.  Standing assumption 1 of the transcription says the space is real OR complex and assumption 4 says the headline theorems apply in infinite as well as finite dimension, so the compiled statement is a specialization of the printed one.  `compiled_specialization` is defined as exactly that: 'a useful compiled specialization exists, but not the full source scope'.  The remedy is a real wrapper through the complexification route, not a reproof; see blocker `real-scalar-infinite-dimensional-scope`.

**AUDIT METHOD CORRECTED 2026-08-07 (Claude Opus 5).**  The scalar-scope audit earlier the same day inspected only the declarations already LISTED on this row, which answers "does this row list a real theorem?" and not "does the repository HAVE one?".  Re-audited by searching the whole stable repo and elaborating candidate signatures.  The sine half of this row was a false positive; the tangent half was not.  Recorded in `scope_gap` rather than by flipping the status, because a row that mixes a covered and an uncovered passage is not honestly described by either label alone.

**SHARED ADAPTER LANDED 2026-08-07 (Claude Opus 5).**  `complexifySubmoduleEquiv (Z : Submodule ℝ E) : RealComplexification ↥Z ≃ₗᵢ[ℂ] ↥(complexifySubmodule Z)` (`DavisKahan/SpectralTheory/Complexification/SubmoduleEquiv.lean`, axiom-clean, in the default build) removes the first load-bearing obstruction to the real lift on this row.  The problem it solves: a real configuration carries an operator on `↥Z`, complexifying lands on `RealComplexification ↥Z`, and every complex theorem here speaks about `↥(complexifySubmodule Z)`.  Canonically the same space, NOT definitionally equal.  `re`/`im` are preserved on the nose, so conjugating a compression or residual through it is mechanical.  It is deliberately an isometric equivalence rather than a definitional identification, because the ideal/norm layer only needs equality of approximation singular values and unitary conjugation gives exactly that.  The unbounded appendix reuses the same adapter for trial subspaces, on top of the existing closed-operator transports in `DavisKahan/SpectralTheory/ClosedOperator/Complexification.lean`.  Do not rewrite the cutoff argument.
- **Next action:** Audit every displayed appendix identity and complete the arbitrary-ideal tangent cutoff/Fan passage; do not infer it from the compiled common-domain wrappers alone.

#### Lemma 6.3: Finite-rank near-maximizer leakage estimate

- **Kind:** `lemma`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** A nearly Ky-Fan-optimal finite-rank compression has small off-block trace norm.
- **Blocked by:** `real-scalar-infinite-dimensional-scope`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage`, `TauCeti.DavisKahan.Experimental.Frontier.Section6Appendix.lemma6_3_singularValue_leakage`
- **Assessment:** The surrounding approximation-number infrastructure exists, but no exact source declaration was found.

CORRECTED 2026-08-04: the row listed no declarations. The frontier manifest maps it to node `s6-lemma6-3-approx`, whose declaration lives in `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean` -- inside the default build despite the `Experimental.Frontier` namespace. It resolves and is axiom-clean (`#print axioms`).

STATUS CORRECTED 2026-08-07 (Fable 5): `partial_or_wrapper_missing` -> `compiled_exact`.  The next_action ('state and prove the source lemma') predates the 2026-08-04 correction that located the declaration; the lemma IS stated and proved, in the default build, axiom-clean, in BOTH the source's forms: `lemma6_3_approximationNumber_leakage` (near-Ky-Fan-optimal prefix square energy forces off-block operator norm below eta, with the source-faithful block hypothesis K P = Q K P -- the module docstring documents why the earlier K P = Q K stating was wrong) and the finite-dimensional singular-value specialization `lemma6_3_singularValue_leakage`.  The compiled statement generalizes the source only by not assuming K compact (the rank hypotheses on the projections carry the finiteness), which is scope-widening, not scope-narrowing.
- **Next action:** Nothing outstanding.  The lemma is reusable for cutoff passages exactly as the audit hoped.

### Section 7

#### Section 7, equations (7.1)–(7.5): Reflection proof of the sine double-angle theorem

- **Kind:** `proof_package`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Reflect the perturbation by 2P-1, identify U squared and sin(2 Theta), and reduce the result to the symmetric sine theorem.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_eq_perturbationDefect`, `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_le_two_mul`, `TauCeti.DavisKahan1970.sinTwoTheta_reflectedOverlap_norm`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative`
- **Assessment:** The reflection identities and finite theorem exist; the exact full proof package is under repair.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The reflection-defect identity and the gap-hypothesis residual theorem are compiled and axiom-clean; a source wrapper preserving both conclusions is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

ROW WAS STALE; CORRECTED 2026-08-07 (Fable 5).  The requested 'source wrapper preserving both residual and perturbation conclusions' has existed since the SinTwoTheta facade landed (DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean, `namespace TauCeti.DavisKahan1970`): the mirror-defect identities of the reflection proof (equations (7.1)-(7.3): `sinTwoTheta_mirrorDefect_eq_perturbationDefect`, `_le_two_mul`, and the gauge form), the double-angle identification (7.4)-(7.5) (`sinTwoTheta_reflectedOverlap_norm`), and BOTH conclusions at source-general scope -- arbitrary complete Hilbert space, unbounded closed self-adjoint operator, arbitrary Ky-Fan-dominant ideal family, representative freedom: `unbounded_sinTwoTheta_uiNorm_representative` (perturbation form, sharp factor two) and `unbounded_sinTwoTheta_residual_uiNorm_representative` (residual form, constant one).  All resolve from `DavisKahan.All` and are axiom-clean (verified by elaborator probe 2026-08-07).
- **Next action:** Nothing outstanding for the reflection proof package.

#### Section 7, equation (7.6) and following argument: Singular-vector proof of the tangent double-angle theorem

- **Kind:** `proof_package`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The off-diagonal block equation and paired singular vectors yield Ky Fan and UI-norm bounds for tan(2 Theta).
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan1970.tanTwoTheta_uiNorm`, `TauCeti.DavisKahan1970.tanTwoTheta_kyFan`, `TauCeti.DavisKahan1970.tanTwoTheta_uiIdeal_infinite`, `TauCeti.DavisKahan1970.tanTwoTheta_kyFan_infinite`, `TauCeti.DavisKahan1970.tanTwoTheta_sharp_opNorm`, `TauCeti.DavisKahan1970.tanTwoTheta_spectral_repulsion`
- **Assessment:** The operator-norm theorem is compiled in finite dimensions; the arbitrary UI-norm singular-vector argument remains uncertified.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The off-diagonal weighted-sine tangent bound is compiled and axiom-clean; the exact source norm scope and the infinite-dimensional approximation passage are absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

ROW WAS STALE; CORRECTED 2026-08-07 (Fable 5).  The requested 'exact source norm scope and infinite-dimensional approximation passage' have existed since the TanTwoTheta facade landed (DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean): `tanTwoTheta_uiNorm` is equation (7.6) at the source norm scope -- every rectangular unitarily invariant norm, proved by the paper's paired-singular-vector argument -- and `tanTwoTheta_uiIdeal_infinite` / `tanTwoTheta_kyFan_infinite` are the infinite-dimensional sharp ideal forms via compression to the finite carrier (the paper's own passage), with `tanTwoTheta_sharp_opNorm` the pole-free sharp subspace theorem carrying the Section 8 acute branch and `tanTwoTheta_spectral_repulsion` the branch-keeping mechanism.  The facade's docstring records the audited boundary: the sharp infinite-dimensional ideal form requires a finite-dimensional invariant subspace (principal angles attained), the unbounded companions cover genuine spectral subspaces at the extended-cosine denominator, and the UNRESTRICTED sharp infinite-dimensional statement is excluded as refuted (the genuine unbounded Sylvester equation has a nonzero commutator defect; `doubleAngleTangent_sylvesterEquation` carries it explicitly).  Excluding an unsupported statement is completing the surface, not a gap.  All declarations resolve from `DavisKahan.All` and are axiom-clean (elaborator probe 2026-08-07).
- **Next action:** Nothing outstanding at the source's own scope.  The facade docstring records the deliberate exclusions (finite-carrier condition for the sharp ideal form; refuted unrestricted statement).

### Section 8

#### Theorem 8.1: Branch selection and spectral repulsion

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Under tan(2 Theta) hypotheses, the closed quarter-angle condition is equivalent to the selected spectral ordering; a canonical reducing subspace exists, is unique, and satisfies the operator, ordered-eigenvalue and every-symmetric-gauge repulsion inequalities on both blocks.
- **Current Lean references:** `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch`, `TauCeti.DavisKahan1970.Section8.theorem8_1_eq_canonicalBranch_of_maximalAngle_le`, `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn`, `TauCeti.DavisKahan1970.Section8.Theorem81Conclusion`, `TauCeti.DavisKahan1970.Section8.canonicalLowBranch`, `TauCeti.DavisKahan.realSpectrum_add_offDiagonal_subset_exterior_of_form_gap`, `TauCeti.DavisKahanExt.re_inner_le_of_mem_boundedSelfAdjointSpectralSubspace_Iic`, `TauCeti.DavisKahanExt.le_re_inner_of_mem_boundedSelfAdjointSpectralSubspace_Iic_orthogonal`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.theorem8_1_upperCompressionRepulsion_canonicalBranch`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.theorem8_1_lowerCompressionRepulsion_canonicalBranch`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSandwichApproximation_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSandwichApproximation_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_angle_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_angle_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperWeightedWeakMajorization_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerWeightedWeakMajorization_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_source`, `TauCeti.singularValues_adjoint_sandwich_weaklyMajorized`, `TauCeti.approximationNumber_adjoint_sandwich_weaklyMajorized`, `TauCeti.DavisKahan1970.Section8.approximationNumber_eq_eigenvalues_of_isPositive`, `TauCeti.DavisKahan1970.Section8.approximationNumber_upperBlockShift_eq_zero_of_le`, `TauCeti.DavisKahan1970.Section8.approximationNumber_lowerBlockShift_eq_zero_of_le`, `TauCeti.DavisKahan1970.Section8.approximationNumber_cosineBlock_eq_principalCosines`, `TauCeti.DavisKahan1970.Section8.approximationNumber_lowerCosineBlock_eq_principalCosines`, `TauCeti.DavisKahan1970.Section8.norm_cosineBlock_eq_principalCosines_zero`, `TauCeti.DavisKahan1970.Section8.norm_lowerCosineBlock_eq_principalCosines_zero`, `TauCeti.DavisKahan1970.Section8.cos_arccos_approximationNumber_cosineBlock`, `TauCeti.DavisKahan1970.Section8.maximalAngle_le_pi_div_six_iff`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_of_rotatedBlockData`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData`
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
- **Next action:** Nothing outstanding.  Theorem 8.1 is complete: the characterization, existence and uniqueness of the branch, parts (i), (ii) and (iii) for BOTH blocks, part (iii) over every symmetric gauge, and a compiled -- not prose -- eigenvalue/angle dictionary with the index reversal proved rather than asserted.  The uniqueness half and the strict quarter-angle bound are stronger than the printed statement; the dimension-free approximation-number forms of (ii) deliver the printed "natural infinite-dimensional extensions".  The `..._of_rotatedBlockData` aliases remain listed as INTERNAL infrastructure: they take an abstract quadratic-data record and are not evidence about the printed theorem.

#### Theorem 8.2: Smallness selects the acute branch

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** If the perturbation norm or the residual norm is below half the gap, and the unperturbed block's spectrum lies in the enlarged central interval, then the sine double-angle estimate is accompanied by Theta < pi/4.
- **Current Lean references:** `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_source`, `TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_source`, `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed`, `TauCeti.DavisKahan1970.Section8.theorem8_2_krein_completion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source`, `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source`, `TauCeti.DavisKahan1970.Section8.subspaceGap_eq_directedGap_of_finrank_eq`, `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_source_maximalAngle_lt`, `TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_source_maximalAngle_lt`, `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_maximalAngle_lt`, `TauCeti.DavisKahan1970.Section8.theorem8_2_source`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.theorem8_2_perturbationHalfGap_source_angle_lt`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.theorem8_2_residualHalfGap_source_angle_lt`, `TauCeti.DavisKahan.Experimental.Frontier.Section8.residual_eq_comp_subtypeL`, `TauCeti.DavisKahan.Experimental.Frontier.Krein.exists_selfAdjoint_completion_eq_norm_restriction`, `TauCeti.DavisKahan1970.Section8.PerturbationHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.ResidualHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.theorem82_branch_of_residualHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_selectedBranch`
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
- **Next action:** Nothing outstanding.  Both printed alternatives are proved from the printed hypotheses with no caller-supplied certificate, the residual alternative through the printed Krein reduction with the exact (1.8) residual, and the printed `Theta < pi/4` is compiled under the Section 1 standing convention (1.5) in its finite form.  The distinction between the dimension-free directed theorem and the printed symmetric conclusion is deliberate and must not be collapsed: see the counterexample in the notes, which satisfies every printed hypothesis of Theorem 8.2 together with the cardinal form of (1.5) and has `||P - Q|| = 1`.  That counterexample is recorded in prose, in the module docstring and here; a machine-checked version would need an explicit two-eigenvalue operator on `E (+) E` and is the only piece of Section 8 that is documented rather than compiled.

### Section 9

#### Section 9, problem setup: Fourth-derivative Rayleigh–Ritz model

- **Kind:** `numerical_model`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The free-beam fourth derivative on L2(0,1), perturbed by multiplication by epsilon t, with the two-dimensional linear trial eigenspace.
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
- **Next action:** Nothing outstanding.  The operator, its kernel, its spectral gap, the orthonormal trial pair, and the identification of the finite moments with genuine L^2 integrals are all compiled and in the default build, and the sorried Section9Analytic skeleton has been deleted.

#### Equations (9.1)–(9.4): Initial sine and sine-double-angle bounds

- **Kind:** `numerical_claims`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Compute R*R and derive the operator- and two-singular-value bounds for sin Theta and sin(2 Theta).
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.initial_residual_gram_from_affine_moments`, `TauCeti.DavisKahan1970.Section9.residualGram_eigenvalueHigh_charAt`, `TauCeti.DavisKahan1970.Section9.equation_9_1`, `TauCeti.DavisKahan1970.Section9.equation_9_4`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamSinTheta_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamSinTwoTheta_lt`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamPerturbation_comp_trialIncl_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamSpecProjection_lowSet_eq_singleton`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamSinTwoThetaSum_lt`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamKyFanTwo_gaugeReal_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamTrialVec_span_eq_top`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.exists_beamTrialVec_repr`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamResidual_gram`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamGram_orthogonal_direction`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamResidualRankOne_rank_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamResidual_sub_rankOne_apply`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamResidual_orthogonal_norm_sq`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.norm_beamResidual_sub_rankOne_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.approximationSingularValue_one_beamResidual_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.kyFanTwo_beamResidual_le`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.beamSinThetaSum_le`
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
- **Next action:** Nothing.  (9.1), (9.2), (9.3) and (9.4) are all derived from `beamOperator` with no certificate field in any statement, and all are in the default build.

#### Equations (9.5)–(9.7): Rayleigh–Ritz tangent refinements

- **Kind:** `numerical_claims`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_conditional`
- **Mathematics:** Use the compressed trial operator and orthogonal residual to obtain sharper tan Theta and tan(2 Theta) bounds.
- **Blocked by:** `section9-certificate-discharge`
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.recentered_residual_gram_from_affine_moments`, `TauCeti.DavisKahan1970.Section9.equation_9_5_low`, `TauCeti.DavisKahan1970.Section9.equation_9_6`, `TauCeti.DavisKahan1970.Section9.equation_9_7`
- **Assessment:** The Ritz compression, rank-one recentered residual, singular-value scalars, exact tangent envelopes, and decimal corollaries are present as a candidate. The unbounded tan-theta and tan-two-theta instantiations remain to be connected.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The exact radical arithmetic is compiled and axiom-clean; the tangent and double-angle theorems are not yet instantiated in place of the certificate fields.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** The exact radical arithmetic compiles. Remaining is to instantiate the strongest correct tangent and double-angle theorems in place of the corresponding certificate fields.

#### Equation (9.8): Comparison with Weinberger bounds

- **Kind:** `comparison_claim`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_conditional`
- **Mathematics:** Derive lower-eigenvalue estimates from a 3x3 comparison matrix and compare individual-vector angle bounds.
- **Blocked by:** `section9-certificate-discharge`
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.ArrowheadThreeByThree`, `TauCeti.DavisKahan1970.Section9.tangent_sq_le_of_weinberger_sine_sq`, `TauCeti.DavisKahan1970.Section9.equation_9_8_lower`, `TauCeti.DavisKahan1970.Section9.equation_9_8_upper`
- **Assessment:** The exact arrowhead characteristic polynomial and the algebraic conversion of Weinberger sine-square bounds to tangent bounds are represented. The historical lower-root theorem is deliberately an explicit certificate rather than an informal O(epsilon^4) assertion.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The arrowhead algebra is compiled and axiom-clean; the root inequality needs the alpha_3 > 500 spectral bound, which does not exist.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.

BLOCKER CLEARED 2026-08-04: `free-beam-third-eigenvalue` is resolved. The paper's `alpha_3 > 500` is now the unconditional theorem `FreeBeam.Classical.five_hundred_lt_pow_four_of_characteristic_eq_zero`, proved from `cos beta * cosh beta < 1` on `(0, 4.73]` with no certificate and no existence hypothesis. What still blocks this row is only `free-beam-closed-operator` -- tying the characteristic roots to the spectrum of an actual self-adjoint operator on `L^2(0,1)`.
- **Next action:** The arrowhead algebra compiles. Remaining is the root inequality, which needs the alpha_3 > 500 spectral bound.

#### Section 9, l2 example after (9.8): Residual-infinite limitation example

- **Kind:** `example`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** An l2 trial vector has a useful Rayleigh quotient but lies outside the perturbed operator domain, so residual-based theorems do not apply while lower-bound methods still do.
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_eq_one`, `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_partial_energy`, `TauCeti.DavisKahan1970.Section9.truncatedDiagonalImage_energy`
- **Assessment:** The pointwise constant image and divergent finite partial energies are formalized algebraically, together with an explicit finite-support truncation repair that agrees on arbitrary prescribed prefixes.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_specialization`. The sequence lemmas are compiled, axiom-clean and unconditional, but stated for coordinate sequences rather than in the abstract operator setting the source example describes.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** The sequence lemmas compile and are unconditional. Optionally lift them from coordinate sequences to the abstract operator setting.

#### Equations (9.9)–(9.11) and final bounds: Individual eigenvector identification inside a cluster

- **Kind:** `numerical_claims`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_conditional`
- **Mathematics:** Reduce the full eigenproblem to a two-dimensional Schur complement, then combine tan(2 Theta) and tan Theta bounds to control each eigenvector angle omega_k.
- **Blocked by:** `section9-certificate-discharge`
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.half_tanTwoPsi_ratio_lt_of_eigenvalue_upper`, `TauCeti.DavisKahan1970.Section9.block_eigenproblem_iff`, `TauCeti.DavisKahan1970.Section9.schur_complement_reduction`, `TauCeti.DavisKahan1970.Section9.individual_angle_le_exact_envelope`, `TauCeti.DavisKahan1970.Section9.final_lower_individual_angle_bound`, `TauCeti.DavisKahan1970.Section9.NumericalExampleCertificate`
- **Assessment:** Equation (9.9) is represented as an explicit block linear map, and equations (9.10)-(9.11) by a generic Schur reduction. The rank-one correction is decomposed into its shifted diagonal and off-diagonal parts, with the exact sqrt(3)/30 coefficient. The final scalar combination producing sqrt(7)/10 and the printed bounds is present. The operator-order resolvent sandwich and actual angle identifications remain certificate fields.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The block reduction and Schur complement are compiled and axiom-clean; the rank-one resolvent order argument that would replace the last certificate fields is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** The block reduction compiles. Remaining is the rank-one resolvent order argument, replacing the last certificate fields.

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
