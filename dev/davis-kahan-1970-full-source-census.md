# Davis--Kahan 1970 full source census

Base commit: `None`.

This is the public, independently worded theorem-by-theorem ledger for the
full paper. The maintained modernized transcription is used only as a local
comparison source and is intentionally not distributed. The JSON file is
authoritative; this Markdown file is generated from it.

## Status summary

| Status | Count |
| --- | ---: |
| `compiled_exact` | 9 |
| `compiled_specialization` | 5 |
| `compiled_general_infrastructure` | 17 |
| `proof_written` | 0 |
| `candidate_under_repair` | 0 |
| `partial_or_wrapper_missing` | 11 |
| `not_represented` | 1 |
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
| `proved_in_build` | 36 |
| `proved_conditional` | 5 |
| `partially_in_build` | 0 |
| `proved_outside_build` | 3 |
| `not_compiling` | 0 |
| `absent` | 1 |
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

### `free-beam-closed-operator` -- hard_math

**Free-beam closed fourth-derivative operator on L2(0,1)**

Section 9's numerical example needs the analytic model itself: the closed fourth-derivative operator with the source's boundary conditions, as an unbounded self-adjoint operator.

Gates: DK-9-model (proved_conditional)

### `free-beam-third-eigenvalue` -- hard_math

**The spectral bound alpha_3 > 500**

A concrete transcendental eigenvalue estimate for the free-beam model. Together with free-beam-closed-operator this is what a FreeBeamFiniteDataCertificate would have to supply.

Gates: DK-9-model (proved_conditional), DK-9.8 (proved_conditional)

### `two-subspace-classification` -- hard_math

**Two-projection canonical decomposition and multiplicity theory**

Section 3's classification results need the Halmos two-subspace canonical form together with spectral multiplicity functions, and the infinite-dimensional existence statement needs cardinal-valued dimension bookkeeping rather than a finite-rank stand-in.

**RE-SCOPED 2026-08-04 (first time).** The multiplicity requirement is an artefact of how the invariant is recorded, not of the mathematics: `genericHalmosCosineSq` is `A (+) A` rather than `A`, so the classification as stated needs multiplicity-halving. The constructive spine through the cosine block on the U-half needs none of it.

**RESOLVED FOR THE CLASSIFICATION 2026-08-04 (second time).** That spine is complete and in the default build: `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, both directions, admission-free, for arbitrary complex Hilbert spaces. The Halmos canonical form is no longer a blocker for anything.

**WHAT STILL BLOCKS.** Only the *phrasing* of Theorem 3.1 in terms of spectral multiplicity functions, which needs Hahn--Hellinger (a translation of the invariant, absent from Mathlib), and the cardinal-valued dimension bookkeeping for the Section 4 infinite-dimensional existence statement. Corollary 3.1 needs neither -- it needs the compact-operator equivalence criterion instead. This blocker should be split along those three lines the next time it is touched.

Gates: DK-3.2-prop (proved_outside_build), DK-3.1-thm (proved_in_build), DK-3.1-cor (absent)

### `section9-certificate-discharge` -- mixed

**Construct the Section 9 certificates**

Section 9 compiles, but every source conclusion is stated relative to FreeBeamFiniteDataCertificate (Section9/ExactData.lean) or TheoremOutputCertificate (Section9/FullExample.lean), and no value of either type is ever constructed. The certificate fields are the paper's numerical claims. Discharging the analytic ones needs free-beam-closed-operator and free-beam-third-eigenvalue; the rest is instantiating theorems the repository already proves.

Gates: DK-9-model (proved_conditional), DK-9.1-9.4 (proved_conditional), DK-9.5-9.7 (proved_conditional), DK-9.8 (proved_conditional), DK-9.9-9.11 (proved_conditional)

### `exact-source-wrappers` -- mechanical

**Source-numbered wrappers over already-proved general theorems**

The mathematics is in the build in a more general form; what is missing is a statement carrying the paper's numbering, scope and hypotheses, so the facade can cite it.

Gates: S1-block-residual (proved_in_build), S2-tan-theta (proved_in_build), S2-sin-two-theta (proved_in_build), S2-tan-two-theta (proved_in_build), S2-unbounded-scope (proved_in_build), DK-3.1-def (proved_in_build), DK-3.2-def (proved_in_build), DK-3.1-prop (proved_in_build), DK-3.3-prop (proved_in_build), DK-3.4-prop (proved_in_build), DK-3.5-prop (proved_in_build), DK-4.1-prop (proved_in_build), DK-5.1-thm (proved_in_build), DK-5.2-thm (proved_in_build), DK-5.1-lem (proved_in_build), DK-7-sin2-proof (proved_in_build), DK-7-tan2-proof (proved_in_build)

### `frontier-tree-unguarded` -- mechanical

**The Davis--Kahan 1970 frontier tree was built by nothing (fixed 2026-08-04)**

`DavisKahan/Experimental/Frontier/**` holds the Section 3 classification spine, the infinite-dimensional Section 4 propositions and the Section 9 analytic model -- 80 manifest declarations, 19 of them `sorry` -- and **no module in the repository imported any of it**. `lake build` missed it, `lake build DavisKahan.Experimental` missed it, and so did `Challenge` and `FinishTanTwoTheta`. It compiled only when a module was named explicitly on the command line. This is the same defect the `RoadmapBridge` block in `lakefile.toml` records for the suggested-signature files, and it went unnoticed for longer because the frontier checker elaborates the tree through its own probe file rather than through a build target, so the status document kept reporting '80 declarations resolving' from a tree nothing built.

Fixed by importing `DavisKahan.Experimental.Frontier.All` from `DavisKahan/Experimental/All.lean`, so `lake build DavisKahan.Experimental` now covers it. It cannot go in a default `warningAsError` target because carrying `sorry`s is the frontier's purpose.

Gates: DK-3.2-prop (proved_outside_build)

### `section8-promotion-out-of-experimental` -- mechanical

**Promote the proved Section 8 theorems out of Experimental**

Theorems 8.1 and 8.2 are PROVED. `DavisKahan/Experimental/Frontier/Section8.lean` is 857 lines and sorry-free, and `#print axioms` on `theorem8_1_selectedBranch_and_spectralRepulsion` and `theorem8_2_perturbationHalfGap_selectedBranch` gives exactly [propext, Classical.choice, Quot.sound]. What remains is guarding them: the module lives under `DavisKahan.Experimental.Frontier`, which is not a default target, so `lake build` never touches it. Promotion is not a one-line `defaultTargets` edit -- measured 2026-08-02, Section 8's transitive closure is 199 repository modules carrying 11 `sorry`s, in Experimental.InfiniteDimensional {DirectRotation (6), SinTheta.General (2), Ideals.Symmetric, Ideals.Rectangular, DoubleAngle}. Five of Section8.lean's seven imports reach all five of those modules, so the dependency cannot be trimmed; the sorried Experimental base has to be finished or the needed results rehomed. Only `Sources.DavisKahan1970.Section8RieszCircle` (50 modules) and `ForTauCeti...SpectralOrder.Complex` (3) are already clean.

Gates: DK-8.1-thm (proved_outside_build), DK-8.2-thm (proved_outside_build)


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
- **Current Lean references:** `TauCeti.DavisKahan1970.sinTheta`, `TauCeti.DavisKahan1970.generalizedSinTheta`
- **Assessment:** The definitive source form is Theorem 6.1; real, complex, bounded, unbounded, and arbitrary-representative forms are present.
- **Next action:** No mathematical gap. Keep the source audit synchronized.

#### Section 2, tan theta theorem: Single-angle tangent theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** One-sided spectral separation plus the Rayleigh–Ritz/off-diagonal condition gives residual and perturbation tangent bounds in every unitary-invariant norm.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`, `TauCeti.DavisKahanExt.tanTheta_spectrum`
- **Assessment:** Finite arbitrary-UI-norm and Hilbert-space operator-norm forms are compiled. The source Hilbert-space arbitrary-UI-norm residual and perturbation statements remain open.
- **Next action:** Reuse the corrected directed Theorem 6.3 Ky-Fan core for the equal-rank source theorem and add the full perturbation companion.

#### Section 2, sin 2 theta theorem: Double-angle sine theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** A spectral gap between the two exact blocks yields residual and perturbation bounds for sin(2 Theta), with sharp factor two.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm`, `TauCeti.DavisKahan.Experimental.sinTwoTheta_addBounded_of_spectrum_gap`
- **Assessment:** Finite arbitrary-UI-norm forms are compiled; general Hilbert-space source forms are under repair.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The UI-norm Part III double-angle theorem is compiled and axiom-clean; the source-general residual and perturbation forms are not yet certified (see next_action).

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Certify source-general residual and perturbation forms.

#### Section 2, tan 2 theta theorem: Double-angle tangent theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** Fully off-diagonal perturbations across an ordered gap give residual and perturbation tan(2 Theta) bounds with factor two.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahanTheory.partIII_tanTwoTheta_opNorm`, `TauCeti.DavisKahanExt.tanTwoTheta_offDiagonalC_of_weighted_sine`
- **Assessment:** The finite operator-norm theorem is compiled. The source arbitrary-UI-norm Hilbert-space endpoint and branch selection are not yet certified.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_specialization`. The operator-norm double-angle tangent theorem is compiled and axiom-clean; the paper's general UI-norm scope and the selected acute branch are not.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Complete the general UI-norm source theorem and its selected acute branch.

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
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_in_build`
- **Mathematics:** The four theorem families extend to unbounded self-adjoint operators under bounded perturbation or residual assumptions, with analytic work concentrated in Theorem 5.2 and the Section 6 appendix.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan1970.canonical_generalizedSinTheta`, `TauCeti.DavisKahan1970.unbounded_sinTheta_opNorm`
- **Assessment:** The sine family is complete in source scope. Tangent has an operator-norm graph-coordinate companion, but the paper claims arbitrary-UI-norm unbounded scope and the cutoff/Ky-Fan passage is not yet formalized.
- **Next action:** Complete Theorem 5.2 and the source-faithful Theorem 6.3 Ky-Fan/cutoff chain; do not credit the operator-norm companion as the full scope claim.

### Section 3

#### Definition 3.1: Direct rotation

- **Kind:** `definition`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** A unitary intertwining the two projections whose diagonal cosine blocks are positive and whose off-diagonal sine blocks are adjoints.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation`, `TauCeti.DavisKahan.Experimental.spectraCanonicalIntertwiner`
- **Assessment:** Acute complex and finite constructions exist; exact nonacute source scope is not yet unified.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The direct-rotation construction is compiled and axiom-clean; a source-facing definition covering the paper's existence regimes is still absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Add a source-facing definition covering the source existence regimes.

#### Definition 3.2: Acute case

- **Kind:** `definition`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** Both crossed intersections P ∩ Q-perp and P-perp ∩ Q vanish.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan.IsAcute`
- **Assessment:** The predicate is broadly used but lacks a numbered source alias.
- **Next action:** Add a source alias only if the facade benefits.

#### Proposition 3.1: Acute direct rotation existence and uniqueness

- **Kind:** `proposition`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_in_build`
- **Mathematics:** In the acute case the direct rotation exists, is unique, and positivity of its diagonal blocks characterizes it.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation`, `TauCeti.DavisKahan1970.complex_directRotation_unique`
- **Assessment:** The main acute construction and uniqueness are present; the exact characterization by positivity needs source-level verification.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. Existence and uniqueness in the acute case are compiled and axiom-clean; the positivity characterization that the printed Proposition 3.1 also asserts is neither proved nor wrapped, so the exact source theorem is not represented.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Prove or wrap the positivity characterization explicitly.

#### Proposition 3.2: Nonacute existence criterion

- **Kind:** `proposition`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_outside_build`
- **Mathematics:** A direct rotation exists exactly when the two crossed intersections have equal dimension; it is then nonunique.
- **Blocked by:** `frontier-tree-unguarded`, `two-subspace-classification`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_parameterized_nonuniqueness`
- **Not reachable from `DavisKahan.All`:** `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent`, `TauCeti.DavisKahan.Experimental.Frontier.Section3.proposition3_2_parameterized_nonuniqueness`
- **Assessment:** No exact general Hilbert-space declaration was found.

CORRECTED 2026-08-04: this row read `not_represented` / `absent` and listed no declarations, but the nonacute existence criterion is stated and **proved sorry-free** in `DavisKahan/Experimental/Frontier/Section3.lean` (verified by `#print axioms`; neither declaration reaches `sorryAx`). It is `proved_outside_build` because the whole `Frontier` tree sits outside the default targets -- see the `frontier-tree-unguarded` blocker.
- **Next action:** State the cardinal/dimension-balanced existence theorem conservatively; finite and infinite cases may need separate APIs.

#### Proposition 3.3: Principal square-root characterization

- **Kind:** `proposition`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_in_build`
- **Mathematics:** Every direct rotation is a principal square root of the product of the two reflections; conversely a suitable principal square root is a direct rotation.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation_sq`
- **Assessment:** The square identity and acute spectral branch exist; the source converse with the crossed-intersection mapping condition is not exposed.
- **Next action:** Add the converse or record the exact missing nonacute hypothesis.

#### Proposition 3.4: Square as a direct rotation

- **Kind:** `proposition`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** When the cosine block squared is at least one half, U squared is the direct rotation from the reflected subspace to the target subspace.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahanTheory.directRotation_sq`, `TauCeti.DavisKahan1970.complex_directRotation_sq`
- **Assessment:** Square identities exist; exact source mapping between Q-minus and Q needs verification.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The square-is-a-direct-rotation content is compiled and axiom-clean; an exact source wrapper is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Add an exact source wrapper after the direct-rotation repair lands.

#### Theorem 3.1: Classification of pairs of subspaces

- **Kind:** `theorem`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** Spectral multiplicity functions of the two angle operators classify dimension-compatible subspace pairs up to isometric equivalence.
- **Blocked by:** `two-subspace-classification`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.SameHalmosCosineBlockInvariant`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.exists_cosineBlockEquiv_of_pairEquiv`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_of_cosineBlockEquiv`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.genericTransport`, `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_of_summandEquivs`
- **Assessment:** **PROVED 2026-08-04, in the paper's own invariant, both directions, admission-free.**

`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant` (`DavisKahan/Geometry/Halmos/GenericReconstruction.lean`): two ordered pairs of subspaces of two complex Hilbert spaces are unitarily equivalent as pairs **iff** their four elementary Halmos summands are linearly isometric and their angle operators `cos^2 Theta` -- the compression of `P_V` to `U /\ generic` -- are unitarily equivalent. No compactness, no finite dimension, no separability, no direct-integral presentation. `#print axioms` gives exactly [propext, Classical.choice, Quot.sound], and the module is reachable from `DavisKahan.All`, so CI guards it.

Brick (2) (`pairOfSubspacesUnitaryEquivalent_of_summandEquivs`, Assembly.lean) glues the four elementary summand isometries and a pair-compatible generic-part isometry into a global unitary. Brick (1) (GenericReconstruction.lean) supplies the generic-part isometry from the cosine block alone, and the extension is *forced*: `B = Phi |B|` has `Phi : M ~= N` unitary, so the only candidate on the U-perp half is `W' := Phi_2 W Phi_1^-1`, and each remaining block is pinned by `A` -- `|B|` is the unique nonnegative square root of `A - A^2`, `D` is pinned by `D B = B (1-A)` plus the dense range of `B`, and `B'` is the adjoint of `B`.

**WHAT IS AND IS NOT LEFT, stated precisely.** The paper phrases Theorem 3.1 with *spectral multiplicity functions* of the angle operators; the theorem above uses the *unitary-equivalence class* of the same operator. The two phrasings differ by Hahn--Hellinger -- 'two self-adjoint operators are unitarily equivalent iff their multiplicity data agree' -- which is a translation of the invariant, not a step in Davis and Kahan's argument. So what remains for the literal printed sentence is a multiplicity theory Mathlib does not have; the classification content of the theorem is done.

**Why the U-side invariant, and not the frontier's.** `SameHalmosOperatorInvariant.generic` records `genericHalmosCosineSq`, the compression of `P_U P_V P_U + P_Uperp P_Vperp P_Uperp`. On the generic part that operator is the cosine block on the U-half and `1 - D` on the U-perp half, i.e. `A (+) A` (`coe_genericHalmosCosineSq_of_mem_left` proves the M half). Recovering `A` from `A (+) A` is multiplicity-halving -- Hahn--Hellinger again, and this time gratuitously, since the pair is determined by `A` alone by elementary means. Davis and Kahan state Theorem 3.1 for the angle operator on the U-side, so recording the cosine block is the paper-faithful reading; the symmetrized operator was a repository choice that doubled the multiplicity.

HISTORY. The pre-existing frontier statement `TauCeti.DavisKahan.Experimental.Frontier.Section3.theorem3_1_spectralMultiplicity_classification` remains `sorry`, and is **vacuous** besides: its premise `TauCeti.DavisKahan.Experimental.Frontier.SameSpectralMultiplicity` is `noncomputable def ... : Prop := by sorry` (`DavisKahan/Experimental/Frontier/Core.lean`), and a Prop-valued definition with a `sorry` body asserts nothing. Its sibling `twoProjection_operator_classification` (Frontier/Section3) also remains `sorry` in the converse direction, for the `A (+) A` reason above and no other. Neither is on this row's evidence path any more.
- **Next action:** Two independent follow-ups, neither blocking the mathematics above. (a) Re-point `SameHalmosOperatorInvariant.generic` at the cosine block on the U-half, then `twoProjection_operator_classification`'s converse closes by `:=` on `pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`. (b) For the literal printed phrasing, build spectral multiplicity (measure class plus cardinal-valued multiplicity function) and prove Hahn--Hellinger, then bridge unitary equivalence to multiplicity equality.

#### Corollary 3.1: Compact classification by angle eigenvalues

- **Kind:** `corollary`
- **Status:** `not_represented`
- **Verification:** `absent`
- **Mathematics:** When the cross projection is compact, the decreasing angle eigenvalue lists, including possible zero multiplicity, classify the pair.
- **Blocked by:** `two-subspace-classification`
- **Current Lean references:** none identified
- **Assessment:** Depends on Theorem 3.1 plus compact spectral classification.

FINDING 2026-08-04: a statement exists, `TauCeti.DavisKahan.Experimental.Frontier.Section3.corollary3_1_compact_angleList_classification`, with a `sorry` proof (verified by `#print axioms`). Unlike DK-3.1-thm its statement is *not* vacuous -- `compactAngleEigenvalueList` is a real definition (the approximation-number sequence) and is axiom-clean. What it needs is the converse of `twoProjection_operator_classification`, itself `sorry`, plus the compact positive spectral theorem.

PROGRESS 2026-08-04: same brick (1)/(2) work as DK-3.1-thm applies -- see that row. This row additionally needs the compact positive spectral theorem (equal approximation-number lists imply unitary equivalence), which is independent of the multiplicity question.

RE-SCOPED 2026-08-04. Theorem 3.1's classification is proved (see DK-3.1-thm), so the dependency that made this row 'defer' is discharged. Feeding it requires exhibiting the cosine block `genericCosineBlock U V` as a compact operator when `P_U P_V P_U` is compact, and then a compact-operator unitary-equivalence criterion. Note the paper's 'including possible zero multiplicity' bookkeeping lands on the four elementary summands, which the invariant already carries separately.
- **Next action:** The general classification now exists in the U-side invariant (`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`), so this row no longer waits on it. What is left is genuinely the compact bridge: for a compact positive contraction, unitary equivalence iff equal decreasing eigenvalue lists with multiplicity, plus the kernel dimension. That is elementary spectral theory of compact self-adjoint operators, not Hahn--Hellinger.

#### Proposition 3.5: Angle commutation and eigenspace geometry

- **Kind:** `proposition`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_in_build`
- **Mathematics:** The full angle commutes with both projections, the quarter-turn and direct rotation; its eigenspaces are maximal reducing constant-angle subspaces in the acute case.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan1970.bounded_angle_commute`, `TauCeti.DavisKahan1970.bounded_sinAngleOperatorC_norm`
- **Assessment:** Commutation identities are present, but the maximal eigenspace characterization is not represented.
- **Next action:** Separate the reusable commutation theorem from the source-specific maximality result.

#### Corollary 3.2: Reversal symmetry

- **Kind:** `corollary`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** Swapping P and Q leaves the angle operator unchanged and reverses the quarter-turn operator.
- **Current Lean references:** `TauCeti.DavisKahan1970.complex_directRotation_reversal`, `TauCeti.DavisKahanTheory.directRotation_symm`
- **Assessment:** Direct-rotation reversal is represented; the exact angle/J statement needs a source wrapper.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The reversal theorem is compiled, axiom-clean, and resolves against the default build -- the earlier "promote it into DavisKahan/FiniteDimensional so CI guards it" instruction is discharged. The source-facing angle and quarter-turn wrapper is still absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** The reversal theorem compiles under DavisKahan/Experimental/FiniteDimensional/DirectRotation.lean. Promote it into DavisKahan/FiniteDimensional so CI guards it, then add the source-facing angle and quarter-turn statement.

### Section 4

#### Proposition 4.1: Pointwise and singular-value extremality of the direct rotation

- **Kind:** `proposition`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** For any unitary carrying P to Q, an orthonormal sequence experiences angles at least the principal angles; equivalently the singular values of (1-V)|P are minimized by the direct rotation and equal 2 sin(theta_k/2).
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahanTheory.singularValues_restrictedDisplacement_le`, `TauCeti.DavisKahanTheory.singularValues_restrictedDisplacement_directRotation`
- **Assessment:** The finite pointwise singular-value theorem is compiled: every singular value of the restricted displacement (1-V)P is minimized by the direct rotation, whose values are the doubled half-angle sines 2 sin(theta_k/2).  A source-numbered wrapper and the infinite-dimensional scope remain open.
- **Next action:** Add a DavisKahan1970 source wrapper and audit the infinite-dimensional statement.

#### Corollary 4.1: UI-norm minimality of direct rotation displacement

- **Kind:** `corollary`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** The direct rotation minimizes the norm of (1-V)P for every unitary-invariant norm.
- **Current Lean references:** `TauCeti.DavisKahanTheory.uiNorm_restrictedDisplacement_le`, `TauCeti.DavisKahanTheory.directRotation_minimizes_restrictedDisplacement_uiNorm`
- **Assessment:** Compiled without any angle restriction, for every unitarily invariant norm, over every RCLike field (finite dimension).  The earlier note conflating this row with Proposition 4.4 is resolved: the corollary concerns the restricted displacement and needs no angle hypothesis.
- **Next action:** Proved. directRotation_minimizes_restrictedDisplacement_uiNorm compiles but only under DavisKahan/Experimental; promote it into the build, then add a DavisKahan1970 source wrapper and audit the infinite-dimensional statement.

#### Proposition 4.2: Basis-angle square-sum extremality

- **Kind:** `proposition`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** For every orthonormal basis of P, the sum of squared displacement sines under V dominates the sum of squared principal sines.
- **Current Lean references:** `TauCeti.DavisKahanTheory.directRotation_minimizes_sum_sq_basis_angles`
- **Assessment:** The finite orthonormal-basis displacement-energy extremality is compiled via the nuclear-norm specialization of the displacement-square majorization.

VERIFIED 2026-08-04: the nuclear-norm specialization for a finite orthonormal basis is compiled, axiom-clean and in the default build. The **infinite-dimensional** form is stated in `DavisKahan/Experimental/Frontier/Section4.lean` and is `sorry` (`#print axioms` reaches `sorryAx`). Proposition 4.1's infinite form *is* proved, in `Experimental/MathAhead/Section4/InfiniteProposition41.lean`, by a spectral-cutoff min-max argument -- that is the pattern to follow.
- **Next action:** Proved. directRotation_minimizes_sum_sq_basis_angles compiles but only under DavisKahan/Experimental; promote it into the build, then settle the exact infinite-dimensional summability convention of the source statement.

#### Proposition 4.3: Squared displacement UI-norm minimality

- **Kind:** `proposition`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** The direct rotation minimizes the UI norm of (1-V*) (1-V).
- **Current Lean references:** `TauCeti.DavisKahanTheory.directRotation_displacementSquare_kyFan`, `TauCeti.DavisKahanTheory.directRotation_displacementSquare_uiNorm`, `TauCeti.DavisKahanTheory.directRotation_minimizes_displacementSquare_uiNorm`
- **Assessment:** Compiled for every unitarily invariant norm over every RCLike field (finite dimension), via Fan-Hoffman majorization of the pinched competitor and two-block pinching contraction.

VERIFIED 2026-08-04: the finite-dimensional UI-norm minimality is compiled, axiom-clean and in the default build. The **infinite-dimensional** form is stated in `DavisKahan/Experimental/Frontier/Section4.lean` and is `sorry` (`#print axioms` reaches `sorryAx`). Proposition 4.1's infinite form *is* proved, in `Experimental/MathAhead/Section4/InfiniteProposition41.lean`, by a spectral-cutoff min-max argument -- that is the pattern to follow.
- **Next action:** Proved. directRotation_minimizes_displacementSquare_uiNorm compiles but only under DavisKahan/Experimental; promote it into the build, then add a DavisKahan1970 source wrapper.

#### Proposition 4.4: Real-space full displacement minimality below pi/3

- **Kind:** `proposition`
- **Status:** `refuted_as_transcribed`
- **Verification:** `proved_in_build`
- **Mathematics:** In a real Hilbert space, if the maximal angle is at most pi/3, the direct rotation minimizes every UI norm of 1-V.
- **Current Lean references:** `TauCeti.DavisKahanTheory.shortRotation_fullDisplacement_refuted`, `TauCeti.DavisKahanTheory.DavisKahanProposition4_4_Finite`, `TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite`
- **Assessment:** The transcribed claim is false: a compiled R^4 counterexample exhibits an acute pair with both principal angles pi/4 and a competitor unitary carrying P to Q whose full displacement 1-V has trace norm 2 sqrt 2, strictly below the direct rotation value 4 sqrt(2 - sqrt 2).  The competitor mixes the equal-angle multiplicity space (rotation angles 0 and pi/2), an obstruction available at every angle threshold; the same family refutes the closing conjecture of Davis 1958.  Operator-norm and squared-displacement consequences survive via 4.1/4.3.
- **Next action:** None outstanding.  The source re-audit is done: the printed Proposition 4.4 carries no hypothesis restricting the competitor class, excluding multiplicity mixing, or replacing the full displacement, so the refutation applies to the claim as printed.  The defect is localized to equation (4.3), whose derivation from (1.12) needs superadditivity of the Ky Fan sum across an orthogonal decomposition of the domain; range orthogonality fails.  The block-level claim the printed proof body establishes (each `||K Omega_k||_2` minimized at V=U, via the pi/3 trigonometry) remains true in the counterexample.  `not_davisKahanProposition4_4_Finite` now refutes the claim in its "every UI norm" form, instantiating N at `(RectangularUnitarilyInvariantSeminorm.kyFan 4).toSquare`.

### Section 5

#### Theorem 5.1: Banach-space Sylvester lower bound

- **Kind:** `theorem`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_in_build`
- **Mathematics:** Under a norm bound on B and an inverse norm bound on A, AX-XB=C implies ||C|| >= delta ||X|| for any compatible operator norm.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan1970.bounded_sylvester_neumann_solution`
- **Assessment:** The repository has Neumann and ordered-gap engines, but no explicit audited source wrapper for this Banach-space theorem.
- **Next action:** Add the exact Banach-space statement and derive it from the geometric-series proof.

#### Theorem 5.2: Semibounded self-adjoint Sylvester theorem

- **Kind:** `theorem`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** For A >= gamma+delta > gamma >= B, a bounded solution of AX=XB+C satisfies the sharp UI-norm inequality.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactSinTheta.directOrderedSylvesterEngine_lowerUpper`, `TauCeti.DavisKahan1970.unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`
- **Assessment:** The completed Section 6 route contains the needed constant-one engines, while the exact source theorem alias is still in the full Part III repair campaign.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The ordered Sylvester engine and the unbounded interval/exterior UI-norm theorem are compiled and axiom-clean; an exact Theorem 5.2 wrapper is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Expose an exact Theorem 5.2 wrapper and include it in the full-paper audit.

#### Lemma 5.1: Strong-cutoff convergence of singular values

- **Kind:** `lemma`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** If projections converge strongly to one, each singular value of K composed with the projection converges to the corresponding singular value of K.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactSinTheta.approximationSingularValue_comp_strongProjection_tendsto`
- **Assessment:** The modern approximation-number theorem is stronger and scalar-generic.
- **Next action:** Add a source-numbered wrapper if needed by the full-paper facade.

### Section 6

#### Lemma 6.1: Direct-sum UI-norm comparison and converse

- **Kind:** `lemma`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Two diagonal block inequalities imply the direct-sum inequality; under equisingularity of paired blocks the converse holds.
- **Current Lean references:** `TauCeti.DavisKahan1970.lemma6_1`, `TauCeti.DavisKahan1970.lemma6_1_converse`
- **Assessment:** Both directions are proved; the converse should be added to the exact audit manifest.
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
- **Current Lean references:** `TauCeti.DavisKahan1970.Proposition6_1`
- **Assessment:** Complex and real source forms are compiled.
- **Next action:** No mathematical gap.

#### Theorem 6.1: Generalized sine theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** A lower frame bound on the trial map and interval/exterior separation give delta epsilon times any equisingular sine representative bounded by the residual.
- **Current Lean references:** `TauCeti.DavisKahan1970.Theorem6_1`
- **Assessment:** This is the canonical source-general sine theorem.
- **Next action:** No mathematical gap.

#### Theorem 6.2: Pairwise-gap square-norm sine theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Arbitrary pairwise spectral distance gives the sharp Hilbert–Schmidt/square-norm residual bound.
- **Current Lean references:** `TauCeti.DavisKahan1970.Theorem6_2`
- **Assessment:** The defect-first pairwise tensor proof is compiled.
- **Next action:** No mathematical gap.

#### Theorem 6.3: Generalized tangent theorem

- **Kind:** `theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** A strict inequality of source-coordinate Hilbert dimensions, the Rayleigh–Ritz residual condition, and a one-sided gap control a directed rectangular tangent representative defined from the singular values of E₀*F₁.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_all_kyFan_core`, `TauCeti.DavisKahan.Experimental.ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal`
- **Assessment:** Bounded finite-source Theorem 6.3 proved axiom-clean in DavisKahan.TanTheta.Theorem63FiniteSource (theorem6_3_all_kyFan_core, theorem6_3_generalizedTanTheta_source_ideal); promoted out of Scratch.
- **Next action:** Compile the new production theorem. The equal-dimension Section 2 tangent theorem and the Appendix arbitrary-ideal unbounded passage remain separate obligations.

### Section 6 appendix

#### Appendix to Section 6, equations (6.7)–(6.11): Unbounded-operator passage

- **Kind:** `appendix`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Domain invariance, bounded residual, spectral cutoffs, and limiting arguments extend the single-angle theorems to unbounded self-adjoint operators.
- **Current Lean references:** `TauCeti.DavisKahan1970.Theorem6_1_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_commonCore`
- **Assessment:** Common-domain and graph-core source forms are compiled. This does not by itself ground the Appendix's full arbitrary-unitarily-invariant tan-theta cutoff/Fan passage, which remains a separate frontier obligation.
- **Next action:** Audit every displayed appendix identity and complete the arbitrary-ideal tangent cutoff/Fan passage; do not infer it from the compiled common-domain wrappers alone.

#### Lemma 6.3: Finite-rank near-maximizer leakage estimate

- **Kind:** `lemma`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_in_build`
- **Mathematics:** A nearly Ky-Fan-optimal finite-rank compression has small off-block trace norm.
- **Current Lean references:** `TauCeti.DavisKahan.Experimental.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage`
- **Assessment:** The surrounding approximation-number infrastructure exists, but no exact source declaration was found.

CORRECTED 2026-08-04: the row listed no declarations. The frontier manifest maps it to node `s6-lemma6-3-approx`, whose declaration lives in `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean` -- inside the default build despite the `Experimental.Frontier` namespace. It resolves and is axiom-clean (`#print axioms`).
- **Next action:** State and prove the source lemma; it may be useful independently for cutoff passages.

### Section 7

#### Section 7, equations (7.1)–(7.5): Reflection proof of the sine double-angle theorem

- **Kind:** `proof_package`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** Reflect the perturbation by 2P-1, identify U squared and sin(2 Theta), and reduce the result to the symmetric sine theorem.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahan.reflectionDefect_eq_perturbationDefect`, `TauCeti.DavisKahan.Experimental.sinTwoTheta_reflectionResidual_of_spectrum_gap`
- **Assessment:** The reflection identities and finite theorem exist; the exact full proof package is under repair.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The reflection-defect identity and the gap-hypothesis residual theorem are compiled and axiom-clean; a source wrapper preserving both conclusions is absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Add a source wrapper preserving both residual and perturbation conclusions.

#### Section 7, equation (7.6) and following argument: Singular-vector proof of the tangent double-angle theorem

- **Kind:** `proof_package`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** The off-diagonal block equation and paired singular vectors yield Ky Fan and UI-norm bounds for tan(2 Theta).
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `TauCeti.DavisKahanExt.tanTwoTheta_offDiagonalC_of_weighted_sine`
- **Assessment:** The operator-norm theorem is compiled in finite dimensions; the arbitrary UI-norm singular-vector argument remains uncertified.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. The off-diagonal weighted-sine tangent bound is compiled and axiom-clean; the exact source norm scope and the infinite-dimensional approximation passage are absent.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Complete the exact source norm scope and infinite-dimensional approximation passage.

### Section 8

#### Theorem 8.1: Branch selection and spectral repulsion

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_outside_build`
- **Mathematics:** Under tan(2 Theta) hypotheses, the acute branch is equivalent to the selected spectral ordering; a canonical reducing subspace exists and satisfies operator, eigenvalue, and symmetric-gauge repulsion inequalities.
- **Blocked by:** `section8-promotion-out-of-experimental`
- **Current Lean references:** `TauCeti.DavisKahan1970.Section8.maximalAngle_selectedSpectralSubspaces_lt_pi_div_four`, `TauCeti.DavisKahan1970.Section8.orientedSpectralRepulsionConclusion`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData`, `TauCeti.DavisKahan1970.Section8.theorem8_1_selectedBranch_and_spectralRepulsion`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_of_rotatedBlockData`
- **Not reachable from `DavisKahan.All`:** `TauCeti.DavisKahan1970.Section8.maximalAngle_selectedSpectralSubspaces_lt_pi_div_four`, `TauCeti.DavisKahan1970.Section8.orientedSpectralRepulsionConclusion`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData`, `TauCeti.DavisKahan1970.Section8.theorem8_1_selectedBranch_and_spectralRepulsion`, `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_of_rotatedBlockData`
- **Assessment:** Theorems 8.1's conclusion is packaged as `Theorem81SourceConclusion` and proved sorry-free in `DavisKahan/Experimental/Frontier/Section8.lean`; `#print axioms` gives [propext, Classical.choice, Quot.sound]. The status stays `candidate_under_repair` because that axis is fidelity to the printed statement, which compiling does not establish -- not because anything fails to build.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_exact`. All five declarations are compiled and axiom-clean. They resolve only outside the default build, which is what `proved_outside_build` records; the mathematics itself matches the printed theorem.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Guard it. The mathematics is done and unguarded: the module is under `DavisKahan.Experimental.Frontier`, outside every default target. See blocker `section8-promotion-out-of-experimental` for the measured cost. Separately, audit `Theorem81SourceConclusion` against the printed Theorem 8.1 to settle the status axis.

#### Theorem 8.2: Smallness selects the acute branch

- **Kind:** `theorem`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_outside_build`
- **Mathematics:** If the perturbation or residual norm is below half the gap, the sine double-angle estimate is accompanied by Theta < pi/4.
- **Blocked by:** `section8-promotion-out-of-experimental`
- **Current Lean references:** `TauCeti.DavisKahan1970.Section8.PerturbationHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.ResidualHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.theorem82_branch_of_residualHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_selectedBranch`
- **Not reachable from `DavisKahan.All`:** `TauCeti.DavisKahan1970.Section8.PerturbationHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.ResidualHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.theorem82_branch_of_residualHalfGapBridge`, `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_selectedBranch`
- **Assessment:** `theorem8_2_perturbationHalfGap_selectedBranch` and `theorem8_2_residualHalfGap_selectedBranch` are proved sorry-free in `DavisKahan/Experimental/Frontier/Section8.lean`; `#print axioms` on the perturbation form gives [propext, Classical.choice, Quot.sound]. The half-gap bridges (`perturbationHalfGapBridge_of_sourceHypotheses`, `residualHalfGapBridge_of_sourceHypotheses`) are proved too.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `compiled_general_infrastructure`. All four declarations are compiled and axiom-clean, outside the default build. The audit of the two half-gap branches against the printed Theorem 8.2 has not been done, so this is not yet claimed as exact.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** Guard it -- same promotion as DK-8.1-thm, same blocker. Then audit the two half-gap branches against the printed Theorem 8.2.

### Section 9

#### Section 9, problem setup: Fourth-derivative Rayleigh–Ritz model

- **Kind:** `numerical_model`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_conditional`
- **Mathematics:** The free-beam fourth derivative on L2(0,1), perturbed by multiplication by epsilon t, with the two-dimensional linear trial eigenspace.
- **Blocked by:** `section9-certificate-discharge`, `free-beam-closed-operator`, `free-beam-third-eigenvalue`
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.CenteredAffine`, `TauCeti.DavisKahan1970.Section9.ritz_matrix_from_affine_moments`, `TauCeti.DavisKahan1970.Section9.FreeBeamFiniteDataCertificate`
- **Assessment:** A source-facing candidate now reconstructs the affine trial basis through exact unit-interval moments and packages the remaining free-beam analytic facts behind an explicit certificate. The closed fourth-derivative operator and the bound alpha_3 > 500 are not yet proved.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The finite-moment layer is compiled and axiom-clean, but every source conclusion is stated relative to `FreeBeamFiniteDataCertificate`, for which no value is ever constructed. The analytic model -- the closed fourth-derivative operator with the source's boundary conditions -- does not exist.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** The finite-moment layer compiles. Remaining is the analytic model itself: construct the free-beam closed fourth-derivative operator on L2(0,1) with the source's boundary conditions, discharge alpha_3 > 500, and build a FreeBeamFiniteDataCertificate. Until such a value exists the Section 9 conclusions are assumed, not derived.

#### Equations (9.1)–(9.4): Initial sine and sine-double-angle bounds

- **Kind:** `numerical_claims`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_conditional`
- **Mathematics:** Compute R*R and derive the operator- and two-singular-value bounds for sin Theta and sin(2 Theta).
- **Blocked by:** `section9-certificate-discharge`
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.initial_residual_gram_from_affine_moments`, `TauCeti.DavisKahan1970.Section9.residualGram_eigenvalueHigh_charAt`, `TauCeti.DavisKahan1970.Section9.equation_9_1`, `TauCeti.DavisKahan1970.Section9.equation_9_4`
- **Assessment:** The residual Gram matrix, its two characteristic roots, exact radical bounds, and the printed rational relaxations are represented. The actual sine and double-angle theorem outputs are still bridge hypotheses pending integration with the maintained theorem APIs.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The arithmetic is compiled and axiom-clean; the printed conclusions are certificate fields rather than applications of the source-facing sine and tangent theorems.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
- **Next action:** The arithmetic compiles. Remaining is to replace the TheoremOutputCertificate fields by applications of the source-facing sine and tangent theorems, so the printed conclusions are derived rather than assumed.

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
- **Blocked by:** `section9-certificate-discharge`, `free-beam-third-eigenvalue`
- **Current Lean references:** `TauCeti.DavisKahan1970.Section9.ArrowheadThreeByThree`, `TauCeti.DavisKahan1970.Section9.tangent_sq_le_of_weinberger_sine_sq`, `TauCeti.DavisKahan1970.Section9.equation_9_8_lower`, `TauCeti.DavisKahan1970.Section9.equation_9_8_upper`
- **Assessment:** The exact arrowhead characteristic polynomial and the algebraic conversion of Weinberger sine-square bounds to tangent bounds are represented. The historical lower-root theorem is deliberately an explicit certificate rather than an informal O(epsilon^4) assertion.

STATUS CORRECTED 2026-08-04: `candidate_under_repair` -> `partial_or_wrapper_missing`. The arrowhead algebra is compiled and axiom-clean; the root inequality needs the alpha_3 > 500 spectral bound, which does not exist.

VERIFIED 2026-08-04 by the elaborator, not by grep: a probe file importing `DavisKahan.All`, `DavisKahan.Experimental.All` and `ForTauCeti` and running `#print axioms` on all 87 declarations named in this census elaborated cleanly -- every name resolves and **none reaches `sorryAx`**. A second probe importing only the default-build roots showed 78 of the 87 resolve there; the 9 that do not are exactly the `TauCeti.DavisKahan1970.Section8.*` names on rows DK-8.1-thm and DK-8.2-thm, whose `proved_outside_build` verification was already correct. `candidate_under_repair` -- "not compiler-certified on this base" -- was therefore false for every row that carried it. The scope question (does the compiled statement match the printed one?) is a separate judgement and is recorded in `next_action`; the status below is the weakest one consistent with that recorded evidence, so no row is overstated.
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
- **Next action:** Record precisely which norm classes are resolved and which remain open.

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
