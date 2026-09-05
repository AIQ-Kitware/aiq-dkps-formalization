# Goal: repair every finding of the 2026-09-04 hostile review and reach an honest 29/29

You are taking over `aiq-dkps-formalization` to close the findings in
`dev/davis-kahan-1970-hostile-review-2026-09-04.md`. Read that report first; this document
tells you what to change, in what order, and what "done" means. It does not repeat the
review's evidence — go to the report for the instance, the type, and the line.

**Finish the whole list.** Do not stop after re-registering evidence. Do not stop after the
census is green. Do not stop after the Lean changes compile if the certificate is still red.
The end state is: every finding below is closed by a compiled theorem, a census edit that a
reviewer can check, or a documented decision — and the documented certificate command passes
with no flags.

Current source beats this document, the review, theorem names, docstrings, and commit
messages. Inspect before you change.

## Read before starting

* `AGENTS.md` (the whole file; the rules below cite it).
* `dev/davis-kahan-1970-hostile-review-2026-09-04.md` — the findings F1--F10 and the Pass B
  table.
* `dev/davis-kahan-1970-result-inventory-contract.md` — how `canonical_evidence`,
  `source_clauses`, `boundary_review`, and the hash fields (`semantic_review_sweep.canonical_evidence_sha256`,
  `source_fidelity_inventory_sha256`, …) are maintained, and what stales the hard gate.
* `dev/davis-kahan-1970-independent-audit-template.md` — the reviewer packet; every
  registration change below must remain explainable from it.
* `DavisKahan/Sources/DavisKahan1970/SectionTwo.lean` and the files named per item.
* `dev/lean-proof-engineering-lessons.md` before touching any proof.

## Ground rules (from `AGENTS.md`; restated because each one bites here)

1. **Edit the census by hand, in the same commit as the Lean change it describes.** Never
   write a script to infer registrations. When a `boundary_review`, `canonical_evidence`, or
   `source_clauses` entry changes, refresh the hash fields the contract names, by the
   mechanism the contract names — do not hand-type a digest.
2. **Do not add a `scripts/check_*.py`.** Every check you need already exists:
   `aiq-lean gates run --config dev/policy/gate-suite.yaml --fast`,
   `python3 scripts/check_davis_kahan_1970_source_census.py`,
   `python3 scripts/certify_davis_kahan_1970.py --require-terminal`,
   `python3 scripts/check_declaration_name_drift.py`, `lake build Challenge`,
   `lean-warning-fix`, `leanq`.
3. **Every rename**: grep the whole repository including `Challenge/` and `comparator/*.json`;
   run `scripts/check_declaration_name_drift.py`; run `lake build Challenge`; update every
   census row that names the declaration; keep a `@[deprecated]` alias only if a standalone
   submission repository under `submodules/` still consumes the old name (check; do not
   assume).
4. **Never claim a declaration is done until Lean has accepted it.** Report status in terms of
   the mathematics, not row counts.
5. **`omit [...] in` goes above the docstring**, applies to one declaration, and is the fix
   for `unusedSectionVars` — never `set_option linter.unusedSectionVars false`.
6. **Do not run `lake` while the gate suite is running.**
7. **Commit as you go** (one logical change per commit), publish the tally
   (`python3 .llm_resource_tally/tool publish`) in its own commit before handing off, and push
   `main`.

## Work items

Effort estimates are for an agent with a warm build. Items marked *census* touch no Lean.

### R1 — DK-6.3-thm: register the printed-shape theorem (*census*, hours)

**Problem.** Canonical evidence `tanTheta_directed_unboundedTrial_symmetricNorming_{complex,real}`
(`Sources/DavisKahan1970/TanThetaDirectedUnbounded.lean:99,142`) assumes
`specProjection hA (Set.Ioo α (α+δ)) = 0` and compares against
`selfAdjointSpectralSubspace A hA (Set.Iic α)`. Printed Theorem 6.3 has neither. Review §F1
gives a 4x4 instance the witnesses miss.

**Repair.**
1. In `dev/davis-kahan-1970-formalization-result-inventory.json`, row `DK-6.3-thm`: make
   `TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_complex` and
   `…_real` (`TanThetaDirectedUnbounded.lean:217,261`) the `primary_source_witness` entries
   for `DK-6.3-thm.generalized-tangent-theorem` at complex and real scope; move the
   `_unboundedTrial_` pair to `supporting_evidence` with role `specialization` and a note
   saying exactly which hypothesis they add. Rewrite both `source_clauses.justification`
   strings so they describe the hypotheses of the new witnesses (unbounded Ritz pair,
   arbitrary `V` with `ReducingComplement A V`, coercivity on `Vᗮ ∩ dom A`, compression
   `≤ α`, arbitrary trial dimension). Keep `semantic_alignment: locally_exact`; it is now
   true.
2. Before registering, **check the witness against the printed statement yourself**: confirm
   from `UnboundedRitzPair` (`DavisKahan/TanTheta/RitzPair.lean`) that
   `D.trial.compression` is the Rayleigh--Ritz compression of `A` (`action_eq`) and that
   `HasTheorem63DirectedTangentApproximationNumbersInfinite Z V` characterizes the
   representative against `P_{Vᗮ}|_Z`, i.e. the singular values of `E₀*F₁`. If either fails,
   stop and fix the theorem, not the row.
3. Rename `tanTheta_directed_unboundedTrial_symmetricNorming_{complex,real}` to
   `tanTheta_directed_unboundedTrial_spectralGap_symmetricNorming_{complex,real}` (the bounded
   sibling already says `spectralGap`), following ground rule 3. Do the same for
   `TanTheta.theorem6_3_unbounded_infiniteTrial_ideal{,_exists}` and
   `theorem6_3_unbounded_infiniteTrial_ideal_exists_real` if they keep the spectral-gap
   hypothesis: their names must say so.
4. Refresh the row's hashes per the contract; run the census check; confirm `29/29` still
   terminal.

**Done when** the row's canonical witnesses have no spectral-gap hypothesis and no
`specProjection` in their types, the justification text matches the types, and no registered
name hides a `spectralGap` hypothesis.

### R2 — Section 8 operator scope: decide and record, or lift (*census* or Lean, ½ day or 1--2 weeks)

**Problem.** `DK-8.1-thm` and `DK-8.2-thm` are formalized for bounded `A H : E →L[𝕜] E` only
(`Sources/DavisKahan1970/Section8/*.lean`), while the fidelity model gives the four Section 2
results unbounded scope and both Section 8 theorems inherit "the hypotheses of the
tan 2θ / sin 2θ theorem". Neither row discloses the restriction.

**Repair — pick one and write it down.**

*Option A (record).* Add to both rows a `boundary_review` cross-block entry and a
`nonlocal_source_interpretation`-style note (the contract's vocabulary for "the printed
statement is read under a scope fixed elsewhere") stating that Section 8 is read at the
bounded main-body scope, with the reason: the paper's Section 8 proofs are written for
bounded operators, and the Section 2 unbounded passage names Theorem 5.2 and the Appendix to
Section 6 as the *only* unbounded machinery. Change `semantic_alignment` on both rows from
`locally_exact` to `paper_faithful_nonlocal_source_interpretation` so the reviewer packet
lists them with S2-tan-theta, DK-4.x and DK-8.2's (3.5) reading. Add a source-scope atom for
"Section 8 main-body bounded scope" to `dev/davis-kahan-1970-source-atom-inventory.json` only
if the contract requires an atom to carry the reading; otherwise reference the existing
`S1-block-residual.setup-hilbert-scope`. Do not silently widen the denominator.

*Option B (lift).* Prove `theorem8_1_maximalAngle_le_iff_spectrumIn`, part (i)
(`theorem8_1_{upper,lower}CompressionRepulsion`), `theorem8_1_canonicalBranch`, and
`theorem8_2_branch_maximalAngle_lt_of_crossedDefects` plus the two retained sin 2θ bounds for
`A : E →ₗ.[𝕜] E` self-adjoint with bounded `H`, using the vocabulary the unbounded Section 2
endpoints already use (`TauCeti.LinearPMap.ReducesSubspace`, `IsOddFor`, form bounds on
`dom A`, `FormBoundedSylvesterGap`, `specRange`). Parts (ii)/(iii) stay as printed
(finite-dimensional / approximation numbers). Keep the bounded theorems as specializations.
Register the new ones as canonical evidence. This is genuine work; the 8.2 homotopy argument
in the tree may be bounded-specific — read `Section8/Theorem82Branch.lean` and
`Section8/Smallness.lean` before committing to B.

**Recommendation:** do A now (it is the honest state of the tree), and open B as a follow-up
row in `GOAL.md` rather than leaving the rows silent. If you do B, remove the A note when the
lifted theorems land.

**Done when** both rows say, in a field the reviewer packet renders, what operator scope
their evidence is at and why — or the evidence is unbounded.

### R3 — Make the tangent endpoints self-certifying against Mathlib's totalisation (Lean, 1--2 days)

**Problem.** `cfc` returns `0` off continuity and `Real.tan (π/2) = 0`; several endpoints
conclude on objects that are junk exactly in the case the paper's proof excludes, and the
exclusion is proved inside the proof but absent from the type. Review §F3.

**Repair.** Add one conjunct to each conclusion; every conjunct is already proved inside the
corresponding proof, so the change is plumbing, not mathematics.

1. Ambient tan θ, (3.5)-form endpoints — add `HasDefinedAmbientTangent U V` (equivalently
   `‖sinAngleOperatorC U V‖ < 1`) to the conclusion of:
   * `tanTheta_ambient_bounded_symmetricNorming_{complex,real}_of_crossedDefects`
     (`TanThetaAmbient.lean`; the fact is `norm_sinAngleOperatorC_lt_one_of_crossedDefectsEquivalent` at line 1224),
   * `tanTheta_ambient_unboundedRitz_symmetricNorming_{complex,real}`
     (`TanThetaUnboundedAmbient.lean:551`, `TanThetaUnboundedAmbientReal.lean:397`),
   * `tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_{complex,real}`
     (`…:436`, `…:351`),
   * `tanTheta_ambient_unboundedOperator_boundedRitz_symmetricNorming_{complex,real}`.
   For the real endpoints use the real definedness predicate (`HasDefinedAmbientTangentReal`)
   the tree already has. Then the `_definedTangent_` endpoints and the (3.5)-form endpoints
   are mutually derivable and the docstring claim "non-vacuous corollary" is a theorem.
2. Ambient tan 2θ — add `∀ t ∈ spectrum ℝ (angleOperatorC P V), Real.cos (2 * t) ≠ 0`
   (this is `cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq`,
   `DavisKahan/DoubleAngle/TangentTransport.lean:569`, applied to the `IsUnit` conjunct the
   `blockRepresentative_derivedReflection` form already concludes) to
   `tanTwoTheta_ambient_unbounded_symmetricNorming_complex`
   (`TanTwoThetaUnboundedAmbientExact.lean:635`) and `…_real`
   (`TanTwoThetaUnboundedExactReal.lean:534`), with the real angle operator in the real
   statement.
3. Directed tan θ — add `‖theorem63DirectedSineBlock Z V‖ < 1` (from
   `approximationSingularValue_sineBlock_lt_one_infiniteData`,
   `DavisKahan/TanTheta/Theorem63UnboundedInfiniteTrial.lean:274`, at `n = 0`, since
   `a₀ = ‖·‖`) to the conclusions of `tanTheta_directed_unboundedRitz_symmetricNorming_*`,
   the renamed `_unboundedTrial_spectralGap_` pair, `theorem6_3_unbounded_infiniteTrial_ideal*`,
   and `tanTheta_directed_bounded_spectralGap_symmetricNorming_*`. If the unbounded-Ritz proof
   route does not currently pass through that lemma, prove the norm bound from the same form
   bounds (the argument is the paper's (6.6) at `n = 0`) rather than weakening the ask.
4. Update every `SectionTwo.*` alias docstring that describes these conclusions, and the
   `HasDefinedAmbientTangent` block comment in `TanThetaUnboundedAmbient.lean` (it currently
   claims the (3.5) endpoints are non-vacuous "corollaries"; after this item they *state* it).
5. Update `Audits/ResultSemanticSurface.lean` only if a `#check` target was renamed; the
   `#check`s themselves need no edit for a changed conclusion. Re-run
   `lake build DavisKahan.Sources.DavisKahan1970.Audits.ResultSemanticSurface` and confirm the
   new conjuncts print.

**Done when** no registered tangent endpoint concludes on `tanAngleOperatorC/R`,
`absTanTwoAngleOperatorC/R`, or a `tan ∘ arcsin`-characterized representative without a
conjunct in the same type that excludes the pole.

### R4 — DK-5.1-lem: register the proofs, not the wrapper (*census* + tiny Lean, hours)

**Problem.** `TauCeti.DavisKahan1970.Lemma5_1` (`Sources/DavisKahan1970/Section5.lean:35`) is
generic over `[HasApproximationNumberStrongCutoff 𝕜]`, a class whose single field is Lemma 5.1
(`DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean:60`).

**Repair.**
1. Add two source-facing declarations in `Section5.lean`, `lemma5_1_complex` and
   `lemma5_1_real`, whose types are Lemma 5.1 at `ℂ` and `ℝ` with **no** class argument,
   proved by the instance fields (`complexHasApproximationNumberStrongCutoff`,
   `realHasApproximationNumberStrongCutoff`, `ScalarGeneric.lean:76,82`) or directly by the
   theorems those instances wrap. Docstrings: Lemma 5.1, scalar scope in the name per the
   naming classification.
2. Register them as canonical evidence (scalar scope `complex`/`real`) on `DK-5.1-lem`. Keep
   `Lemma5_1` only as a `supporting_evidence` facade, renamed `lemma5_1` for casing (see R6),
   with a docstring saying the class is discharged at both fields — or delete it if nothing
   consumes it (`leanq` will tell you).

**Done when** the row's canonical evidence has no capability class in its type.

### R5 — S2-sin-two-theta ambient clause: canonical evidence at the printed `P` (*census* + aliases, hours)

**Problem.** Canonical ambient evidence `sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_{complex,real}`
and the alias `SectionTwo.sinTwoTheta_ambient_*` restrict the paper's arbitrary reducing `P`
to a spectral subspace. `sinTwoTheta_ambient_unbounded_reflectionPair_symmetricNorming_rclike`
(`SinTwoThetaAmbientUnbounded.lean:288`) has the printed shape.

**Repair.**
1. Check, by unfolding, that the rclike theorem's intertwining hypothesis is exactly "`V`
   reduces `A + Eop`" (`reflectionPerturbation V Eop = Eop − X_V Eop X_V`). If it is, add a
   thin wrapper `sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike` that takes
   `TauCeti.LinearPMap.ReducesSubspace (A.addBounded Eop) V` instead of the raw intertwining
   equation (there is a `ReflectionIntertwines.ofReducesSubspace`-style constructor; use the
   same pattern), plus fixed-field `_complex`/`_real` aliases in the same file.
2. Make those the canonical ambient evidence of `S2-sin-two-theta`; demote the `addBounded`
   spectral endpoints to `specialization`. Retarget `SectionTwo.sinTwoTheta_ambient_{complex,real}`
   and the ambient conjunct of `sinTwoTheta_bothConclusions_{complex,real}` at the new
   declarations (the "both conclusions" certificate may then quantify over a reducing `V`
   instead of a measurable `S`).
3. Delete or fix the canonical entry `sinTwoTheta_ambient_bounded_symmetricNorming_complex`
   whose `covers_source_atoms` is empty; a canonical entry covers something or is not
   canonical.

**Done when** the ambient clause's canonical witnesses quantify over an arbitrary reducing
subspace of the unperturbed operator.

### R6 — Naming and placement (Lean renames, 1 day; do after R1--R5 so you rename once)

Follow ground rule 3 for every rename.

1. Move `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean` from
   `namespace DavisKahan1970` to `namespace TauCeti.DavisKahan1970`. Eight registered
   declarations and three predicates that appear in `theorem6_1_complex`'s type change name.
   Update the census rows (`S2-sin-theta`, `DK-6.1-thm`, `DK-6.2-thm`), the `SectionTwo.sinTheta`
   alias (which no longer needs `_root_`), `Audits/ResultSemanticSurface.lean`, and
   `dev/davis-kahan-1970-statement-map.json`.
2. Resolve the six case-twin pairs on DK-6.1-prop, DK-6.1-thm, DK-6.2-thm: the lowercase
   component theorems are canonical (the module comment in `SineThetaSourceInventory.lean`
   says so). Rename the capitalized record-method aliases to `*Data.result_*`-style names or
   delete them; deregister them from the census. No two registered names may differ only in
   case — check with the review's one-liner over `lean_declarations`.
3. Unify source-facing casing to the lowercase `theoremN_M_*` / `propositionN_M_*` /
   `corollaryN_M_*` / `lemmaN_M_*` form the naming classification commits to:
   `Proposition4_1_*`, `Proposition4_2_*`, `Proposition4_3_*`, `Corollary4_1_*`, `Theorem5_2`,
   `Lemma5_1`, `Theorem6_1_*`, `Theorem6_2_*`, `Proposition6_1_*`. Keep deprecated aliases only
   where ground rule 3 says so.
4. Give source-facing homes and `TauCeti.DavisKahan1970` names to the registered witnesses
   that live outside the paper namespace: `TauCeti.DavisKahan.TanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists`
   (`DavisKahan/TanTheta/`), `TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial`
   (`Sources/DavisKahan1970/Section2TanThetaPerturbation.lean`, wrong namespace),
   `TauCeti.DavisKahan.Sylvester.davisKahan1970_sylvester_real` (`DavisKahan/Sylvester/RealUnbounded.lean`),
   `TauCeti.DavisKahan.FiniteDimensional.DavisKahanProposition4_4_Finite` and its two companions.
   The rule: a declaration registered as source evidence is either declared under
   `TauCeti.DavisKahan1970` in `Sources/DavisKahan1970/**`, or is aliased there and the alias
   is what the census names.
5. Rename `UnboundedTrialBlock` to `BoundedCompressionTrialBlock` (its compression is bounded;
   the current name has already misled one certificate, per the S2-tan-theta review note).
6. Retire the unqualified clause aliases `SectionTwo.tanTheta_{complex,real}`,
   `SectionTwo.sinTwoTheta_{complex,real}`, `SectionTwo.tanTwoTheta_{complex,real}` in favour of
   the `_directed_`/`_ambient_` names; keep `@[deprecated]` aliases one release, then delete.
   Rewrite the module docstring of `SectionTwo.lean` — most of its length is history of
   mistakes; a reader needs the table of clauses and witnesses, not the diary.
7. Delete `Proposition4_2_compact_nonacute` (unused `_J`, strictly weaker than
   `Proposition4_2_infiniteDimensional`) and deregister it.
8. Prune `lean_declarations` on `S2-sin-two-theta` and `S2-tan-two-theta` to canonical
   witnesses plus explicitly-roled `source_correspondence` lemmas; proof structure such as
   `diagonalPart_sq_add_offDiagonalPart_sq` and `complexifyReal_addBounded` does not belong on
   a result row. Do this by hand, row by row, reading each entry's `role`.

**Done when** `python3 scripts/check_declaration_name_drift.py`, `lake build Challenge`,
`aiq-lean namespaces check`, and the census all pass, and the review's case-twin and
root-namespace one-liners return nothing.

### R7 — Green certificate: clear the production warnings (Lean, 1 day)

**Problem.** `python3 scripts/certify_davis_kahan_1970.py --require-terminal` is `FAIL` on
`main` because `DavisKahan.All` emits 81 warnings.

**Repair.** Run `lake build DavisKahan.All` and fix every warning at its source:
`omit [...] in` for `unusedSectionVars` (28), remove unused `simp` arguments (12), delete
never-executed tactics (5), `simpa`→`simp` (4), replace deprecated
`ContinuousLinearMap.mul_apply`/`coe_comp'` (5), drop no-op `rw`s (2). `lean-warning-fix`
handles the mechanical ones; read each of the rest. Heaviest files are listed in review §F8.
Then run the certificate **without** `--allow-warnings` and commit the `build/…` summary line
into the review's follow-up section (not the bundle).

Also fix `scripts/certify_davis_kahan_1970.py` so `--output-dir` outside the repository does
not crash at `probe_path.relative_to(ROOT)` (write the probe under the output dir and pass an
absolute path to `lake env lean`, or reject off-tree paths with a clear message). This is a
bug fix in an existing gate, not a new checker.

**Done when** `python3 scripts/certify_davis_kahan_1970.py --require-terminal` prints
`status: PASS` on a clean tree with no flags.

### R8 — Stale and misleading row text (*census*, hours)

Fix, in `dev/davis-kahan-1970-formalization-result-inventory.json`:
* `source_representation_conventions.crossed-defect-dimension-equality.witness_scope` still
  says the infinite-dimensional reading "is not written"; `crossedDefectsEquivalent_iff_sameDimension`
  exists. Rewrite the paragraph to name it and drop the convention language.
* `S2-tan-theta.review_note` names the `_unboundedTrial_` pair as the directed clause's
  "registered primaries"; after R1/R6 it must name the unbounded-Ritz pair.
* The `KyFanDominantIdealFamily` "stronger in its own quantifier but not the printed one"
  notes (DK-6.3-thm and wherever else the phrase appears): reword per R9.
* Convert the long `review_note` diaries into a current-state sentence plus a pointer to
  Git history where the history matters. The reviewer packet is for a reviewer, not an
  archive.

### R9 — Norm-class wording (docstrings, one hour)

`SymmetricNormingFunction`'s docstring (`SineTheta/Norms/UnitaryInvariantNorm.lean`) and the
census call it "the literal Davis--Kahan class". Say instead: the class of unitarily invariant
norms generated by a dimension-coherent symmetric norming function (symmetrically normed
ideals in the Gohberg--Krein sense); note that this is every unitarily invariant norm in finite
dimension, and in infinite dimension excludes norms on `B(H)` such as `‖T‖ + ‖π(T)‖` that are
not determined by finite singular-value prefixes; note that `KyFanDominantIdealFamily` is the
abstraction that covers those, and which results are also stated over it. Do not change any
theorem.

## Order

R1 → R4 → R5 → R2 (option A) → R3 → R6 → R7 → R8 → R9. R1, R4, R5, R2-A are census-heavy and
independent of each other; do them first so the semantic state is honest before the renames.
R6 last among the Lean items so every name is touched once. R7 can run in parallel with R8/R9.

## Definition of done

Mechanical, all on a clean tree at one commit:
* `lake build` (default targets) and `lake build Challenge` succeed with zero warnings.
* `aiq-lean gates run --config dev/policy/gate-suite.yaml` — every gate passes or is
  `unavailable`; none skipped by you.
* `python3 scripts/certify_davis_kahan_1970.py --require-terminal` — `status: PASS`, 29/29,
  no `--allow-warnings`.
* `python3 scripts/check_declaration_name_drift.py` clean.
* The review's three one-liners (root-namespace registrations, case-twin names, canonical
  entries with empty `covers_source_atoms`) return nothing.

Semantic, written into a dated follow-up section appended to
`dev/davis-kahan-1970-hostile-review-2026-09-04.md` (do not rewrite the findings; append
"Closure, <date>" with one line per finding naming the commit and the declaration or row that
closes it):
* F1: DK-6.3-thm canonical witnesses have no spectral-gap hypothesis.
* F2: DK-8.1/8.2 rows state their operator scope, or are unbounded.
* F3: every registered tangent endpoint carries its pole-exclusion conjunct.
* F4: DK-5.1-lem canonical witnesses have no capability class.
* F5: ambient sin 2θ canonical witnesses take an arbitrary reducing subspace.
* F6: all eight naming/placement items closed, with the rename list.
* F7--F9: closed by wording; F8 by a green certificate line.

Then publish the tally in its own commit and push `main`.

## What not to do

* Do not reclassify any of the 29 results, change the denominator, or edit the distributable
  TeX. Nothing in the review asks for it.
* Do not "fix" a finding by deleting the theorem it is about.
* Do not make a gate green by removing what it checks, and do not add `--allow-warnings` to
  any documented command.
* Do not write a new checker for the case-twin / namespace / empty-coverage conditions; they
  are three one-liners in the review and the existing `aiq-lean source|namespaces` gates cover
  the durable part.
* Do not recreate lane claims, coordination boards, or scratch overlays.
