# Davis--Kahan 1970 formalization-result inventory contract

This file defines the maintained denominator behind **100% formalized**.

## The formalization criterion

**The fundamental unit is a Davis--Kahan RESULT, not a source atom.**  Source
atoms exist so a hostile reviewer can audit the source-to-Lean correspondence;
they do not independently create proof obligations.

### What belongs in the denominator

A source item belongs to the formalization denominator when Davis and Kahan
present it as a mathematical result of the paper **and provide a proof for it**.
That is the four unnumbered Section 2 headline theorems plus the paper's proved
named theorems, propositions, lemmas and corollaries.  A fresh source audit may
identify another genuinely independent proved result.  Definitions, proof steps,
intermediate identities, examples, explanatory remarks, immediate consequences,
restatements, and open or deferred claims do **not** become separate
formalization obligations merely because they contain mathematical assertions.

### The objective is semantic equivalence of results

Not reproduction of the paper's proofs.  For every counted result the repository
must identify canonical Lean theorem evidence and support this claim under
hostile review:

> The hypotheses, mathematical objects, scope and conclusions of this Lean
> theorem are the same as those of the corresponding Davis--Kahan result, after
> making explicit any definitions or standing conventions the paper uses.

The Lean proof may use different lemmas, abstractions, representations,
reductions, proof order, or stronger intermediate results.  An intermediate step
of the paper need not be separately formalized unless it is itself a counted
result.

### What hostile review must be able to check

* the mathematical hypotheses;
* the conclusion or conclusions;
* constants and inequality direction;
* the precise angle, subspace, residual, perturbation or operator being bounded;
* the norm class;
* finite- versus infinite-dimensional scope;
* real versus complex scalar scope where applicable;
* bounded versus unbounded operator scope;
* spectral-gap assumptions, including any half-infinite cases actually belonging
  to the result;
* standing assumptions or nonlocal conventions genuinely required by the paper;
* representative or multiplicity issues that affect unitarily invariant norms.

Where a source formulation and the Lean formulation are equivalent but the
equivalence is not apparent from the theorem types, an explicit correspondence
lemma must be supplied.  `lowerFrameBound_iff_source_operator_inequality` is the
model: the source prints Theorem 6.1's hypothesis as `E₀* E₀ ≥ ε² I` while the
Lean statement takes `LowerFrameBound E₀ ε`, and that theorem is why a reviewer
does not have to accept the equivalence informally.

### When a later passage affects a counted result

Only when it is necessary to determine **what Davis and Kahan actually claim** in
that result under the paper's own semantics — a standing convention, a
definition, or a scope sentence the printed statement relies on.  A later passage
does **not** enlarge the result merely because it discusses a stronger variant,
an extension, a consequence, or another case.  If such a passage is itself a
distinct substantive result that Davis and Kahan introduce *and prove*, it
belongs in the denominator, and that is a decision for a fresh result-selection
audit — never something the atom ledger may do by reclassifying an atom.

> **Corrected 2026-08-31.**  `selection_definition.statement_boundary` previously
> ended: *"A later source passage that explicitly extends the proved scope of a
> counted result is part of that result's scope and must be covered."*  That
> contradicted the same field's own `does_not_count` entry for scope remarks
> outside the printed result environment, and under it a scope-atom audit briefly
> reopened five results and took the certificate to 24/29.  The four passages
> involved — the Theorem 5.1 `A`/`B` interchange and unbounded-`A` remarks, the
> Appendix sentence saying Proposition 6.1 and Theorem 6.1 "admit the analogous
> relaxation", and the Section 8 sentence extending `sin 2Θ` to unequal
> dimensions — are each an extension the paper *mentions* without introducing and
> proving it as a result of its own.  They are `result_adjacent_extension`
> fidelity material.  The Lean coverage written while the results were reopened
> is kept as **supporting** evidence: stronger than the counted statements
> require, which is worth holding and is not a canonical obligation.

### A terminal certificate

Every substantive result introduced and proved by Davis and Kahan has canonical
Lean evidence — a proof, or an exact formal refutation where the printed result
is false — and every canonical Lean statement has been audited against the
corresponding source result closely enough to withstand a hostile
theorem-by-theorem comparison.

The denominator is a set of **source results**, not a count of source assertions
or proof steps.  The ~274 source atoms are the evidence base for auditing the 29;
they are deliberately far more exhaustive than the theorem denominator.

## Two inventories, two jobs

`prose/distilled_literature/DavisKahan1970_part_III.tex` and
`dev/davis-kahan-1970-source-atom-inventory.json` answer the **source-fidelity**
question: did the distributable reconstruction preserve the mathematical content
and order of the paper? The fidelity inventory is deliberately exhaustive enough to
record definitions, proof equations, intermediate identities, calculations,
examples, historical/external statements, deferred claims, and open questions.

Those atoms are **not Lean proof obligations merely because they are
mathematical**. Their purpose is disclosure: a hostile reviewer can see what the
project intentionally does and does not include in its completion claim.

`dev/davis-kahan-1970-formalization-result-inventory.json` answers the
**completion** question. Its denominator is exactly the results Davis--Kahan
actually establish in this paper:

- the four unnumbered headline theorems in Section 2; and
- every named theorem, proposition, lemma, and corollary Davis--Kahan establish
  in Sections 3--8.

At the current audited source revision this is **29 results**. Exact source scope
is part of each obligation. Several Lean declarations may jointly cover one source
result without creating extra source results.

## What is deliberately excluded from the denominator

The 100% denominator does not include definitions, setup, proof equations,
intermediate derivations, examples, numerical working, sharpness/interpretation
remarks outside a designated result, immediate consequences outside the printed
result statement, historical or externally attributed results, later restatements
of already-counted results, Section 10 questions, or claims the paper explicitly
leaves unresolved/deferred. They remain visible in the source-fidelity inventory.

The rule is intentionally narrower than "every mathematical claim": the project
claims exact formalization of every **result Davis--Kahan establish**, while
separately claiming faithful accounting of the broader mathematical surface.

## Explicit boundary accounting

Every one of the 274 source-fidelity atoms must carry:

1. a `formalization_role`;
2. a specific `formalization_role_reason_code` and explanatory
   `formalization_role_reason`; and
3. `formalization_result_ids`, the exact reverse link to the counted result(s) the
   atom supports, or an empty list when it is deliberately outside the denominator.

Result-support atoms use explicit statement/hypothesis/scope reason codes.
Fidelity-only atoms use a reason that identifies *why* they are outside the
denominator, for example proof/derivation, pre-result setup, post-result
consequence, worked example, historical attribution, deferred/unproved claim, or
open question. A generic unexplained `non_result` is insufficient.

Every counted result must carry an accepted `boundary_review`. For its primary
source block the review records exactly:

- `included_same_block_atom_ids`: atoms inside the printed result statement;
- `excluded_same_block_atom_ids`: adjacent atoms deliberately outside it; and
- `cross_block_scope_atom_ids`: source-scope atoms needed from another registered
  block.

The checker verifies both directions: result entries must point to the same atoms
that point back to them, and the boundary partition must exactly cover the primary
block. This is the defense against silently dropping a theorem conclusion while
also avoiding the opposite error of turning proof details into theorem obligations.

The accepted result-selection review records SHA-256 hashes of both the
source-fidelity inventory and distributable TeX and records
`policy = dk_established_results_only` plus
`boundary_review_status = accepted`. If either source artifact changes, the
selection review becomes stale. The current denominator size is also hard-checked
at 29; changing it requires a fresh original-paper result-selection audit rather
than an incidental metadata edit.

## Source-alignment taxonomy and nonlocal source interpretations

Every counted result carries two extra fields, and the checker rejects a row that
omits either:

- `semantic_alignment` — one of `locally_exact`,
  `paper_faithful_nonlocal_source_interpretation`, or `refuted_as_transcribed`;
- `local_statement_self_contained` — an explicit boolean.

Most printed statements are locally self-contained: everything Lean needs is in
the printed environment. A few are not, because the paper imposes semantics
elsewhere — a global convention, a later standing assumption, an inherited proof
context. For those, Lean necessarily states something the printed display does
not literally state, and hiding that from a reviewer would be the worst possible
outcome. Such a row must carry a `nonlocal_source_interpretation` record with:

- `status`, `classification`, and a `local_statement_self_contained` that agrees
  with the row;
- `reviewer_issue`, `awkwardness`, `accepted_reading`,
  `alternative_literal_reading`, `why_not_refutation`, `semantic_conclusion` —
  each a substantive reviewer-facing explanation, with the competing literal
  reading stated at its strongest;
- `nonlocal_dependencies` — the source material that supplies the missing
  semantics;
- `supporting_atom_ids` — real source-fidelity atoms, each of which must carry an
  `interpretation_support` block naming this result. The checker verifies both
  directions, so an atom cannot claim to support a reading that does not cite it;
- `lean_explicitation` — the declarations that make the implicit semantics
  explicit, each with the exact hypothesis or conclusion that does it. Every such
  declaration must be registered in the census and `#check`ed in the compiler
  audit surface;
- `distinct_from_refutation` — the counted result that is the repository's
  canonical refutation, so the two categories stay visibly separate;
- three staleness hashes: the distributable TeX, the source-fidelity inventory,
  and a digest of the cited atoms. Any edit to the source specification or to the
  cited evidence makes the accepted reading stale and the checker fails closed.

`interpretation_support` on an atom is **not** `formalization_result_ids`. The
latter is the printed-statement boundary and feeds the 29-result denominator; the
former is evidence about how a printed statement is read and adds nothing to the
denominator.

The middle category is never a softened refutation. `refuted_as_transcribed`
keeps its full meaning: all objects exist, the printed hypotheses hold, the
compared quantities are finite and meaningful, and the printed conclusion is
false. Proposition 4.4 remains the canonical case. A result is placed in the
middle category only when the printed statement is true under the paper's own
semantics and the formalization merely makes those semantics explicit.

The generated audit packet renders a **NONLOCAL SOURCE-SEMANTICS DEPENDENCY**
section for every such row, reproduces the cited source passages so the reading
can be checked without the original paper, and asks the reviewer for one of
`PASS paper-faithful nonlocal interpretation`, `FAIL illicit strengthening`, or
`UNCERTAIN source interpretation`.

## Terminal result semantics

A counted true result is terminal only when:

1. its disposition is exact proof;
2. compiler verification is `proved_in_build`;
3. hostile semantic certification is `accepted`;
4. it names source-facing Lean declaration(s); and
5. those declarations are registered by the maintained source census.

A false printed counted result remains in the denominator and is terminal only
after an exact formal refutation. Repository policy additionally creates a
separate best-effort repair obligation. A terminal repair is either a proved
natural correction with registered Lean declaration(s), or a substantive record
that no satisfactory correction could be justified. Proposition 4.4 is the
canonical example: exact refutation plus the proved `Q`-norm repair.

## Canonical evidence

`lean_declarations` mixes primary witnesses, fixed-field companions, presentation
wrappers, stronger generalizations, specializations, implementation structures and
conformance theorems.  Agents repeatedly picked the wrong theorem out of that list
by name or by ordering, so the list is now **partitioned**.

Every counted result carries two arrays, and their union must be exactly
`lean_declarations`:

* `canonical_evidence` — the declarations that carry the printed statement.  This
  answers *which declarations should an auditor compare with the paper?*
* `supporting_evidence` — everything else: generality, transport, compatibility,
  alternative presentations.  This answers *what else is registered, and why?*

### `canonical_evidence` entry fields

| field | meaning |
| --- | --- |
| `declaration` | the Lean name; must be in this result's `lean_declarations`, registered in the source census, and `#check`ed by the audit surface |
| `role` | `primary_source_witness`, or `exact_refutation` for a printed statement that is false |
| `evidence_kind` | `proof` or `refutation`; must pair with `role` |
| `scalar_scope` | `complex`, `real`, `rclike`, `scalar_generic`, `mixed`, `not_visible_in_type` — **derived from the compiler-printed type, not asserted** |
| `scalar_scope_note` | required when `scalar_scope` is `not_visible_in_type`; says where the scalar actually lives |
| `capability_classes` | the proof-capability instance binders the printed type carries — **also derived** |
| `covers_source_atoms` | which of the result's source atoms this declaration establishes |

`supporting_evidence` entries carry `declaration` and a `role` from a fixed
vocabulary (`public_alias`, `specialization`, `alternative_route`,
`generalization`, `presentation_wrapper`, `implementation_structure`,
`transport_lemma`, `scalar_generic_facade`, `supporting_theorem`), plus an
optional `note`.

### What the checker enforces

* canonical and supporting partition `lean_declarations`, with no overlap and
  nothing left over;
* every canonical declaration is registered in the source census **and**
  `#check`ed by the audit surface — no canonical claim without compiler evidence;
* the union of `covers_source_atoms` over canonical evidence covers every source
  atom of a **terminal** result, and no atom outside the result;
* a **nonterminal** result may *not* claim complete canonical atom coverage —
  either the coverage or the status is wrong;
* supporting evidence cannot make a result terminal: a result with no canonical
  evidence fails;
* `DK-4.4-prop` — the one printed statement that is false — must carry
  `role: exact_refutation` / `evidence_kind: refutation` and disposition
  `refuted_as_transcribed`; no other result may claim a refutation;
* the census `semantic_review.canonical_declarations` for a counted result must be
  a subset of that result's canonical evidence.  (It was not: the packets for
  three of the four Section 2 results named a *finite-dimensional* facade as
  canonical for a result certified at unbounded infinite-dimensional scope.)

### Scalar scope and capability classes are compiler-derived, not asserted

The checker `#check`s every canonical declaration through the same Lean probe the
source census uses, and reads two things off the printed type:

* the **scalar scope**, from the field position of `InnerProductSpace` /
  `NormedSpace` binders — `[RCLike 𝕜]` over a bound field is `rclike`,
  `NontriviallyNormedField` is `scalar_generic`, a concrete `ℂ` or `ℝ` is
  `complex` or `real`.  A parameter such as `δ : ℝ` occurs in nearly every
  statement and is deliberately ignored;
* the **capability classes** it carries, from a policy vocabulary
  (`HasMinMaxLowerBoundEverywhere`, `HasUnboundedSylvesterKyFan`,
  `HasApproximationNumberStrongCutoff`).  Any *other* instance binder whose head
  matches `…Has<Something>` is an error rather than a silent pass, so a new
  capability class cannot appear in a canonical signature unclassified.

Both are compared against the recorded values and fail on disagreement.  This is
not decoration: nine canonical entries claimed `complex` for declarations whose
types quantify over `[RCLike 𝕜]`, including both halves of Lemma 6.1.

`--no-lean-probe` skips the probe for use on a tree that does not compile, and
prints a NOTE saying the scopes were **not** verified.  Never present the values
as certified after that flag.

### Capability classes and the choice of canonical witness

A capability class has instances for both of the paper's scalar fields, so a
generic declaration carrying one still proves the printed result at `ℝ` and at
`ℂ`.  But `RCLike` is an **open** class, so at any other field the binder is a
genuine hypothesis — and the paper prints no such hypothesis.  The rule that
follows:

> When a capability-class-free pair of fixed-field declarations states the result
> at the printed scope, that pair is the canonical evidence and the generic form
> is `supporting_evidence` with role `generalization`.  When no such pair exists,
> the generic declaration is canonical and its `capability_classes` are recorded.

`S2-sin-theta` is the first case; `DK-5.1-lem`, `DK-6.1-lem` and `DK-6.2-lem` are
the second.  A declaration that is merely the `ℝ` instance of a canonical
`RCLike` theorem — proof: that theorem applied — is `supporting_evidence` with
role `specialization`, not a second primary witness.

### Coherent clauses: one witness per printed clause

`canonical_evidence` alone was not enough, and the way it failed is worth
stating plainly.  It recorded, per declaration, a set of source atoms that
declaration covered, and a result was terminal when the **union** over its
declarations covered the row.  That accepts a certificate assembled from pieces
no theorem proves together.  It happened, in `S2-sin-two-theta`:

```text
unbounded DIRECTED theorems  ->  unbounded scope, gap scope, bounded residual
bounded  AMBIENT  theorem    ->  the ambient conclusion
union                        ->  "the ambient conclusion at unbounded scope"
```

No declaration and no proof chain establishes that conjunction.

Every counted result therefore carries:

* `result_wide_scope_atoms` — scope and hypothesis atoms that hold of the printed
  result as a whole, and that **every** clause's witness must carry;
* `source_clauses` — one entry per printed clause per scalar field.

Each clause names **one** `evidence.primary`, optionally with
`evidence.correspondence` lemmas, and records `conclusion_atoms`, an optional
`clause_hypothesis_atoms` local to it, a `scalar_scope`, a `status`
(`established` / `open`), and a `justification` naming the printed clause it
discharges.  An `open` clause must say in `open_reason` exactly what is missing.

The checker then requires:

* the clause's primary is **canonical evidence of that result** — not a
  specialization or a presentation wrapper held as supporting evidence, which
  would leave the coherence check with no compiler-printed type to work with;
* the clause's `scalar_scope` equals the primary's, and the primary's is
  **compiler-derived** — so a result cannot claim both of the paper's scalar
  fields from one theorem;
* the clause's primary satisfies the `type_requirements` of its own conclusion
  atoms **and of every result-wide scope atom** — so scope cannot be donated by a
  sibling declaration;
* every printed conclusion of the result is discharged by some established
  clause, at **both** of the paper's scalar fields, unless one scalar-generic
  clause covers them or the conclusion is discharged by an `exact_refutation`
  (one counterexample refutes a claim the source makes over either field);
* a terminal result has no open clause and no undischarged conclusion, and a
  nonterminal result has at least one of them;
* `canonical_evidence[…].covers_source_atoms` is **derived** from the clauses and
  must equal the derivation — the hand-authored union is gone.

A *printed conclusion* is a source atom of kind `theorem`, `lemma` or
`source-assertion`.  That list was `theorem` alone until 2026-08-31, and the
omission was a hole: the four Section 6 lemmas state their conclusions under
`lemma`, and Proposition 4.4 — false as printed — under `source-assertion`, so
for those five results the coverage rule was vacuous and a clause could name no
conclusion at all.

This is deliberately not the crude rule "every canonical theorem must contain
every atom on the row".  Clause conclusions stay clause-local, fixed-field
siblings are separate clauses, a clause may carry hypotheses that belong to it
alone, and a theorem stronger than the paper is not penalised for omitting a
printed hypothesis it does not need.  `scripts/tests/test_davis_kahan_coherent_evidence.py`
pins both directions: the negative test reconstructs the old
`S2-sin-two-theta` composition and requires rejection *with the right
diagnosis*; the positive tests pin real/complex siblings, separately discharged
directed and ambient clauses, a clause-local hypothesis, and a
primary-plus-correspondence chain.  Four further negative tests, added by the
2026-08-31 result-by-result review, pin the four rules that review found missing:
a supporting-evidence primary, a clause scalar field contradicting its primary, a
conclusion stated under `lemma`, and gap tokens absent from the printed type.

### Scope that a printed type cannot decide

`type_requirements` on a source atom are a **necessary** condition read off the
compiler-printed type — `→ₗ.[` for unbounded ambient scope, no
`FiniteDimensional`, `PaperUnitaryInvariantNorm` for the source norm, `→L[` for a
bounded residual.  Where no substring decides the question, the atom instead
carries `scope_assertion_mode: clause_justified` and every clause must record a
named justification.  `half-infinite-gap-intervals` is the case: the tangent
family realizes it through an ORDERED spelling (`SemiboundedAbove` plus a
coercivity bound) and `tan 2Θ` through bare form bounds with `a < b`, so
requiring the `FormBoundedSylvesterGap` token would have rejected four correct
theorems.  A wrong requirement is worse than none.

Prose alone would be an escape hatch, so such a clause must also record
`gap_scope_hypothesis_tokens`, and **every token must occur in the primary's
compiler-printed type**.  A justification can still be wrong about what those
hypotheses mean; it can no longer claim a scope realized by hypotheses the
theorem does not have.

### Staleness

`semantic_review_sweep.canonical_evidence_sha256` digests every result's canonical
evidence — declaration, role, scalar scope, evidence kind, covered atoms and
capability classes.  Changing any of them makes the accepted semantic sweep stale
and the checker fails.  Canonical evidence is the answer to *what proves this
result*, so editing it must be re-reviewed rather than inherited.

## Scope atoms carry an explicit classification

Every source atom with `kind: "scope"` stating a mathematical assertion carries a
`scope_classification`: one of

| category | meaning |
| --- | --- |
| `counted_result_scope` | needed to determine what a counted result claims; must be covered |
| `result_adjacent_extension` | an extension, variant, consequence or further case the paper mentions around a counted result without introducing and proving it as a result of its own — fidelity material, and any Lean coverage of it is *supporting* evidence |
| `source_wide_setup` | ambient setting or convention governing the whole paper |
| `reading_interpretation` | tells a reader how to read a statement (automaticity, vacuity conventions) |
| `proof_context` | sits inside a proof and describes the argument |
| `non_extending_commentary` | motivation, negative remarks, worked-example choices |

together with the results it extends (exactly when the category says it extends
any), a substantive rationale, and a **verbatim quotation** from the
distributable specification, so a reviewer checks the classification against the
source rather than against a summary.

The checker refuses three reason codes for such an atom —
`post_result_scope_remark_not_in_printed_statement`,
`expository_commentary_not_result` and
`introductory_background_not_designated_result` — because each says only that the
passage lies outside the printed statement, which by itself decides nothing.

## One owner for mutable status

Facts that move are recorded once, structurally, and checked — never restated in
prose in several places:

* **which `SectionTwo.*` short names are bound** — `section_two_short_names` in
  the inventory, compared against `SectionTwo.lean`'s own `alias` lines.  Four
  census notes and four inventory notes previously asserted that all four were
  unbound, and went on saying it after `SectionTwo.sinTheta` was bound;
* **the terminal count and per-result status table** in
  `dev/davis-kahan-1970-formalization-result-inventory.md` — checked line by line
  against the JSON;
* **which declaration is canonical** — `canonical_evidence`, with the census
  packet checked against it.

## Reviewer-facing claim

A final certificate should make both layers explicit:

- **274/274 source items accounted for** does *not* mean 274 theorems were proved;
- **29/29 established results exact/refuted and accepted** is the 100% formalization
  claim; and
- every excluded source item remains displayed with its boundary rationale so a
  reviewer can challenge the exclusion directly.

## Static semantic evidence surface

The result inventory is not allowed to promote a result using declaration names that exist
only in JSON.  `semantic_review_sweep` names two maintained reviewer artifacts:

- `DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean`, which
  imports `DavisKahan.All` and `#check`s every declaration selected by all 29 result
  entries plus the strongest existing evidence for each red result; and
- `dev/davis-kahan-1970-result-semantic-review-2026-08-12.md`, which records the
  source-boundary comparison, the accepted semantic judgement, or the exact residual gap.

The result checker requires those artifacts to mention every selected declaration/result,
and the compiler certificate separately runs `lake env lean` on the Lean audit surface.
Thus a hostile reviewer can inspect the source passage, inspect the actual Lean theorem
type, and reproduce the compiler check without trusting a prose status flag.

## Gates

Source-fidelity / structural check:

```bash
python3 scripts/check_davis_kahan_1970_statement_map.py
```

Result-denominator and boundary-accounting check:

```bash
python3 scripts/check_davis_kahan_1970_result_inventory.py
```

Hard 100% gate:

```bash
python3 scripts/check_davis_kahan_1970_statement_map.py --require-terminal
```

A green build, 274/274 source-fidelity atoms, or 50/50 organizational rows cannot
substitute for terminal coverage of the 29 counted results.
