# Davis--Kahan 1970 formalization-result inventory contract

This file defines the maintained denominator behind **100% formalized**.

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

Every one of the 266 source-fidelity atoms must carry:

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

## Reviewer-facing claim

A final certificate should make both layers explicit:

- **266/266 source items accounted for** does *not* mean 266 theorems were proved;
- **29/29 established results exact/refuted and accepted** is the 100% formalization
  claim; and
- every excluded source item remains displayed with its boundary rationale so a
  reviewer can challenge the exclusion directly.

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

A green build, 266/266 source-fidelity atoms, or 49/49 organizational rows cannot
substitute for terminal coverage of the 29 counted results.
