# Davis--Kahan 1970 formalization-result inventory contract

This file records the checker contract for the denominator behind the phrase
**100% formalized**.

## Two inventories, two jobs

`prose/distilled_literature/DavisKahan1970_part_III.tex` and
`dev/davis-kahan-1970-source-atom-inventory.json` answer the **source-fidelity**
question: did the distributable reconstruction preserve the paper's
mathematical story in source order?  That inventory may be fine-grained enough
to mention proof equations, intermediate identities, calculations,
counterexamples, historical comparisons, and explanatory statements.

Those source-fidelity atoms are **not Lean proof obligations merely because they
are mathematical**.

The separate formalization-result inventory answers the **completion** question.
Its denominator consists only of results Davis--Kahan state as results:

- theorems, propositions, lemmas, and corollaries;
- the four unnumbered headline theorems in Section 2;
- any other clearly standalone theorem-like result;
- distinct conclusions of a stated result when they require distinct exact Lean
  statements;
- exact source scope attached to those results (real/complex,
  finite/infinite-dimensional, bounded/unbounded, norm class, directed/ambient,
  and separation hypotheses).

Definitions remain source-fidelity material needed to state the results.  Pure
open questions may be listed for source accounting but are not proof
obligations.  Proof equations and intermediate derivations do not enlarge the
formalization denominator.

## Discovery

The checker looks first for one of these keys in
`dev/davis-kahan-1970-statement-map.json`:

- `formalization_result_inventory`
- `result_inventory`
- `completion_result_inventory`

If no key is present it recognizes, by default:

- `dev/davis-kahan-1970-formalization-result-inventory.json`, or
- `dev/davis-kahan-1970-result-inventory.json`.

Until a result inventory exists, ordinary source/census checks may run, but
`--require-terminal` fails closed: the project has no defensible denominator for
a 100% formalization claim.

## Minimum result-inventory shape

The checker accepts `results` or `items` as the entry list.  A representative
terminal entry is:

```json
{
  "id": "S2-tan-theta.directed",
  "parent_claim_id": "S2-tan-theta",
  "result_kind": "unnumbered_theorem",
  "completion_obligation": true,
  "source_atom_ids": [
    "S2-tan-theta.gap-hypothesis",
    "S2-tan-theta.directed-conclusion"
  ],
  "disposition": "proved_exact",
  "verification": "proved_in_build",
  "semantic_certification": "accepted",
  "lean_declarations": [
    "TauCeti.DavisKahan1970.someExactSourceFacingTheorem"
  ]
}
```

An open question has `result_kind = "open_question"`,
`completion_obligation = false`, an open-question disposition, and no proof
bindings.

The result inventory must also contain an accepted selection review (accepted
key names are `result_inventory_review`, `selection_review`, or
`coverage_review`) with:

```json
{
  "status": "accepted",
  "policy": "stated_results_only",
  "source_fidelity_inventory_sha256": "...",
  "distributable_specification_sha256": "...",
  "method": "Reviewed the source-fidelity inventory/source specification in paper order and selected every stated result while excluding proof-only mathematics from the completion denominator."
}
```

The hashes make the selection audit fail stale after either the fidelity
inventory or distributable TeX changes.

### Total classification bridge

To prevent a real theorem from disappearing between the fine-grained fidelity
inventory and the compact result inventory, **every source-fidelity atom must be
classified**.  The classification may live inline on each fidelity atom under
`formalization_role` / `formalization_result_role` / `completion_role`, or in the
result inventory under `source_atom_classification`.

Atoms selected by one or more formalization results use a result-support role
(`result`, `stated_result`, `result_support`, `result_hypothesis`, or
`result_scope`).  Atoms not selected into the theorem/result denominator need an
explicit non-result reason, such as `definition`, `proof_only`, `derivation`,
`historical`, `numerical_working`, `expository`, or `open_question`.

This classification is bookkeeping, not new theorem work.  Its purpose is to
make omission visible: the hard gate rejects an unclassified fidelity atom, a
result-support atom selected by no result, or a proof-only atom that has been
accidentally promoted into the result denominator.

## Terminal result semantics

A proof obligation is terminal only when all of these are true:

1. its disposition is exact proof or formal source refutation;
2. compiler verification is `proved_in_build`;
3. hostile semantic certification is `accepted`;
4. it names at least one source-facing Lean declaration;
5. those declarations are registered by the maintained source census.

For a false printed source result, `refuted_as_transcribed` faithfully settles
the printed claim but the project policy creates a **separate best-effort repair
obligation**.  Such a result must carry a `repair` object.  A terminal repair is
either:

- `status = "proved"` with registered Lean repair declaration(s), or
- `status = "documented_no_satisfactory_repair"` with a substantive explanation.

This preserves the distinction between "the paper said X and X is false" and
"what mathematically useful theorem survives after diagnosing X?".

## Gates

Structural/source-fidelity check:

```bash
python3 scripts/check_davis_kahan_1970_statement_map.py
```

Result-inventory check:

```bash
python3 scripts/check_davis_kahan_1970_result_inventory.py
```

Hard 100% gate:

```bash
python3 scripts/check_davis_kahan_1970_statement_map.py --require-terminal
```

The hard gate is intentionally result-level.  A green build, 266/266
source-fidelity atoms, or 49/49 organizational rows cannot substitute for
terminal stated-result coverage.
