# Davis--Kahan 1970 formalization-result inventory contract

This file defines the denominator behind **100% formalized**.

## Two inventories, two jobs

`prose/distilled_literature/DavisKahan1970_part_III.tex` and
`dev/davis-kahan-1970-source-atom-inventory.json` answer the source-fidelity
question: did the distributable reconstruction preserve the mathematical content
and order of the paper? Source-fidelity atoms may include definitions, proof
equations, intermediate identities, calculations, examples, historical claims,
and open questions.

Those atoms are **not Lean proof obligations merely because they are
mathematical**.

`dev/davis-kahan-1970-formalization-result-inventory.json` answers the completion
question. Its denominator is exactly the results Davis--Kahan actually establish
in this paper:

- the four unnumbered headline theorems in Section 2; and
- every named theorem, proposition, lemma, and corollary in Sections 3--8.

At the current source revision this gives 29 result obligations. Exact result
scope is part of the obligation. Distinct conclusions or real/complex branches
may be backed by separate Lean declarations without becoming separate source
results.

## What is deliberately excluded

The result denominator does not include definitions, proof-only equations,
intermediate derivations, examples, numerical working, historical or externally
attributed results, or explanatory statements merely because they are true.
Section 10 questions are not obligations. Claims the paper explicitly leaves
unresolved, or whose proof it defers to an open question, are also not obligations.
They remain in the source-fidelity inventory with an explicit non-result role.

This selection rule is intentionally narrower than "every mathematical claim".
The project claim is that every **result proved by Davis--Kahan in the paper** is
formalized exactly, not that Lean reproduces every line of the paper's proof.

## Total classification bridge

Every source-fidelity atom must carry a `formalization_role`. Atoms used to state
or scope a counted result use one of:

- `result_support`
- `result_hypothesis`
- `result_scope`

Everything else must be explicitly classified with a non-result role such as
`definition`, `proof_only`, `numerical_working`, `historical`, `open_question`,
or `non_result`. The classification exists to make accidental omission visible;
it does not create theorem work.

The accepted result-selection review records SHA-256 hashes of both the fidelity
inventory and distributable TeX. If either changes, the selection review becomes
stale and must be repeated.

## Terminal result semantics

A counted true result is terminal only when:

1. its disposition is exact proof;
2. compiler verification is `proved_in_build`;
3. hostile semantic certification is `accepted`;
4. it names source-facing Lean declaration(s); and
5. those declarations are registered by the maintained source census.

A false printed result remains a counted source result and is terminal only after
an exact formal refutation. Repository policy additionally creates a separate
best-effort repair obligation. A terminal repair is either a proved natural
correction with registered Lean declaration(s), or a substantive record that no
satisfactory correction could be justified. Proposition 4.4 is the canonical
example: exact refutation plus the proved `Q`-norm repair.

## Gates

Source-fidelity / structural check:

```bash
python3 scripts/check_davis_kahan_1970_statement_map.py
```

Result-denominator check:

```bash
python3 scripts/check_davis_kahan_1970_result_inventory.py
```

Hard 100% gate:

```bash
python3 scripts/check_davis_kahan_1970_statement_map.py --require-terminal
```

A green build, 266/266 source-fidelity atoms, or 49/49 organizational rows cannot
substitute for terminal coverage of the 29 counted results.
