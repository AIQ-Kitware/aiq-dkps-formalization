# Davis--Kahan 1970 private-source workflow

A private modernized transcription, when available, and any publisher PDF are local
comparison/provenance sources. They are not part of the distributable
repository and no repository validation command may require them.

The distributable mathematical source specification is:

`prose/distilled_literature/DavisKahan1970_part_III.tex`

It has two simultaneous roles:

1. a readable, independently worded reconstruction in the presentation order of
   Davis--Kahan (1970); and
2. the static semantic audit baseline. Text between each
   `DK-CERT-SOURCE-BEGIN` / `DK-CERT-SOURCE-END` pair is hashed by
   `dev/davis-kahan-1970-statement-map.json` and compared against the mapped Lean
   declarations by the audit packet.

The file must preserve the mathematical content needed for exact statement
comparison: standing hypotheses, theorem hypotheses and conclusions, relevant
displayed equations, exceptional branches, counterexamples, symmetry/extension
clauses, bounded/unbounded and finite/infinite-dimensional scope, and the source
presentation order. It must remain transformative: paraphrase prose and avoid
continuous reproduction of the private transcription.

Do not create a second copied "exact source register." A duplicate authority can
silently diverge from the distributable reconstruction and makes a public
checkout depend conceptually on non-distributable material.

The maintained completion/status authorities are:

- `dev/davis-kahan-1970-full-source-census.json` — authoritative structured
  source ledger;
- `dev/davis-kahan-1970-full-source-census.md` — generated human view;
- `dev/davis-kahan-1970-statement-map.json` — hashes the distributable TeX
  passages and binds them to Lean declarations;
- `dev/davis-kahan-1970-formalization-result-inventory.json` — the 29-result
  completion denominator.

Dated completion plans and handoffs are historical records, not proof queues.
If they disagree with the checked source specification, the census, the result
inventory or the build, the checked artifacts win.

A local provenance audit may compare the private transcription or paper against
`DavisKahan1970_part_III.tex`. This checks the *distillation itself* and is
separate from the ordinary static source-to-Lean audit. A fresh public checkout
must be able to run the statement-map and compiler certificate without access
to that private material.

When the private transcription is revised or re-audited:

1. independently inventory the original mathematical claims in presentation
   order;
2. repair the public distillation in independent wording without changing the
   mathematics;
3. update claim markers/map/census metadata when the audit unit boundaries
   change;
4. regenerate derived Markdown views and the independent audit template;
5. run `python3 scripts/check_davis_kahan_1970_statement_map.py`,
   `python3 scripts/check_davis_kahan_1970_source_census.py`, and
   `python3 scripts/check_davis_kahan_1970_result_inventory.py`;
6. never add the private file or publisher source to an overlay or archive.
