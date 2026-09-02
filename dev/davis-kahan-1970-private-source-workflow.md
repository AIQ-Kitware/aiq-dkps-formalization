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

## Reading the source beside the Lean, in the browser

The `DK-CERT` passages are resolvable coordinates, not only hashing targets. The
`DavisKahan1970` work in `prose/distilled_literature/source_manifest.json`
declares `source_document: {marker_prefix: "DK-CERT", macro_files: ["preamble.tex"]}`,
so a semantic review can cite a passage by marker and the alignment browser
renders it -- prose, displayed equations and all -- next to the Lean declaration
that answers it:

```bash
aiq-lean alignment html dev/davis-kahan-1970-full-source-census.json \
    --statements --graph build/leanq/project-semantic-graph.json \
    -o build/davis-kahan-alignment.html
aiq-lean alignment html dev/davis-kahan-1970-full-source-census.json \
    --row DK-8.2-thm -o build/theorem-8-2.html
aiq-lean serve --root .          # the same view, beside every census
```

A review row declares the passages it depends on, each with a role:

- `primary` -- the printed passage the result states;
- `standing_assumption` -- a condition the source put in force earlier, which
  this result inherits without restating. `DK-8.2-thm` cites `S3-standing-scope`
  for (3.5) and reads `nonlocal`; a row that claims a `local` reading while
  citing one of these fails validation.
- `definition` / `convention` / `context` -- material a reviewer needs in order
  to judge the passage.

`aiq-lean alignment pin` records the content hash of each cited passage beside
the elaborated-type hashes, and `aiq-lean alignment check` fails with
`source-drift` when a repaired distillation moves a passage a review had already
accepted. **Repairing the distillation is therefore a two-step change:** edit the
TeX, then re-read the affected rows and re-pin them. That is the point --- the
old workflow let a repair land silently under an accepted review.

The private transcription can be read in the same browser without entering the
repository. Declare it in a JSON file **outside** the checkout and pass it:

```bash
aiq-lean serve --root . --private-sources ~/private/dk-sources.json --include-private
```

A private path inside the checkout is refused. Without `--include-private` the
passage's identity, locator and hash are shown and its text is withheld, so a
generated page or a committed ledger never carries it. Step 6 below is unchanged
and now has tooling behind it.

See `submodules/aiq-lean-formalization-tools/docs/source-model.md` for the model.

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
6. run `aiq-lean alignment check dev/davis-kahan-1970-full-source-census.json
   --source-only`, re-read every row it reports as `source-drift`, and re-pin
   with `aiq-lean alignment pin ... --source-only` **as part of the same
   change** --- a repaired passage that is silently re-pinned is a review nobody
   re-read;
7. never add the private file or publisher source to an overlay or archive.
