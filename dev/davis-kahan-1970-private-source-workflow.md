# Davis--Kahan 1970 private-source workflow

The maintained modernized transcription and any publisher PDF are local
comparison sources. They are not part of the distributable repository.

The public source surrogate is:

`prose/distilled_literature/DavisKahan1970_part_III.tex`

It should contain independently worded mathematical statements, formulas,
source numbering, proof architecture, scope qualifications, and formalization
status. It should not reproduce the source prose continuously.

The maintained completeness/status authorities are:

- `dev/davis-kahan-1970-full-source-census.json` — authoritative structured
  source ledger;
- `dev/davis-kahan-1970-full-source-census.md` — generated human view;
- `dev/davis-kahan-1970-frontier.json` — maintained proof-frontier graph;
- `dev/davis-kahan-1970-frontier-status.md` — generated frontier view.

Dated completion plans and handoffs are historical records, not proof queues.
If they disagree with the census/frontier or the build, the checked artifacts
win.

A local audit may compare the private transcription against the structured
ledger, but repository checks must not require the private file. This keeps a
fresh public checkout reproducible.

When the private transcription changes:

1. inspect all section and numbered-result anchors;
2. update the public distillation in independent wording;
3. update the JSON census/frontier data as required;
4. regenerate their Markdown views;
5. run `scripts/check_davis_kahan_1970_source_census.py` and
   `scripts/check_davis_kahan_frontier.py`;
6. never add the private file to an overlay or archive.
