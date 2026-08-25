## Banned repository-development vocabulary in the main text

Do not use repository-internal development labels as scientific terminology in the main body when direct mathematical prose is available. This includes:

- `source-faithful`;
- `project-local`;
- `inventory` when it refers to internal bookkeeping;
- `dependency snapshot`;
- `machine-readable correspondence`;
- `positive formal-source claim`;
- `census` when discussing the scientific result rather than the appendix audit method;
- `canonical declaration` or `canonical Lean surface` without a mathematical uniqueness statement supporting "canonical".

These terms may appear in appendices when they identify reproduction machinery precisely.

## Banned external-auditor voice for our own work

Do not write as though repository notes were discovered by an outside observer. Avoid formulations such as:

- "the repository documents ancestry in Spectra";
- "we found a note saying the proof was adapted";
- "the data records that we used..." when the manuscript can state directly what we used.

State the ancestry, adaptation, workflow, or methodological choice as an authorial claim and cite the source.

## Lean terminology restrictions

Do not:

- call displayed Lean code a `listing` or `surface`;
- call a Lean declaration `canonical` without a mathematical reason;
- discuss glyph substitutions or TeX rendering accommodations;
- repeat implementation identifiers in prose when a mathematical description suffices;
- explain generic Lean syntax around each theorem after the appendix reader guide has been cited.

## Resource-accounting restrictions

Do not:

- place modeled USD, CO2e, or kWh estimates in the abstract as though they were direct measurements;
- show incomplete observed telemetry without `lower bound` in the relevant table header and caption;
- put observed lower bounds and project-total extrapolations in an unlabeled shared column;
- describe extrapolations as confidence intervals unless a statistical model actually supports that interpretation;
- use CO2e in the current manuscript unless the authors explicitly decide to restore it.

## Citation and appendix restrictions

Do not:

- use a hand-written `thebibliography` block in `paper.tex`;
- leave a vague sentence such as "the appendix gives..." when an explicit section reference can be used;
- put census construction, exact source registries, file paths, or declaration-level provenance tables in the main body;
- place appendices before the references.

