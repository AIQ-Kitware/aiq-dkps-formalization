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


## Do not promote recent discussion into manuscript prominence

Do not let the most recent review, correction, user comment, or agent discussion
set the emphasis of a manuscript revision merely because it is fresh in context.
Use new information to revise the paper's understanding, then write at the level
of the paper's stable research question and evidence.

In particular:

- do not move a newly discussed episode into the title, abstract, contribution
  list, or conclusion unless it is independently central to the paper;
- do not summarize the conversation that led to a revision when the manuscript
  only needs the resulting scientific point;
- do not enumerate review rounds, transient classifications, or recent repair
  details in the abstract unless the count or chronology is itself a reported
  result;
- keep concrete episodes in the body when they provide evidence for a broader
  claim, rather than making every episode a headline claim;
- after incorporating new evidence, reread the abstract and conclusion from the
  perspective of a reader who has not seen the development conversation and
  remove details whose prominence depends on that conversation.
