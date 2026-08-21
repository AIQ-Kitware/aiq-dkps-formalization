# Banned words, phrases, and LLM writing habits

These rules apply to manuscript prose, captions, headings, and appendix prose. This file is the negative companion to [STYLE_GUIDE.md](STYLE_GUIDE.md): it records vocabulary and constructions to remove.

## Banned rhetorical words

Do not use these words as rhetorical emphasis:

- `matters`
- `silently`
- `quietly`
- `unusually`

Do not replace them with a synonym that performs the same empty emphasis. State the concrete consequence.


## Banned phrases

- "The X is worth" stating / saying out loud / clarifying / etc..
- "X bites" 

## Banned contrast template

Do not use the formula **"X is not Y; it is Z"** or routine variants such as:

- "This is X, not Y."
- "The point is not X but Y."
- "Our contribution is not X; rather, it is Y."
- "This should not be understood as X, but as Y."

Mathematical negation is fine when it is mathematically required. The prohibition is on the rhetorical template.

## Banned slogan style

Do not use:

- taglines or dramatic one-line morals;
- punchy oppositions written for cadence;
- metaphorical names for ordinary methodology when literal prose is available;
- self-congratulatory adjectives about scale, rigor, novelty, or instrumentation;
- sentences announcing what the paper "really" shows instead of stating the result.

## Banned note-to-self prose

Do not leave editorial or agent-facing instructions in the manuscript, including formulations such as:

- "should be repeated before submission";
- "needs a final refresh";
- "final reporting should";
- "the appendix should eventually";
- explanations of why the authors are being cautious about wording.

State the current evidence and claim.

## Banned vague methodology language

Do not use abstract phrases when the concrete source can be named. Examples include:

- "the missingness mechanism is structured";
- "coordination-tooling provenance";
- unexplained interaction categories;
- vague references to "presentation choices";
- generic claims that a distinction "matters" without giving its consequence.

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

## Word to use sparingly

Reduce uses of `presentation`. Retain it only when it names a substantive mathematical representation or another technical object. Remove sentences whose only purpose is to explain reader-facing layout choices.
