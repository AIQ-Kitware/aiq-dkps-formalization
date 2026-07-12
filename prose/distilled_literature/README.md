# Distilled literature for the DKPS formalization

This directory is the source registry and future home of source-order mathematical reconstructions for the DKPS, response-embedding, Perfect Quench, classical MDS, Gram-rigidity, and Davis--Kahan theorem families developed in this repository.

`source_manifest.json` is canonical. `source_index.md` and `distilled_papers_index.tex` are generated views.

## Inclusion rule

Include a work when at least one of the following holds:

1. a paper-facing Lean namespace formalizes one of its named definitions or results;
2. a direct DKPS paper inherits a definition or theorem family from it;
3. a `ForMathlib` module implements or actively scaffolds its theorem family;
4. it is the primary historical source displaced in the current repository by a modern textbook citation;
5. it is a modern comparison source needed to audit constants, hypotheses, finite-versus-infinite-dimensional scope, or theorem naming.

Do not include empirical application citations merely because they occur in a paper bibliography. General results already delegated entirely to Mathlib, such as routine measure theory or elementary concentration tools, belong here only if this repository develops a substantive new theorem layer around them.

## Reconstruction standard

A completed distilled note should be a standalone LaTeX document that records:

- the exact source file, version, edition, or stable bibliographic record;
- the exact section, theorem, lemma, and equation anchors in scope;
- the source's definitions and hypotheses before any modernization;
- the proof in source order, preserving the source's actual reduction strategy;
- every implicit regularity, rank, measurability, gap, orientation, or dimension condition used by the argument;
- any correction, stronger substitute proof, or modern imported lemma, clearly separated from the source proof;
- the matching Lean declarations and discrepancies between paper and formal theorem;
- unresolved source issues and any supplementary references used to repair them.

A transcription is normally evidence rather than a reconstruction. A narrow exception is allowed for a short paper whose exact source-order transcription already contains the complete mathematical argument, provided a maintained formalization-versus-literature ledger supplies the modernization, hidden-hypothesis audit, and explicit Lean theorem map. The Quench paper currently uses this exception. A broad “core arguments” note is useful, but it is not complete until it has precise source anchors and an explicit Lean theorem map.

## Citation discipline

The primary source must remain visibly responsible for its own proof route. A later book, survey, or cleaner proof may clarify an omission, but it must not be silently attributed to the historical paper. Conversely, theorem names such as “Weyl,” “von Neumann,” or “Procrustes” should not be sourced only to a modern textbook when a specific primary paper is central to the formalized result.

Entries marked `needs_verification` in the manifest must be bibliographically checked before a source-faithful note is declared complete.

## Current starting point

The repository already contains:

- transcriptions of the 2024 consistency paper, the 2025 concentration paper, and the 2026 Quench paper; the Quench transcription is intentionally retained as the source-order asset because its short proof is reconstructed and audited in `papers/DKPS-formalized-vs-literature.tex`;
- source prose and TeX for the 2025 inference paper;
- broad core-argument notes for Davis (1963), Davis--Kahan Part III, Horn--Johnson Gram theory, and Yu--Wang--Samworth;
- broad formalized-versus-literature comparison documents under `papers/`.

It did not have a canonical source inventory tying these assets and the mathematical infrastructure to one paper-level roadmap. The initial manifest fills that gap and explicitly records missing primary sources discovered by the audit.

The first completed source-order reconstructions are:

- `Davis1963_rotation_of_eigenvectors.tex`, covering Sections I--V and every numbered theorem/equation in the supplied transcription;
- `YuWangSamworth2015_statistical_davis_kahan.tex`, covering the mixed-gap baseline, population-gap theorem, sharpness examples, rank-one corollary, rectangular extension, and complete appendix proofs.

Both notes are transformative mathematical reconstructions. They record local transcription hashes but do not redistribute the supplied transcriptions.

## Workflow

Regenerate the human-readable indexes after editing the manifest:

```bash
python scripts/render_distilled_literature_index.py
```

Validate the schema, evidence paths, asset paths, and generated views:

```bash
python scripts/check_distilled_literature_index.py
```

Build the standalone TeX index from this directory with:

```bash
pdflatex -interaction=nonstopmode -halt-on-error distilled_papers_index.tex
pdflatex -interaction=nonstopmode -halt-on-error distilled_papers_index.tex
```
