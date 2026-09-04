# Semantic-auditing workshop paper

Four-page workshop draft:

**Semantic Auditing for LLM-Assisted Formalization: Lessons from a Davis--Kahan Case Study**

The paper is intentionally modest and beginner-oriented. It reports practical
lessons from one evolving formalization effort, compares those lessons with
recent semantic-alignment systems, and presents the local dashboard as one
implementation that emerged during the project. Detailed Davis--Kahan and
Yu--Wang--Samworth mathematics remain in `../formalization_draft2/` for the
longer formalization paper.

## Build

```bash
make -C papers/formalization_process_4page
```

The default target builds both:

- `paper.pdf`: the four-page workshop draft (references follow the main text),
- `related_work_semantic_alignment.pdf`: the longer author-reference memo on
  semantic alignment and adjacent autoformalization work.

To build them independently:

```bash
make -C papers/formalization_process_4page paper
make -C papers/formalization_process_4page related-work
```

The workshop paper uses `draft_neurips_2026.sty`, an explicit draft-only
approximation of the 2026 NeurIPS workshop text block. Use the official workshop
style for submission; see `notes/SUBMISSION.md`.

Regenerate the Git-history evidence from the pinned repository snapshot with:

```bash
make -C papers/formalization_process_4page evidence
```

The generated CSV gives every accepted-to-nonaccepted semantic-review transition
used for the retrospective count.

## Related work

`related_work_condensed.tex` is Section 2 of the submission. It is organized as
a practical map for readers: statement alignment, selecting what humans need to
inspect, paper-facing review, large-corpus browsing/evaluation, and long-horizon
review/maintenance.

`related_work_semantic_alignment.tex` is a standalone literature memo for the
authors. It should remain much more detailed than the submission and should be
refreshed before claims about the surrounding tool landscape are revised.

The closest system-level comparisons currently include EconCSLib, Lean Atlas /
Lean Compass, ATLAS / AutoformBot, ShadowBench / SA-Pass, LeanMarathon,
FormaTheoria, and LeanArchitect. The paper presents these as resources for
readers rather than as systems that our local dashboard is intended to replace.

## Paper boundary

The four-page paper is an experience report and practical guide. It does not
claim to introduce semantic alignment, adversarial semantic review, provenance,
or review dashboards. The local dashboard is described because it records how
our own requirements accumulated and because its clause-level source context,
Lean evidence, and drift checks provide a concrete comparison point.

## Draft status

The author-provided workflow figure remains Figure 1. A dashboard screenshot may
be useful for a later version, but the current page budget prioritizes the
practical related-work map and the retrospective review episodes.

Reproduction details for the retrospective count live in `notes/EVIDENCE.md`
rather than in the manuscript.
