# `docs/` — project-facing planning and reference

Scope, roadmap, and reference material for the AIQ DKPS formalization.
Engineering memory and live agent coordination live in
[`../dev/`](../dev/README.md); the governing policy lives in
[`../AGENTS.md`](../AGENTS.md).

## What is actually current

The repository has run a **dual-track policy since 2026-07-24**: Tau Ceti
extraction is the primary track, Davis--Kahan source fidelity is maintenance.

**The Mathlib track is closed and is not resuming.** Several documents here
predate that decision and were written against Mathlib; each carries a banner
saying so. Do not read them as evidence that a Mathlib PR is planned — but do
not discount their analysis either. **Tau Ceti holds a comparable bar** (accepted
roadmap target, one topic per PR, green build, standard axiom allowlist), so
statement clarity, API shape, proof locality, naming, and reviewer-objection
analysis all carry over. What does *not* carry over is any claim about what
Mathlib does or does not already contain; re-check against `external/TauCeti`
and `vendor/Spectra`.

| Read | For |
|---|---|
| [`planning/tauceti-adaptation-and-spectra-extraction.md`](planning/tauceti-adaptation-and-spectra-extraction.md) | The active roadmap: sequence, acceptance gates, A1–A3 submission split |
| [`planning/davis-kahan-full-paper-goal.md`](planning/davis-kahan-full-paper-goal.md) | The maintained scope ledger and completion standard for the 1970 paper |
| [`planning/opus-next-paper-completion-campaign.md`](planning/opus-next-paper-completion-campaign.md) | The current campaign brief |
| [`planning/davis-kahan-general-sin-theta-roadmap.md`](planning/davis-kahan-general-sin-theta-roadmap.md) | Required reading before changing the single-angle API |
| [`../dev/LANES.md`](../dev/LANES.md) | Who holds what right now — claim before editing |

## Directory map

```text
docs/
  planning/     # Scope, roadmap, candidate dossiers, PR decisions
    historical/ # Completed-phase artifacts, kept for provenance (see its README)
  challenge/    # How the comparator challenge package works
  migrations/   # Library reorganizations and their crosswalks
  ots/          # OpenTimestamps proofs for release manifests
```

### `planning/`

**Roadmap and scope** — `tauceti-adaptation-and-spectra-extraction.md`,
`davis-kahan-full-paper-goal.md`, `davis-kahan-general-sin-theta-roadmap.md`,
`opus-next-paper-completion-campaign.md`.

**Candidate dossiers and PR shaping** — `mathlib-candidates.md` (the dossiers),
`upstream-readiness-audit.md` (per-candidate reviewer objections, readiness
ratings, and the PR sequencing), `pr-decisions.md`,
`spectral-pr-decomposition.md`, `rectangular-singular-values-and-frames.md`.
These were written for the Mathlib track. The mathematics and the reviewer
analysis remain valid against Tau Ceti's comparable bar; only the *destination*
changed.

**Trackers** — `remaining-work.md` (R-numbered inventory; its header phase is
superseded, see its banner), `acharyya-plan.md` (formalization-phase map, that
phase is complete) and `acharyya-graveyard.md` (approaches tried and abandoned,
so nobody re-visits them).

### `historical/`

An intentional archive, not clutter. Its [`README.md`](planning/historical/README.md)
gives each file's disposition. Left intact during the 2026-07-29 documentation
purge because it is already labelled and because
`prose/distilled_literature/source_manifest.json` — validated by
`scripts/check_distilled_literature_index.py` — names a file inside it.

## Where a document goes

- Paper scope, completion standard, roadmap → `planning/`.
- Comparator/challenge mechanics → `challenge/`.
- A library reorganization and its module crosswalk → `migrations/`.
- Migration execution detail, ledgers, per-declaration decisions →
  `../dev/tauceti/`, not here.
- A lane claim or working status → a row in `../dev/LANES.md`, not a new file.

When a phase ends, **update the document in place with a banner** saying what
superseded it, or move it to `historical/` with an entry in that README. Do not
leave a finished plan looking active — that is precisely the failure the
2026-07-29 purge was cleaning up, and it had already caused two reversed lanes.
Files removed in that purge live in [`../dev/topurge/`](../dev/topurge/MANIFEST.md).
The review pass ran and **jon decided on 2026-07-30 that the directory stays** —
treat it as a labelled archive, not as pending work.
