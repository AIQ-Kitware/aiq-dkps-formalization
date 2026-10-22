# `dev/tauceti/` — TauCeti integration and provenance

The active architecture and dependency rules live in
[`../../AGENTS.md`](../../AGENTS.md) and
[`../../ForTauCeti/README.md`](../../ForTauCeti/README.md).
**`ForTauCeti` is a shrinking donor for results not yet available upstream**;
accepted TauCeti/Mathlib implementations are consumed directly. This directory
contains historical evidence and a small number of current handoffs, not a
second permanent library implementation.

## Start here

1. [**Current upstream-consumption review and next work (2026-10-22)**](upstream-consumption-review-2026-10-22.md)
   — reviewed upstream-consumption changes, the compiled SSP-D01 eigenframe
   retirement, the one-way corresponding-eigenblock comparison, and remaining
   scope-sensitive or unmerged boundaries. This is the current *action queue*.
2. [**DKPS-to-TauCeti contribution and mathematical-lineage census**](dkps-upstream-contribution-census.md)
   — initial, incomplete PR/result provenance ledger. Separates direct
   adaptation, broader campaign activity, independent overlapping results,
   and future Hilbert-space-operator-theory provenance work. Do not equate a
   shared roadmap item, a Bors title, or a closed PR with proof descent.
3. [**Historical reducing-restriction handoff (2026-10-21)**](upstream_consumption_reducing_2026-10-21.md)
   — checkpoint evidence from an earlier migration. Its old "next slices"
   are superseded by the current review; much of that work has since landed.
4. [**Canonical-spectrum migration proof lineage**](proof-lineage/2026-10-20-canonical-spectrum-migration.md)
   — exact original proof anchors, source scope, and the boundary between
   canonical and legacy spectral/resolvent concepts.
5. [`extraction-manifest.json`](extraction-manifest.json),
   [`roadmap-topic-map.md`](roadmap-topic-map.md), and
   [`spectra-provenance-map.md`](spectra-provenance-map.md)
   — maintained donor inventory, roadmap topic grouping, and layered Spectra
   ancestry. A topic grouping is not a statement of accepted upstream status.
6. [`submission-ladder.md`](submission-ladder.md)
   — regenerate/check with its maintained derivation tool rather than trusting
   hard-coded counts in prose.

The [overnight instruction sheet](overnight-accepted-upstream-consumption-2026-10-21.md)
records the completed October 21--22 campaign and is **not** a live todo list;
the review above supersedes it as a new starting point.

The former `canonical-port-completion.md` pointer was stale and is not a
current entry point. Do not reconstruct an obsolete completion gate from old
campaign or review notes.

## Keeping the census honest

For an accepted PR record its final TauCeti declaration and integration commit,
its donor declaration and historical proof commit, the actual mathematical
relationship, any earlier Spectra ancestry, and the donor implementation
removed here. PR bodies are starting evidence, not the complete proof-lineage
audit. Preserve independent contributors' work and distinguish a theorem used
as a dependency from a proof that was actually adapted from this repository.

The companion `tauceti-dkps-campaign` checkout is a **historical source**, not
a live status oracle. Its first-wave `manifest.json` and
`roadmap_port_index.json`, and its October 19 `port_wave.json`, can seed an
audit. Refresh individual PR and upstream-main evidence before updating
integration status; do not invent an automated gate or a new polling tool.
