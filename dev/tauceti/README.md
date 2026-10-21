# `dev/tauceti/` — TauCeti integration and provenance

The active architecture and dependency rules live in
[`../../AGENTS.md`](../../AGENTS.md) and
[`../../ForTauCeti/README.md`](../../ForTauCeti/README.md).
**`ForTauCeti` is a shrinking donor for results not yet available upstream**;
accepted TauCeti/Mathlib implementations are consumed directly. This directory
contains historical evidence and a small number of current handoffs, not a
second permanent library implementation.

## Start here

1. [**DKPS-to-TauCeti contribution and mathematical-lineage census**](dkps-upstream-contribution-census.md)
   — initial, incomplete PR/result provenance ledger. Separates direct
   adaptation, broader campaign activity, independent overlapping results,
   and future Hilbert-space-operator-theory provenance work. Do not equate a
   shared roadmap item, a Bors title, or a closed PR with proof descent.
2. [**Upstream-consumption and reducing-restriction handoff**](upstream_consumption_reducing_2026-10-21.md)
   — the current canonical restriction implementation, consumer migration,
   obsolete bridge cleanup, and compile checkpoints.
3. [**Canonical-spectrum migration proof lineage**](proof-lineage/2026-10-20-canonical-spectrum-migration.md)
   — exact original proof anchors, source scope, and the boundary between
   canonical and legacy spectral/resolvent concepts.
4. [`extraction-manifest.json`](extraction-manifest.json),
   [`roadmap-topic-map.md`](roadmap-topic-map.md), and
   [`spectra-provenance-map.md`](spectra-provenance-map.md)
   — maintained donor inventory, roadmap topic grouping, and layered Spectra
   ancestry. A topic grouping is not a statement of accepted upstream status.
5. [`submission-ladder.md`](submission-ladder.md)
   — regenerate/check with its maintained derivation tool rather than trusting
   hard-coded counts in prose.

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
