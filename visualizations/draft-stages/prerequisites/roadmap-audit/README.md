# OperatorTheory roadmap coverage audit (proposed curriculum branch)

Start at [`audit.md`](audit.md), then inspect [`obligations.json`](obligations.json)
for **all 899** separately enumerated roadmap obligations, with IDs, titles,
branch and source line. The six Toeplitz prose stages are recorded separately.
The table records *candidate homes*, never invented transcripts, proofs, or
Lean declarations. Source titles from the roadmap are preserved.

The supplemental [`proposed-proof-nodes.json`](proposed-proof-nodes.json) adds
25 mathematical developments to the prior 159-node curriculum DAG, plus seven
proof-reconstruction endpoints. Its additional edges have been checked for
cycles against that baseline: 184 combined vertices admit a topological order.
[`proposed-topological-order.md`](proposed-topological-order.md) lists one such
order; do not automatically renumber the curriculum from it.

[`lean-source-anchors.json`](lean-source-anchors.json) records a few real local
source names and lines without pretending they are current upstream aliases.
[`lean-evidence-request.md`](lean-evidence-request.md) explains the requested
compiler-level export and what it would establish. The optional
[`collect_lean_snapshot.py`](collect_lean_snapshot.py) records pins and
**source-level imports only**, not proof dependencies.

Revalidate with:

```bash
python3 visualizations/draft-stages/prerequisites/roadmap-audit/check_roadmap_audit.py
```

The audit is deliberately additive and does not overwrite `outline.md`, the
original `lesson-dag.json`, any generated TTS lecture, or any Lean source.
