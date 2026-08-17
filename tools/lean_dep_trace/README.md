# Lean dependency tracing tools

These tools were built to generate presentation-oriented dependency graphs for
the DKPS formalization, especially the path into
`DkpsQuench2026.QueryEfficiency.infiniteFixedSubset`.

## Current status

The **Python lexical tracer is usable**, but pass the current project roots
explicitly.  Its historical defaults still include the retired `ForMathlib`
name, so relying on defaults would omit current reusable-library declarations.

```bash
python -m pip install networkx
python tools/lean_dep_trace/trace_deps.py . \
  --include ForTauCeti DavisKahan YuWangSamworth2015 \
            Acharyya2024 Acharyya2025 DkpsQuench2026 Helm2025 \
  --outdir build/lean-dep-trace \
  --target DkpsQuench2026.QueryEfficiency.infiniteFixedSubset
```

The generated DOT/GraphML and milestone files are exploratory visualization
artifacts, not proof-closure evidence.  For theorem/source status use the
repository censuses and gates.

## Elaborated exporter is historical until refreshed

`ExportDeclDeps.lean` predates the `ForMathlib` retirement and still imports that
removed root.  Therefore the old command

```text
lake env lean --run tools/lean_dep_trace/ExportDeclDeps.lean
```

is **not a current workflow**.  Update the helper's import/root list and validate
it on the pinned Lean toolchain before re-enabling elaborated dependency export.
Do not present its historical README instructions as a supported exact mode.

## Editing the slide-level dependency story

`tools/lean_dep_trace/milestones.toml` controls the coarse presentation map.
Each `[[milestone]]` supplies an id, label, subtitle, display color, and matching
patterns; each `[[edge]]` declares a slide-level relation.  The generated
`milestone_evidence.md` records whether matched declarations have a path in the
focused lexical graph.

This layer is intentionally editorial: it helps decide what belongs on a slide.
It should not be used to infer whether a theorem is built, admission-free, or a
source-faithful endpoint.
