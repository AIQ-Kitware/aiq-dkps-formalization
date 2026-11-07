# Lean import boundaries and upstream mathematics: curriculum audit bridge

This **standalone additive overlay** enriches the proposed course's roadmap-obligation
review with two different kinds of evidence:

1. A module-import graph derived from the `source-imports.json` / `pins.json` pair
   exported by the existing `collect_lean_snapshot.py`. Each target's module closure
   is computed over local DKPS/ForTauCeti modules only.
2. **Pointers** into the existing provenance authority
   `dev/tauceti/dkps-upstream-contribution-census.md`, limited to its table of
   PRs explicitly marked as originating from DKPS. These are evidence references,
   not a competing declaration-by-declaration provenance inventory.

## Artifacts

- `import-lineage-review.md`: short interpretation and deficiencies.
- `import-lineage-bridge.json`: detailed snapshot counts, targeted closure import
  boundaries, explicit PR-to-roadmap-ID evidence, and topological ordering of
  the **local Lean module** import graph.
- `audit_source_import_lineage.py`: Python standard-library reproducibility tool.
- `lean-proof-dependency-export-contract.md`: specification for the next Lean
  extraction step, distinguishing theorem-term references from module imports.

## Regenerate with live inputs

```bash
cd ~/code/aiq-dkps-formalization
python3 visualizations/draft-stages/prerequisites/roadmap-audit/lean-lineage/audit_source_import_lineage.py \
  --source-imports /tmp/dkps-lean-dependency-evidence/source-imports.json \
  --pins /tmp/dkps-lean-dependency-evidence/pins.json \
  --repo . \
  --out /tmp/dkps-lean-lineage-refresh
```

The supplied captured inputs were generated against DKPS HEAD
`8fb4ea3d2122cb442f7043e5de5002cbc966ba81` with TauCeti revision
`a67a65006c07449dcb2ebe1a3a8b6bf6e0b909f8`. The source archive used
for local donor inspection is a separate `fb96c39f0091` snapshot. These are
**different snapshots**, and their mathematical content must not be silently
assumed identical.

## Meaning and limitations

- Imports are a **conservative structural boundary**, not proof dependencies.
- The source's existing census distinguishes adapted ports, roadmap-associated
  contributions, independently developed counterparts, Bors status, and proofs
  previously derived from Spectra. Preserve those distinctions.
- Do not classify a current `TauCeti.*` module as mathematics originating
  independently of DKPS merely because its DKPS donor was retired.
- Do not infer DKPS proof descent for a PR merely because its roadmap ID appears
  in the project's planning material.
- A course topic being mapped to an upstream theorem is **not** evidence that
  the learner can prove it. Pedagogical coverage must be audited separately.
