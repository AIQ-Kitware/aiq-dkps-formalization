# Lean evidence request for a concrete theorem graph

The present mathematical DAG is a **teaching hypothesis**. The strongest complementary
artifact is a **declaration-level proof-term dependency export** at the exact repo pins.
I cannot obtain that from the source archive alone: it does not contain a `.lake`
build tree or the compiled upstream TauCeti environment.

## Highest-value export

For the actual final statements in `DavisKahan.All`, plus the major local/theorem
endpoints identified in the manuscript, export a JSONL table with:

- declaration name, `theorem`/`def`/`axiom` kind, and full type;
- **direct constants in its elaborated proof/definition term**, distinct from constants
  in its *statement*;
- owning module and origin (`DavisKahan`, `ForTauCeti`, pinned `TauCeti`, `Mathlib`);
- exact git SHA for the DKPS checkout, TauCeti pin and Mathlib pin;
- explicit status when a theorem body is not accessible (e.g. public-interface
  imports exported as axioms or erased proof bodies).

For each top-level theorem, take the transitive closure across `DavisKahan`,
`ForTauCeti` and `TauCeti`; stop at `Mathlib` but retain those frontier constants
as named external mathematical prerequisites. Keep the statement dependencies
separate from proof dependencies; avoid mistaking compiler implementation
artifacts for teaching obligations. A proof-term graph will be **more concrete
about actual implementation** but still needs mathematical review (one large
automation call can hide many elementary logical steps, and some imported
support is only an implementation detail).

## A useful first run on the local project

```bash
cd ~/code/aiq-dkps-formalization
lake build DavisKahan.All
python3 visualizations/draft-stages/prerequisites/roadmap-audit/collect_lean_snapshot.py \
  --out /tmp/dkps-lean-dependency-evidence
```

The included collector **does not pretend to extract theorem-level dependencies**.
It records repository pins and direct imports with their file locations, checks
where the target source modules are, and provides a stable manifest to accompany
the next declaration-level export. It never edits Lean files, runs a build, or
prints theorem axioms. It only scans relevant source-module imports (not Mathlib).

The follow-on extractor should be written against **the exact pinned Lean
`v4.36.0-rc2` API**, tested as an explicit opt-in development target; it
should inspect the elaborated `ConstantInfo` proof terms, not source-token guesses.
The current snapshot cannot verify such a Lean implementation, so an untested
one is intentionally not supplied as if working.

If you run the two commands above and share the generated directory along
with this audit, we will have reproducible provenance for the next extraction
pass. The real next high-value result remains the compiled declaration graph.
