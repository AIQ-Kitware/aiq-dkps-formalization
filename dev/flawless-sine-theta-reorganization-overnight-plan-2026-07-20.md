# Historical record: sine-theta library reorganization

**Status: completed and superseded.**  This path is retained because the current
structural checker and a few archived notes cite the reorganization that created
its invariants.  It is no longer an execution prompt.

The July plan had three durable goals:

1. production Davis--Kahan modules must be reachable from the supported roots;
2. production modules must not depend on admitted Experimental proofs;
3. source-facing sine-theta endpoints must remain covered by the full-paper
   audit rather than becoming green through an unbuilt wrapper.

Those requirements are now encoded in the repository structure and in
`scripts/check_library_structure.py` / `scripts/audit_full_paper_sine_theta.py`.
Use the scripts, not the old file-move checklist, as the current specification.

The architecture described by the original plan has also moved on:
`ForMathlib` was retired into `ForTauCeti`, Spectra was removed, and the
production source aggregate is under `DavisKahan/Sources/DavisKahan1970/`.
Historical references to those old paths can be recovered from Git history if a
migration detail is needed.

Current Davis--Kahan proof status is owned by the source census and frontier:

```bash
python3 scripts/check_davis_kahan_1970_source_census.py
python3 scripts/check_davis_kahan_frontier.py
python3 scripts/check_library_structure.py
```
