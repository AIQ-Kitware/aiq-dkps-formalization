# External development checkouts

This directory is reserved for Git submodules used during active upstream
collaboration.  External source trees are not copied or edited as ordinary DKPS
files.

## Spectra

`external/Spectra` is created by:

```bash
scripts/bootstrap_spectra_submodule.sh --create-fork
```

The committed submodule URL remains the public upstream repository.  The local
checkout receives:

- `upstream`: the public Spectra repository;
- `fork`: the contributor fork used for pull-request branches;
- a named compatibility branch rather than detached `HEAD`.

The submodule is not automatically a Lake dependency.  Enable it only after its
Lean and Mathlib pins agree with the root workspace:

```bash
python3 scripts/enable_spectra_lake_dependency.py
scripts/spectra_import_smoke.sh
```

See `dev/spectra-integration-survey-2026-07-14.md` for the audited capability map
and ownership boundary.
