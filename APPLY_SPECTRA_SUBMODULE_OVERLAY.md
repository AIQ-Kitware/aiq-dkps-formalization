# Apply the Spectra collaboration overlay

From the DKPS repository root:

```bash
python3 scripts/apply_spectra_submodule_overlay.py
scripts/bootstrap_spectra_submodule.sh --create-fork
```

The first command updates repository guidance and removes any redundant Mathlib
snapshot files from the earlier vendor experiment. The second command creates or
detects the authenticated user's fork, creates the actual Git submodule, and
stages `.gitmodules` plus the gitlink. It configures remotes manually rather than
passing the unsupported `--remote=false` form to `gh repo fork`.

The Lake dependency is intentionally not enabled yet because the audited Spectra
checkout is one Lean release behind the DKPS workspace.  Port the compatibility
branch first.  Then run:

```bash
python3 scripts/enable_spectra_lake_dependency.py
scripts/spectra_import_smoke.sh
```

To back out only the Lake path dependency while retaining the collaboration
checkout:

```bash
python3 scripts/disable_spectra_lake_dependency.py
```
