# Vendored Spectra upstream snapshot

`vendor/Spectra/` is an exact source snapshot of the public upstream repository:

- Repository: `https://github.com/adambornemann-glitch/Spectra.git`
- Commit: `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
- Commit subject: `added more lean options to the lake file, fixed warnings.`
- Snapshot format: `git archive` of the commit above

The snapshot directory must remain byte-for-byte equivalent to the tracked
files at that upstream commit. `external/Spectra/` is retained as a read-only
reference submodule pinned to the same commit; it is not used by the build. Project-specific compatibility changes must not
be edited into `vendor/Spectra/` as an undocumented fork. They belong in a
separate patch recorded outside the snapshot and applied by a dedicated script.

## Update procedure

1. Remove any applied compatibility patch.
2. Fetch and inspect the desired commit in `external/Spectra/`.
3. Replace `vendor/Spectra/` with `git archive <new-upstream-commit>`.
4. Regenerate `vendor/Spectra.SHA256SUMS` from the clean snapshot.
5. Run `python3 scripts/verify_vendored_spectra.py`.
6. Update the `external/Spectra` gitlink to the same commit and run
   `python3 scripts/verify_spectra_reference.py`.
7. Rebase and regenerate the DKPS compatibility patch in a separate commit.

This commit intentionally records only the clean upstream snapshot. A following
commit may add the compatibility patch required by the DKPS Lean/Mathlib pin.
