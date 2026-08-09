# Vendored Lean proof references

This directory preserves selected upstream Lean proofs that are unusually close
to spectral and finite-frame infrastructure used by the DKPS formalization.

The files are **reference snapshots, not project imports**. They are kept outside
the production dependency graph so provenance remains visible, obsolete APIs
cannot silently enter the build, and adaptations can be compared against an
immutable source copy.

## Policy

- Copy a source only after verifying an explicit compatible license.
- Record repository, commit, source path, blob SHA, license, authors, and whether
  the local copy is exact or excerpted in `manifest.toml`.
- Exact snapshots retain their upstream header unchanged.
- Excerpts carry a prominent local notice and preserve the copied proof text.
- Sources with no visible license are documented in
  `dev/external-lean-references.md` but are not copied here.
- An adapted theorem keeps a source note in its production file header and
  commit history; vendoring does not transfer authorship.

## Current snapshots

- `jbarrcfl-mathlib4/TopSingularValue.excerpt.lean` — operator norm equals the
  top singular value.
- `lean-stat-learning-theory/SingularSystemGram.excerpt.lean` — right and left
  singular vectors, zero/nonzero cases, orthonormality, and reconstruction.
- `lean-stat-learning-theory/EYMOperatorNorm.excerpt.lean` — operator-norm
  lower and attained halves of Eckart--Young--Mirsky.
- `lean-stat-learning-theory/DavisKahanSpectralProjection.excerpt.lean` —
  centered operator-norm spectral-projection Davis--Kahan proof.
- `drifting-identifiability/FiniteFrameBound.excerpt.lean` — qualitative linear
  independence to a positive finite lower-frame constant.

See `manifest.toml` for immutable source identifiers, `NOTICE.md` for attribution,
and `SHA256SUMS` for local snapshot integrity.
