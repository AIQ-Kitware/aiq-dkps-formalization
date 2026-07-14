# Vendored Lean proof references

This directory preserves selected upstream Lean proofs that are unusually close to the
spectral and finite-frame infrastructure needed by the DKPS formalization.

The files here are reference snapshots, not project imports. They are intentionally kept
outside the `ForMathlib` dependency graph so that:

1. provenance is never obscured by later adaptation;
2. upstream code can be compared against our re-authored Mathlib-facing version;
3. license and source-commit information remain attached to every copied proof; and
4. obsolete APIs in a snapshot cannot silently enter the production build.

## Policy

- A source is copied only when an explicit compatible license was verified.
- Every copied file or excerpt has a manifest entry with repository, commit, source path,
  blob SHA, license, authors, and whether the local copy is exact or excerpted.
- Exact snapshots retain their upstream header unchanged.
- Excerpts carry a prominent local notice and preserve the copied proof text unchanged.
- Sources with no visible license are documented in `dev/external-lean-references.md` but
  are not copied here.
- No proof becomes ours merely because it is vendored. Any adapted theorem must keep a
  source note in its file header and commit history.

## Current snapshots

  operator-graph infrastructure.
  complete and closed range.
  inverses for injective closed-range maps between Banach spaces.
  inversion tools.
- `jbarrcfl-mathlib4/TopSingularValue.excerpt.lean`: the operator norm equals the top
  singular value.
- `lean-stat-learning-theory/SingularSystemGram.excerpt.lean`: right and left singular
  vectors, zero/nonzero cases, orthonormality, and reconstruction.
- `lean-stat-learning-theory/EYMOperatorNorm.excerpt.lean`: the operator-norm lower and
  attained halves of Eckart-Young-Mirsky.
- `lean-stat-learning-theory/DavisKahanSpectralProjection.excerpt.lean`: the centered
  operator-norm spectral-projection Davis--Kahan proof.
- `drifting-identifiability/FiniteFrameBound.excerpt.lean`: qualitative linear
  independence to a positive finite lower-frame constant.

See `manifest.toml` for immutable source identifiers and `SHA256SUMS` for local snapshot integrity.
