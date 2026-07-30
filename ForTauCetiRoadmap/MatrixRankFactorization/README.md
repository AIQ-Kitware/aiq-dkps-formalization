# Roadmap: rank factorization and positive-semidefinite factorization of matrices

**Topic T21 of the candidate design.** Two modules, no prerequisites — the
smallest independent topic in the library, and the one closest to something
Mathlib would take as-is.

## The two theorems

Over a field, every matrix factors through its rank, and only through it:

```lean
theorem rank_le_iff_exists_eq_mul {r : ℕ} {M : Matrix m n 𝕜} :
    M.rank ≤ r ↔ ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R
```

Over `RCLike`, a positive-semidefinite matrix is a Gram matrix of the right
dimension, and only of that dimension:

```lean
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} {B : Matrix n n 𝕜} :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) n 𝕜, B = Aᴴ * A
```

The second is the **multidimensional-scaling embedding step** stated exactly: a
PSD matrix of rank at most `d` *is* the Gram matrix of `n` points in `𝕜^d`. Both
are iffs, and that is the point — the easy direction (`rank (L * R) ≤ r`) is what
makes them usable as characterisations rather than constructions.

## Why it is not already in Mathlib

Mathlib has the rank API (`Matrix.rank`, `rank_mul_le`, and the PSD spectral
theory) but no **factorization** statement: nothing produces the `L`, `R` or `A`.
The content added here is the assembly — the eigenvalue-square-root construction
for the PSD case, and the through-`Fin r` normalisation that makes the inner
dimension a natural number a caller can choose.

## Pinned conventions

### The inner dimension is `Fin r`, not a subtype

`exists_eq_mul_rank` gives inner dimension exactly `M.rank`;
`exists_eq_mul_of_rank_le` relaxes it to any `r ≥ M.rank`. Both index by `Fin r`.
A caller who wants "at most `d` rows" gets it without transporting along a
cardinality equivalence, which is the whole reason the `≤` form exists beside the
exact one.

### Declarations live in `TauCeti.Matrix`

These four theorems are pinned as *data* in `comparator/pending-rank-factorization.json`
and `comparator/pending-rank-psd-realization.json`, and named in the paired
`Challenge/MathlibPending/**/Leaderboard.lean` files. They read `TauCeti.Matrix.*`
today; they read `ForMathlib.Matrix.*` before 2026-07-29. Anyone renaming here
must run `scripts/check_declaration_name_drift.py` and `lake build Challenge` —
`Challenge` is outside `defaultTargets`, so a green default build proves nothing
about those pins.

## Existing foundations

Mathlib supplies `Matrix.rank` with `rank_mul_le` and the row/column space API,
`Matrix.PosSemidef` with `IsHermitian.spectral_theorem` and its eigenvalues, and
`RCLike`.

A sorry-free staged implementation exists under `ForTauCeti/LinearAlgebra/Matrix/`
(`scripts/check_tauceti_roadmap_topics.py --topic T21`). It still requires Tau
Ceti review and migration.

## What remains to land

- **Uniqueness up to the obvious action.** A rank factorization is unique up to
  `L ↦ L * g`, `R ↦ g⁻¹ * R` for `g ∈ GL r`, and the PSD factor up to a left
  unitary. Neither is stated, and both are what a reviewer asks after seeing an
  existence iff.
- **Theorem-level acceptance examples**, in Tau Ceti's shape.

## Ordering and PR slices

One PR. Two modules, one of which (`PosDef`) imports the other; together they are
404 lines and the second theorem is the first plus a spectral square root.

## Provenance and coordination

Both modules were authored in place in this repository (Davis–Kahan/DKPS
formalization, Kitware, Inc.), and both lived in `ForMathlib` until 2026-07-29,
when lane FM-RETIRE retired that library into `ForTauCeti`. The move renamed the
namespace `ForMathlib.Matrix → TauCeti.Matrix` and repointed the comparator pins
and leaderboards with it; the reasoning, including why a parallel version of the
same lane had decided otherwise, is recorded in `ForTauCeti/Topology/Berge.lean`.

T21 is rung **T** of `dev/tauceti/submission-ladder.md`. Nothing in the library
depends on it — it is a leaf, which is another reason it is a cheap first
submission.

Written 2026-07-30 by `jon (yardrat)` under lane ROADMAP-WRITE, claimed together
with T22 because the two share that FM-RETIRE provenance.
