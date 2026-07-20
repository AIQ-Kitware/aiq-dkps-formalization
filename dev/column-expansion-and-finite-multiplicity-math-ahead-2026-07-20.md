# Column expansion and finite-multiplicity continuation

Base commit: `b9c546cc9eb0f36068960ac25d07adf1a0994c01`

## Non-negotiable baseline

The literal source sine-theta audit is genuinely clean at this base.  Preserve
all 38 existing audited endpoints and their exact dependency set:

- `propext`
- `Classical.choice`
- `Quot.sound`

Do not modify the accepted Proposition 6.1 proof, Theorem 6.2 chain, universe
polymorphism, Frobenius bridge, or strengthened whole-report audit parser merely
to make the new files elaborate.

## New compiler targets

### 1. Alternative Hilbert--Schmidt column expansion

File:

`DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean`

Purpose:

- preserve a genuinely different proof of column summability;
- obtain summability from pairwise orthogonality plus the norm bound for every
  finite column partial sum;
- derive the partial-sum bound from right tensoring by the finite-span
  orthogonal projection;
- use basis reconstruction only after summability has been established.

The canonical vendored proof remains authoritative and must not be replaced.
This alternative may use the accepted low-level tensor dictionary, but it must
not prove its main result by invoking the canonical `hasSum_columnTensor`,
`norm_sq_eq_tsum_column_norm_sq`, `summable_column_norm_sq`, or
`toOperator_ofOperator` theorems.

Likely elaboration seams:

- the conjugate right tensor action and the direction of
  `toOperator_mapL_right`;
- simplification of the finite-span projection formula;
- the exact protected `HasSum.mapL` API;
- coercions between a Hilbert basis and its orthonormal basis.

Compile first:

```bash
lake env lean \
  DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean
```

Then require:

```bash
lake build DavisKahan.All
```

### 2. Genuine finite-multiplicity extremizer

File:

`DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean`

This is not another scalar-homogeneity theorem.  It defines an explicit family
on

`WithLp 2 (EuclideanSpace 𝕜 (Fin m) × EuclideanSpace 𝕜 (Fin m))`

with:

- first-block exact inclusion;
- second-block complementary inclusion;
- simultaneous coordinate-plane rotation;
- ambient operator `0 ⊕ delta I`;
- zero trial operator;
- residual exactly `delta sin(theta)` times the second inclusion;
- directed sine exactly `sin(theta)` times the second inclusion.

The second inclusion is decomposed into `m` norm-one rank-one coordinate
columns.  This must prove membership in every source-defined ideal, rather than
assuming a generic finite-dimensional membership axiom.  For nonzero
`sin(theta)`, the sine block must be injective on the `m`-dimensional domain,
so the declaration really witnesses multiplicity `m`.

Likely elaboration seams:

- the exact `WithLp` norm and coordinate simplification lemmas;
- proving the adjoint of `blockInl` is `WithLp.fstL`;
- the operator norm of `EuclideanSpace.proj`;
- the argument order of `LinearMap.rank_comp_le_left`;
- simplification of the standard-basis reconstruction sum;
- finite-sum notation in `PaperUnitaryInvariantNorm.mem_finset_sum`;
- scalar cancellation in the injectivity theorem.

Do not weaken the final theorem by adding a membership hypothesis.  Repair the
finite-rank membership proof instead.

Compile second:

```bash
lake env lean \
  DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean
```

## Candidate acceptance sequence

After both files are green, run:

```bash
lake build DavisKahan.All
python3 scripts/audit_full_paper_sine_theta.py
```

The audit has five new finite-multiplicity reports.  Update declaration paths
only if the source-layer reorganization moves them.  Do not reduce the number
of reports, permit subset dependency checks, or tolerate non-report output.

The structural check is expected to remain red before the remaining source
facades and their clean implementation dependencies are moved out of
`Experimental`.  Do not weaken it to obtain an intermediate green result.

## Reorganization continuation

Only after the candidate sequence above passes:

1. Resume `dev/flawless-sine-theta-reorganization-overnight-plan-2026-07-20.md`.
2. Perform the two foundational extractions recorded in
   `dev/sine-theta-move-manifest-2026-07-20.md`.
3. Move the remaining exact-paper implementation into
   `DavisKahan/Sources/DavisKahan1970/SineTheta/` using `git mv` and preserve
   declaration names initially.
4. Ensure `DavisKahan.All` reaches every claimed proof, including alternatives.
5. Keep `Experimental` as the transitive admission quarantine only.
6. Keep `ForMathlib` Mathlib-only.  It must never import `Vendor/Spectra`.
7. For a Lean Pool export, use
   `LeanPool/DavisKahan/Vendor/Spectra/` and retain exact Spectra provenance in
   headers and the vendor README.  General Spectra-derived results that have
   been rewritten to a Mathlib-only closure move to `ForMathlib` with their
   provenance retained in comments.
8. Run `python3 scripts/check_library_structure.py` and make every check green
   without exemptions.

## Completion claim

The sine-theta section may be described as FLAWLESS only when:

- the strengthened source audit is clean;
- the finite-multiplicity model compiles and is audited;
- `lake build DavisKahan.All` is green;
- every non-Experimental production module is reachable from that target;
- no non-Experimental module depends on the admission closure.
