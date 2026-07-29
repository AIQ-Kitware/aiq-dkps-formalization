# Full formalization frontier scaffold overlay

This overlay adds an isolated experimental signature graph for the remaining
Davis--Kahan 1970 formalization. It does not import the frontier into
`DavisKahan.All`.

## Scope

- Section 3 constructive crossed-defect direct rotations, operator-level Halmos
  classification, spectral multiplicity bridge, compact classification, and
  fixed-angle maximality.
- Infinite-dimensional statements for the valid Section 4 extremal results.
  The refuted Proposition 4.4 is intentionally absent.
- The exact compatible-norm form of Theorem 5.1.
- The full ideal-scope Theorem 6.3 and Lemma 6.3.
- Exact source-level Section 7 ideal statements.
- A circle-only Riesz projection API and the remaining Section 8 bridges.
- A semantic free-beam model, the third-eigenvalue estimate, and constructors
  replacing the conditional Section 9 certificates.
- A 72-node machine-readable dependency graph and checker.

## First compiler pass

Do not try to discharge proofs initially. The first milestone is:

```bash
lake env lean DavisKahan/Experimental/Frontier/Core.lean
lake env lean DavisKahan/Experimental/Frontier/Section3.lean
lake env lean DavisKahan/Experimental/Frontier/Section4.lean
lake env lean DavisKahan/Experimental/Frontier/Lemma63.lean
lake env lean DavisKahan/Experimental/Frontier/RieszCircle.lean
lake env lean DavisKahan/Experimental/Frontier/Section8.lean
lake env lean DavisKahan/Experimental/Frontier/Section9Analytic.lean
lake env lean DavisKahan/Experimental/Frontier/RemainingSourceSurface.lean
lake env lean DavisKahan/Experimental/Frontier/All.lean
```

Repair names, coercions, universe constraints, and statement formulations while
preserving the intended mathematics. Do not weaken source endpoints merely to
obtain elaboration. When a signature is semantically wrong, correct it and
record the divergence in this note or the frontier README.

After the aggregate elaborates, run:

```bash
python3 scripts/check_davis_kahan_frontier.py --write-report
```

The expected initial state is full statement coverage with most new nodes
reported as admitted. As proofs land, the recursively grounded counts should
increase without modifying the manifest topology unless a genuine missing
lemma is discovered.

## Suggested proof order

1. `lemma6_3_approximationNumber_leakage`.
2. Generic Halmos cosine/sine restrictions.
3. Proposition 3.2 constructive existence and parameterization.
4. Operator-level two-projection classification.
5. Circle scalar Cauchy formula and operator-valued integral.
6. Circle Riesz equals the Spectra projection.
7. Section 8 continuation witness and half-gap bridges.
8. Free-beam closed operator, self-adjointness, and `alpha_3 > 500`.
9. Section 9 certificate constructors.
10. Spectral multiplicity and compact classification.

## Important semantic checks

- Equality of crossed-intersection dimensions must not be replaced silently by
  finite rank.
- Spectral multiplicity must include continuous-spectrum measure-class data;
  point-spectrum multiplicities alone are not Theorem 3.1.
- The first Ky Fan norm in Lemma 6.3 is the operator norm, not the nuclear norm.
- Section 8 should use circles and existing Spectra projections, not recreate a
  nonexistent general contour API.
- Section 9 certificate values must be defined from actual angle operators and
  spectral data.
