# Source-general sine-theta completion audit

Baseline: `7463ca25c64a46c48411a2769b47714889974a97`.

## Mathematical status

The source-faithful Davis--Kahan 1970 Section 6 sine-theta development is
mathematically complete in the intended ambient scope.  It is not merely a
finite-dimensional or bounded specialization.

The production source surface contains:

- literal directed cosine, sine, and angle objects, with singular-value bridges
  to the paper representatives and to the full projection difference;
- the source class of coherent normalized unitarily invariant norms;
- Lemmas 6.1 and 6.2, including the converse direction of Lemma 6.1;
- the original isometric sine theorem and generalized Theorem 6.1 for a bounded
  below trial map, unequal coordinate spaces, and every source norm;
- Proposition 6.1 under both directional gap assumptions;
- Theorem 6.2 under arbitrary pairwise spectral distance in the square norm,
  together with the printed finite-rank operator-norm consequence;
- complex and real forms;
- common-domain and graph-core forms from the unbounded appendix;
- planar equality, constant-one optimality, the one-gap counterexample, and
  explicit equality models of arbitrary finite multiplicity;
- the restored source-facing square-energy and square-norm Sylvester estimates.

The theorem is broader than the source where harmless: it does not need a
separability assumption.  The paper-facing aliases retain the source gap,
residual, lower-frame, representative, and norm quantifiers.

## What is not missing

No additional mathematical lemma is required to obtain the exact Section 6
Theorems 6.1 or 6.2 in the intended closed-operator scope.  In particular, the
following open or experimental APIs are not dependencies of the source theorem:

- the scalar-generic historical `IsometricSinThetaProblem.result` route;
- the generic legacy spectral-cutoff and bounded-truncation API;
- the abandoned joint-PVM proof sketch for the Hilbert--Schmidt Sylvester bound;
- the remaining direct-rotation, tangent, double-angle, continuation, and
  Section 8 obligations from the full Part III manuscript.

Those are alternate abstractions or later paper families, not holes in the
completed Section 6 theorem.

## Remaining acceptance hardening

The exact audit currently selects 43 principal endpoints.  The public source
facade contains additional proved theorem aliases that are not separately
printed by that audit.  The most source-significant omission is
`lemma6_1_converse`; other examples include the finite-Ky-Fan forms, the
source-norm law aliases, and common-domain finite-rank corollaries.

This is an audit-coverage and documentation task, not missing mathematics.  A
future hardening pass should either add all theorem-valued source aliases to the
exact audit or generate the audit list from a maintained declaration manifest.

## Stable acceptance baseline

At this baseline all of the following have been reported green:

- ordinary production build;
- `DavisKahan.All`;
- the explicit nondefault `DavisKahan.Experimental` target;
- aggregate generation in check-only mode;
- the 43-endpoint exact source audit;
- the five structural checks;
- the independent column-expansion proof;
- the finite-multiplicity equality model.
