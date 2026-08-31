# General Davis--Kahan sine-theta roadmap

## Target

The canonical single-angle target is the source-faithful Davis--Kahan 1970
Section 6 theorem for closed, possibly unbounded, self-adjoint operators, with
explicit domains, a bounded residual, the paper spectral-gap alternatives, and
the full source quantifier over coherent unitarily invariant norms.

Bounded and finite-dimensional forms are specializations or independent
alternative proofs.  They are not substitutes for this target.

## Status at `7463ca25c64a`

The target is complete for complex and real Hilbert spaces.

The completed source surface includes:

1. literal source angle objects and complete singular-value identifications;
2. the source unitarily invariant norm family and Ky Fan dominance passage;
3. Lemmas 6.1 and 6.2;
4. the original isometric sine theorem;
5. generalized Theorem 6.1 with a lower-frame trial map;
6. Proposition 6.1 with both directional gaps;
7. pairwise-gap square-norm Theorem 6.2 and its finite-rank bound-norm corollary;
8. common-domain and graph-core appendix forms;
9. real descent by complexification;
10. sharpness, the one-gap counterexample, and arbitrary finite-multiplicity
    equality models.

The production theorem uses the maintained interval/exterior and pairwise-gap
engines. It does not depend on the unresolved generic legacy cutoff API.

## Exact source mapping

The authoritative human map is
`dev/davis-kahan-1970-source-correspondence-matrix.md`.  The executable surface
is `DavisKahan/Sources/DavisKahan1970/SineThetaSourceInventory.lean`, and the selected
trusted-dependency audit is
`DavisKahan/Sources/DavisKahan1970/Audits/SineThetaSourceInventory.lean`.

The result is harmlessly more general than the paper in omitting separability.
It preserves the source hypotheses that matter: domains, self-adjointness,
residual identity, lower-frame constant, gap orientation or pairwise distance,
representative singular values, and norm scope.

## Remaining work around this theorem

No mathematical work remains to prove the exact Section 6 headline theorem.
The remaining tasks are:

- expand the exact audit beyond its 43 selected endpoints, especially to include
  the converse direction of Lemma 6.1;
- keep historical correspondence documents from contradicting the authoritative
  matrix;
- improve API placement and naming for external library integration;
- preserve independent bounded, finite, and orthogonal-series proof routes.

## Work outside this roadmap

The following belong to the full-paper roadmap rather than to completion of the
single-angle theorem:

- direct rotation and its extremal properties;
- general tangent and double-angle theorem families;
- graph and Riccati theory beyond the single-angle prerequisites;
- continuation, canonical spectral selection, and Section 8 spectral repulsion;
- remaining unbounded extensions outside the Section 6 appendix;
- full extraction of proved declarations from mixed Experimental files.
