# Rectangular singular values, singular systems, and finite frames

Status: R1 (rectangular adjoint invariance), R2 (intrinsic singular system), the
finite-frame core of R4, and R5 (add-one centered scatter) are **fully proved** and
imported by `ForMathlib.lean`; the fully grounded Quench spectral track consumes R1/R4/R5
through `DkpsQuench2026/Spectral/GramSpectrum.lean`.  R3 and the rest of R4 are
future work.

This plan records the general mathematical layer that should replace application-specific
Gram arguments in fully grounded Quench. The target is not the smallest local lemma. It is a
coherent Mathlib-quality contribution built on the current rectangular
`LinearMap.singularValues` API.

## Why this layer

fully grounded Quench repeatedly moves between three equivalent views of finite data:

1. a synthesis or analysis map;
2. its domain Gram operator `T.adjoint.comp T`;
3. its codomain Gram operator `T.comp T.adjoint`.

Current Mathlib defines rectangular singular values through the first Gram operator, but it
does not yet expose enough of the bridge to the second Gram operator, a full singular
system, or finite-frame inequalities. Consequently downstream proofs repeatedly reconstruct
standard SVD and frame facts in application notation.

The intended dependency order is:

```
RectangularSingularValues
        |
        v
SingularSystem
        |
        +----------------------+
        v                      v
FiniteFrame              Eckart-Young / norms
        |
        v
fully grounded Quench adapters

CenteredScatter (separate branch, depends only on positive/rank-one operators)
```

## File status

- `ForMathlib/Analysis/InnerProductSpace/RectangularSingularValues.lean` — **proved**.
  Contains the nonzero eigenspace equivalence between `A†A` and `AA†` (with equal
  finrank and `HasEigenvalue` transport), the antitone fiber-counting lemma
  `antitone_eq_of_card_filter_eq`, the sorted-spectrum bridge
  `eigenvalues_adjointCompSelf_eq_selfCompAdjoint`, zero-padded adjoint invariance
  `LinearMap.singularValues_adjoint`, the left-Gram squared-singular-value identity
  `sq_singularValues_selfCompAdjoint`, and the two-way transfer between quadratic
  floors `α‖x‖² ≤ ‖Ax‖²` and spectral floors of `A†A`/`AA†`.
- `ForMathlib/Analysis/InnerProductSpace/FiniteFrame.lean` — **proved** (core).
  Analysis/synthesis maps, the adjoint identity, frame and Gram operators, positivity,
  the frame quadratic form, and the two-way lower-frame-bound ↔ Gram-spectral-floor
  correspondence.  The originally scaffolded `HasFiniteFrameBounds`/Löwner-interval,
  injectivity-iff-spanning, and antilipschitz existence theorems were dropped from the
  file to keep it fully proved; they remain future R3/R4 work.
- `ForMathlib/Analysis/InnerProductSpace/CenteredScatter.lean` — **proved**.
  Finite means, `appendFin`, the exact add-one identity `centeredScatter_append`
  (coefficient `n/(n+1)` in `𝕜`), positivity, Löwner monotonicity, and the
  quadratic-form version.
- `ForMathlib/Analysis/InnerProductSpace/SingularSystem.lean` — **proved**.
  The right singular basis, total left singular vectors, the singular relation
  `A vᵢ = σᵢ uᵢ` including the zero case, orthonormality on the nonzero subtype,
  the `AA†` eigen-equation for left vectors, the intrinsic reconstruction of `A x`,
  the rank-one operator expansion, and the orthonormal-basis extension of the
  nonzero left family.

## Milestone R1: rectangular adjoint invariance — DONE

Root theorem:

```lean
Module.End.eigenspace (A.adjoint.comp A) mu ≃ₗ[K]
  Module.End.eigenspace (A.comp A.adjoint) mu
```

for `mu ≠ 0`, with forward map `x |-> A x` and inverse
`y |-> mu⁻¹ • A.adjoint y`. This theorem is stronger and more canonical than set equality
of nonzero spectra: it preserves eigenspace dimension directly and is the right bridge to
multiplicity-counted sorted spectra.

Primary sequence theorem:

```lean
A.adjoint.singularValues = A.singularValues
```

This must hold for `A : E -> F` with unequal finite dimensions because Mathlib uses a
zero-padded `Nat`-indexed singular-value sequence.

Preferred proof route:

1. Construct the nonzero eigenspace equivalence explicitly.
2. Derive equality of nonzero eigenspace dimensions and `HasEigenvalue` transport.
3. Use the spectral theorem to convert eigenspace multiplicities into equality of the
   positive sorted eigenvalue lists of `A†A` and `AA†`.
4. Rewrite the support of both singular-value sequences using map rank and
   `finrank_range_adjoint`.
5. Square the nonnegative singular values inside the support and use zero padding outside.

Alternative algebraic route:

1. Move to orthonormal-basis matrices.
2. Apply `Matrix.charpoly_mul_comm'` or `Matrix.charpoly_mul_comm_of_le` to `A` and
   `A.conjTranspose`.
3. Cancel the explicit power of `X` and transfer the positive roots back to sorted
   eigenvalues.

The singular-system route is preferred because it also discharges R2 and gives useful
vectors. The characteristic-polynomial route is an independent cross-check and may produce
smaller spectrum lemmas.

Do not use the square-only polar-unitary proof in
`DavisKahan/Specialized/SingularSubspaceCore.lean` as the final rectangular
argument. Keep it as a corollary or retire it after R1 lands.

## Milestone R2: intrinsic singular system — DONE

Construct:

- `rightSingularBasis A`, the eigenbasis of `A.adjoint.comp A`;
- `leftSingularVector A i = sigma_i^-1 * A v_i`;
- orthonormality on the subtype where `sigma_i != 0`;
- `A v_i = sigma_i u_i`, including the zero case;
- reconstruction of `A x` as the finite singular expansion;
- extension of the nonzero left singular family to an orthonormal basis of the codomain.

Proof strategy:

1. Rewrite inner products of images by adjointness.
2. Replace the Gram action by the eigenbasis equation.
3. Convert the eigenvalue to `sigma_i^2` using `sq_singularValues_fin`.
4. Prove the zero singular-value case through `ker_adjoint_comp_self` or
   `inner_self_eq_zero`.
5. Normalize only on the nonzero subtype; avoid carrying arbitrary inverse side conditions
   through every theorem.
6. Reconstruct by expanding `x` in the right orthonormal basis and applying linearity.
7. Use `Orthonormal.exists_orthonormalBasis_extension` for the codomain basis, rather than
   hand-written index packing.

The source comparison table in `dev/external-lean-references.md` identifies three complete
implementations of most of this route.

## Milestone R3: variational singular-value API

The strongest useful API should include:

- largest singular value equals operator norm;
- smallest domain-indexed singular value equals minimum gain;
- lower gain bound iff a lower bound on the smallest singular value;
- injectivity iff the smallest singular value is positive;
- `A.adjoint.comp A >= alpha^2 * I` iff `alpha * norm x <= norm (A x)`;
- singular-value Courant-Fischer max-min and min-max formulas;
- rank-k projection truncation and operator-norm Eckart-Young-Mirsky.

Much of this exists either locally or in licensed upstream work. Prefer adapting and
consolidating it rather than creating parallel definitions.

## Milestone R4: finite frames — core DONE (items 1–3, 7 below plus the
frame-bound/Gram-floor transfer); the remaining items are future work

For a finite family `v : i -> E`, define:

- analysis map: `x |-> (inner x (v j))_j`;
- synthesis map: `c |-> sum_j c_j * v_j`;
- frame operator: synthesis after analysis;
- Gram operator: analysis after synthesis;
- explicit lower and upper frame bounds.

Required theorems:

1. analysis adjoint equals synthesis;
2. frame and Gram operators are the two adjoint products;
3. frame quadratic form equals the sum of squared coefficients;
4. frame bounds are equivalent to Loewner bounds on the frame operator;
5. a positive lower frame bound is equivalent to injectivity of the analysis map in finite
   dimension;
6. the optimal lower bound is the square of the smallest singular value;
7. frame and Gram operators have the same positive zero-padded spectrum;
8. linearly independent finite families admit a positive lower bound;
9. explicit inverse-matrix and condition-number certificates imply concrete bounds.

For fully grounded Quench, the finite-frame adapter should turn the centered response family into
an analysis or synthesis map and obtain the covariance floor from R4. The paper-specific
normalization factors should remain outside the general file.

## Milestone R5: centered scatter updates — add-one track DONE

Keep the online covariance/scatter algebra in a separate contribution. Proved:

- add-one scatter update (`centeredScatter_append`);
- positive-semidefinite monotonicity (`centeredScatter_le_append`);
- quadratic-form growth (`re_inner_centeredScatter_append`), which yields
  lower-floor preservation through the Gram bridge.

Still open: the two-sample merge identity and the trace update.

This layer uses the positive-operator and rank-one APIs but does not depend on full SVD.

## Reuse decisions

### Vendor and adapt

- Jacob Barr's top-singular-value proof, Apache-2.0.
- Zhang, Lee, and Liu's Courant-Fischer and operator-norm Eckart-Young development,
  Apache-2.0.
- Dronmong's finite-dimensional lower-frame existence proof, MIT.

Selected proof excerpts are under `vendor/lean/` with immutable provenance metadata. The
most direct donor for R1/R2 is now
`vendor/lean/lean-stat-learning-theory/SingularSystemGram.excerpt.lean`.

### Reference and re-derive only

- `rjwalters/lean-genius`: no visible license.
- `andersonwu2000/Asterism`: no visible license.
- `BoltonBailey/BrascampLieb`: no visible license in the surveyed tree.
- `jaumededios/Cantor_Measure_Frames`: no visible license.
- closed GPT-generated matrix-SVD Mathlib PRs: useful proof quarry, but superseded in design
  by the intrinsic linear-map API and subject to their original contribution context.


## Survey conclusion

The extended search found no single upstream-ready implementation of the whole desired API,
but it did find enough verified proof material that this project should adapt rather than
restart:

- current Mathlib supplies the zero-padded singular values, positive operators, adjoints,
  and the `AB`/`BA` characteristic-polynomial identity;
- `lean-stat-learning-theory` supplies the most complete Apache-2.0 singular-system, Gram,
  Courant--Fischer, and operator-norm Eckart--Young proofs;
- `jbarrcfl/mathlib4` supplies an Apache-2.0 top-singular-value proof and an intrinsic SVD
  branch;
- `drifting-identifiability` supplies the MIT-licensed finite lower-frame existence route;
- Asterism, lean-genius, BrascampLieb, and Cantor frames supply reference-only proof maps; and
- closed Mathlib PRs `#31821`/`#31830` are explicit GPT-5.1 proof quarries but not the
  preferred architecture.

The source registry and licensing decisions in `dev/external-lean-references.md` are part of
the contribution setup and must stay synchronized with any later copied or adapted proof.

## Upstream PR decomposition

Recommended sequence:

1. rectangular adjoint singular values and left-Gram eigenvectors;
2. singular vectors and reconstruction;
3. operator norm / minimum gain / singular min-max, coordinated with active upstream work;
4. finite frames and frame-bound equivalences;
5. centered scatter rank-one updates and the two-sample merge identity.

Each PR should be independently useful and avoid DKPS names or hypotheses.
