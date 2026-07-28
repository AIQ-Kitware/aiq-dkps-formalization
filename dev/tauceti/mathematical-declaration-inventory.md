# Mathematical declaration inventory for Tau Ceti integration

Baseline: `7463ca25c64a46c48411a2769b47714889974a97`.

This inventory separates generally reusable mathematics from source-specific
wrappers.  It is selective: it names the main API-bearing declarations and
modules, not every helper lemma.

## Tier 1 -- broadly reusable functional analysis

### Rectangular approximation numbers

Current home: `DavisKahan/OperatorIdeal/ApproximationNumbers/`.

Main contributions:

- `approximationSingularValue`: best rank-bounded approximation for rectangular
  continuous linear maps;
- monotonicity, absolute homogeneity, perturbation inequalities, operator-norm
  control, adjoint invariance, and two-sided ideal inequalities;
- `approximationSingularValue_eq_singularValues`: finite-dimensional agreement
  with Mathlib singular values;
- `rectangularOperatorModulus` and
  `sameApproximationSingularValues_rectangularOperatorModulus`;
- orthogonal block sums and lower bounds for the approximation numbers of each
  summand;
- real/complexification compatibility and independent source/target universes.

Tau Ceti value: a general operator-ideal foundation independent of
Davis--Kahan.

### Rectangular symmetric ideal families

Current home:
`DavisKahan/OperatorIdeal/UnitarilyInvariant/RectangularFamily.lean`.

Main contributions:

- a coherent family of ideal membership predicates and gauges over rectangular
  Hilbert-space maps;
- left and right ideal membership;
- multiplicative gauge estimates and contraction corollaries.

Tau Ceti value: the abstraction used to state one theorem uniformly for
operator, Schatten, Ky Fan, and other symmetric norms.

### Orthogonal block and column reconstruction

Current homes:

- `DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean`;
- `DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean`;
- supporting orthogonal-series modules under `ForMathlib/Analysis/InnerProductSpace/`.

Main contributions:

- continuous `L²` orthogonal block sums;
- recovery of each summand by contractive coordinate maps;
- approximation-number monotonicity under block inclusion;
- independent orthogonal-series proof of Hilbert--Schmidt column expansion.

Tau Ceti value: reusable Hilbert-space series and block-operator infrastructure.

### Closed operators and bounded extensions

Current home: `DavisKahan/SpectralTheory/ClosedOperator/`.

Main contributions:

- `ClosedOperator`, its canonical `LinearPMap` view, dense-domain and closed-graph
  facts;
- `SameDomain`, `MapsDomainTo`, and `BoundedExtension`;
- embedding bounded maps as full-domain closed operators;
- bounded realizations of spectrally bounded restrictions;
- complexification of real closed operators.

Tau Ceti value: reusable domain-aware operator theory, but **not** as the
existing bundle. The representation decision is closed: restate the reusable
content over Mathlib `LinearPMap`, compatible with Tau Ceti's semigroup
generators, and demote the bundle to a temporary Davis--Kahan adapter. This is
active U1 implementation work; semigroup coordination affects later theorem
placement, not the foundational representation choice.

Migration status: **ACTIVE / CLAIMED 2026-07-27.** The exact execution order and
exit gates are in `dev/tauceti/u1-linearpmap-migration.md`.

### Reducing restrictions

Current home: `DavisKahan/SpectralTheory/ReducingSubspace/`.

Main contributions:

- invariant and reducing subspaces for domain-aware operators (now canonical
  `TauCeti.LinearPMap` predicates, with historical bundle names as facades);
- preservation of domains by orthogonal projections;
- restricted domains, restricted actions, projection back into the restricted
  domain, and the resulting raw partial map (all now canonical
  `TauCeti.LinearPMap` declarations);
- self-adjointness and spectral localization of restrictions.

Tau Ceti value: general spectral-subspace machinery for unbounded operators.

## Tier 2 -- general spectral and operator-equation theory

### Closed Sylvester equations

Current homes: `DavisKahan/Sylvester/ClosedSylvesterEquation.lean` and
`DavisKahan/Sylvester/Unbounded/`.

Main contributions:

- `ClosedSylvesterEquation`, including domain transport and pointwise equation;
- additive, negative, subtraction, and scalar closure;
- `HasBoundedEverywhereInverse` for closed operators;
- ordered, interval/exterior, and all-gap solution estimates;
- real unbounded variants and homogeneous uniqueness.

### Pairwise spectral separation

Current homes:

- `DavisKahan/Sylvester/PairwiseSpectrumGap.lean`;
- `DavisKahan/Sylvester/PairwiseHomogeneousUniqueness.lean`;
- `DavisKahan/Sources/DavisKahan1970/Sylvester/HilbertSchmidtPairwise.lean`.

Main contributions:

- canonical `LinearPMap.GenuinePairwiseSpectrumGap`, symmetry, monotonicity,
  and disjointness; the bundle-shaped `GenuinePairwiseSpectrumGap` is now a
  source-compatibility facade over it;
- raw-partial-map homogeneous uniqueness under separated spectra; the three
  historical bundle signatures delegate to those proofs;
- Hilbert--Schmidt Sylvester estimates at arbitrary pairwise spectral distance,
  including real descent.
- source-facing square-energy, complex norm, and real norm declarations restored
  in `Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean`, all derived from
  the completed defect-first pairwise-gap engine.

Migration status: **raw `LinearPMap` core landed 2026-07-28.** This family stays
downstream because its spectrum and separated-intertwiner dependencies are from
Spectra.  Seven source/audit consumers still use the bundle-shaped predicate;
their mechanical representation migration is the deletion condition for that
facade.

### Finite-dimensional Sylvester multipliers

Current home: `DavisKahan/FiniteDimensional/Sylvester/`.

Main contributions:

- ordered and interval/exterior estimates for arbitrary rectangular
  unitarily invariant norms;
- spectral-distance estimates over real and complex fields;
- reciprocal Fourier/orbit interpolation and Ky Fan domination machinery;
- explicit separation between the sharp complex constant and the real
  obstruction at the naive Fourier certificate.

Tau Ceti value: substantial reusable finite-dimensional matrix/operator theory,
though the internal Fourier certificate API should be reviewed for placement
and minimal public exposure.

## Tier 3 -- subspace geometry and perturbation theory

### Operator angles

Current home: `DavisKahan/Geometry/Angle/`.

Main contributions:

- complex and real directed sine and cosine operators;
- positivity, self-adjointness, contraction bounds, and norm-gap identities;
- operator-level Pythagoras and commutation;
- full sine and projection-difference compatibility;
- arcsine/cosine formulations of the directed angle.

### Frame and trial-map factorization

Current homes: `DavisKahan/SinTheta/FrameFactorization*.lean` and finite
`Residual/TrialMap.lean`.

Main contributions:

- lower-frame control for non-isometric trial maps;
- factorization through a normalized isometric representative;
- residual and complementary-block Sylvester identities.

### Sine-theta theory

Current homes: `DavisKahan/SinTheta/` and
`DavisKahan/Sources/DavisKahan1970/SineTheta/`.

Main contributions:

- bounded and closed unbounded theorems;
- interval/exterior and pairwise-gap routes;
- arbitrary symmetric-ideal gauges;
- real and complex forms;
- common-domain and graph-core variants;
- natural-input and reducing-subspace wrappers.

### Double-angle, tangent, graph, and Riccati theory

Current homes:

- `DavisKahan/DoubleAngle/`, `TanTheta/`, and `TanTwoTheta/`;
- `DavisKahan/Riccati/`;
- the proved extraction queue documented separately.

Main contributions:

- reflection-defect and off-diagonal identities;
- bounded and unbounded `sin 2 Theta` and `tan 2 Theta` estimates;
- pole-free vector tangent estimates;
- graph-reduction/Riccati transport and unbounded existence results.

These are reusable but more specialized than the Tier 1 foundations.

## Tier 4 -- finite source package

Current home: `DavisKahan/Sources/DavisKahan1970/PartIII.lean`.

The stable finite package contains:

- direct-rotation mapping and projection intertwining;
- ordered and interval Sylvester bounds in arbitrary rectangular UI norms;
- generalized and ordinary `sin Theta` results;
- equal-rank and strict-lower-rank Ritz-residual `tan Theta` results;
- `sin 2 Theta` in UI norms;
- operator-norm `tan 2 Theta` with the acute-branch conclusion;
- sharp projector-difference companions.

See `finite-dimensional-part-iii-audit.md` for exact exclusions.

## Tier 5 -- literal Davis--Kahan source correspondence

Current homes:

- `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean`;
- `DavisKahan/Sources/DavisKahan1970/SineTheta/`;
- `dev/davis-kahan-1970-source-correspondence-matrix.md`.

This layer owns paper numbering, literal hypotheses, equality models, the
printed counterexample, and explicit claims/nonclaims.  It is valuable as an
acceptance suite but should not determine the names or placement of general
Tau Ceti infrastructure.
