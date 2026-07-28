# FinishTanTwoTheta proof obligations

This file is the compiler-agent work order.  The Lean sources contain the full
intended theorem statements and local proof plans.  The obligations below are
ordered by mathematical dependency, not by filename.

## A. Elaboration and API adaptation

Before changing any theorem statement:

1. make the nested package resolve the parent `aiq_dkps_formalization` package;
2. adapt names for current Mathlib/Tau Ceti APIs;
3. compile `Sequence.WeakSubmajorization`;
4. preserve the zero-based approximation-number convention;
5. do not replace canonical `ContinuousLinearMap.approximationNumber` with a
   finite-dimensional singular-value definition.

Pure elaboration failures should not be “fixed” by weakening a statement.

## B. Infinite symmetric-ideal foundations

### B1. Minimal completion is fully symmetric

Prove:

```text
x weakly submajorized by y
and y is in the finite-sequence closure
implies x is in the finite-sequence closure.
```

This is the central theorem in
`StandardSymmetricIdeal.isMinimalSequence_of_weaklySubmajorized`.

A valid route is the classical Calderon/T-transform truncation argument for the
minimal symmetric sequence space associated with a symmetric norming function.
Do not make this a field of the ideal structure.

### B2. Generic generated ideal laws

For both maximal and minimal completion modes, prove:

- triangle inequality from Ky Fan submajorization of `A+B`;
- scalar homogeneity;
- operator-norm domination from normalization;
- the two-sided ideal inequality from approximation-number composition bounds;
- adjoint invariance.

This constructs standard ideals from arbitrary symmetric norming functions, so
Lorentz, Orlicz, Marcinkiewicz, and similar families need only provide their
finite norming function.

### B3. Concrete standard families

Complete:

- maximal operator norm (already available in the parent tree);
- minimal operator norm = compact operators;
- maximal fixed Ky Fan norms;
- minimal fixed Ky Fan norms = compact operators with that norm;
- Schatten `p` for every real `p >= 1`;
- trace class (`p=1`);
- Hilbert--Schmidt (`p=2`).

For finite `p`, prove minimal = maximal by tail convergence of a summable
nonnegative series.

## C. Approximate leading singular families

Prove the universal selection theorem without compactness.

For each finite `k` and `epsilon > 0`:

- select exact eigenvectors for isolated approximation numbers above the
  essential norm;
- select orthogonal approximate eigenvectors at the essential-norm plateau;
- omit values at most `epsilon`;
- transfer right vectors through the canonical polar partial isometry;
- obtain both `Xx ~= s y` and `X* y ~= s x` uniformly.

The theorem must remain valid for nonseparable ambient Hilbert spaces because
only finitely many vectors are selected.

Do not replace this theorem with compactness or finite-rank assumptions.

## D. Double-angle functional calculus

For `||X|| < 1`, prove:

```text
a_n(2 X (I-X*X)^-1) = 2 a_n(X) / (1-a_n(X)^2).
```

Recommended route:

1. use the general polar partial isometry `X = U |X|`;
2. rewrite the tangent operator as `U f(|X|)` with
   `f(t)=2t/(1-t^2)` and `f(0)=0`;
3. prove a min-max functional-calculus theorem for positive operators and
   continuous increasing `f` on the spectral interval;
4. handle the essential-spectrum plateau directly through the min-max
   characterization, not by assuming singular-vector attainment;
5. show the support partial isometry preserves the relevant approximation
   numbers.

This theorem belongs in final Tau Ceti.

## E. Stable Riccati estimate and epsilon limit

### E1. Stable pair estimate

Expand the existing exact equation-(7.6) proof with residuals

```text
Xx - s y,
X* y - s x.
```

On `0 <= s <= r < 1`, bound every residual term uniformly by operator norms and
`1/(1-r^2)`.  Retain the matched coefficient
`-Re <x, B01 y>` so it can be summed by the orthonormal Ky Fan theorem.

### E2. Finite-family sum

Sum the stable pair estimate over the selected family and apply the existing
dimension-free orthonormal Ky Fan bound.  Error must be `O(k epsilon)` with a
constant independent of the selected vectors.

### E3. Remove epsilon

Control omitted transformed approximation numbers using

```text
2t/(1-t^2) <= 2t/(1-r^2),  0 <= t <= r.
```

The final inequality has an additive `C k epsilon`; let `epsilon -> 0` by an
Archimedean lemma.  Do not retain an epsilon, compactness assumption, finite
carrier, or cosine denominator.

## F. Standard-ideal endpoint

Scale the canonical tangent operator by `d/2`.  The sharp Ky Fan theorem gives
weak submajorization by `B01`.  Apply the generic Fan-dominance theorem to get:

```text
Tan2(X) belongs to every standard ideal containing B01,
d * N(Tan2(X)) <= 2 * N(B01).
```

Provide explicit Schatten, trace, Hilbert--Schmidt, operator-norm, compact
operator-norm, and fixed-Ky-Fan corollaries.

## G. Unbounded source wrapper

The sharp theorem is specifically for an off-diagonal perturbation.  Preserve
the explicit hypothesis

```text
IsOffDiagonal U E
```

where `U` is the unperturbed spectral subspace.

Use current unbounded spectral restrictions and quarter-acute graph machinery
to produce the bounded Riccati block.  Identify its coupling with
`P_U E | U^perp`, apply the ideal composition law, and invoke the sharp graph
theorem.  Finally prove unitary equivalence between the graph-coordinate
`Tan2(X)` and the existing source-facing ambient tangent block.

The final source theorem must have no factor

```text
1 / (1 - 2 * directedGap^2).
```

## Nonnegotiable statement guards

Do not:

- assume Fan dominance as a field of a broadly named ideal;
- assume compactness in the full Ky Fan theorem;
- require a finite-dimensional active carrier;
- replace approximate singular families with nonexistent exact families;
- omit the off-diagonal hypothesis from the sharp unbounded theorem;
- use the totalized bounded-below `polarIsometry` as a general polar
  decomposition;
- weaken the conclusion by reintroducing the cosine denominator;
- add axioms.

A theorem statement may be changed only after producing a mathematical
counterexample or identifying a precise mismatch with a current parent API.
