# 082000 - Spectral approximation by cutoffs

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `073000` Borel sets, `074000` integration and L two, `076000` projection-valued measures, `079000` bounded Borel calculus, and `081000` resolvents. **Next:** `083000` densely defined operators and their graphs.

<!-- BEGIN SPOKEN LECTURE -->

# Approximating an operator without losing its spectral geometry

A spectral integral looks like an infinite version of a diagonal matrix. But to turn that analogy into proofs, we need to know exactly which finite approximations are legitimate, and which notion of convergence each approximation provides.

Today we will build two kinds of approximation. First we approximate bounded functions by functions taking only finitely many values. Then we restrict the spectrum to larger and larger bounded intervals. The first construction can converge in operator norm. The second usually converges only strongly, meaning on each fixed vector.

That difference becomes essential as soon as the operator itself is unbounded.

## Finite spectral partitions

Let A be a bounded self-adjoint operator on a complex Hilbert space, and write E of B for its spectral projection on a Borel set B.

Suppose the spectrum has been divided into finitely many disjoint Borel regions. Call them B one through B m. Choose a scalar c j for each region. The simple function s takes the value c j on region B j.

Its operator is a finite sum: c one times E of B one, plus the corresponding terms for the remaining regions.

Why is this construction well behaved? The projections of disjoint regions are orthogonal, and their sum is the identity when the regions cover the spectrum. Any vector x splits into orthogonal pieces, one for each region. The simple-function operator multiplies each piece by just one scalar.

Consequently its squared output length is the sum over j of the squared magnitude of c j times the squared length of E of B j applied to x. The operator norm is therefore no larger than the largest magnitude of the chosen scalars.

We have reduced a spectral integral to finitely many orthogonal components, without assuming that any component is one-dimensional. A spectral projection onto an interval can have infinite-dimensional range.

## Approximating a bounded symbol

Now let f be any bounded Borel function on the spectrum. Choose a small positive tolerance, epsilon.

The values of f lie in a bounded region of the complex plane. Divide that region into finitely many small squares, each of diameter less than epsilon. For each square, take the set of spectral points whose f-values fall in that square. These preimages are Borel sets because f is measurable.

Choose one representative value in each square. This produces a simple function s whose value differs from f by less than epsilon at every spectral point.

The squared-norm formula for simple functions, followed by passage to the functional-calculus limit, shows that f of A minus s of A has operator norm at most epsilon.

This is genuine operator-norm approximation. One finite spectral sum approximates the action of f of A uniformly on every unit vector.

Notice what made the argument work. We partitioned according to the values of f, not necessarily into intervals of the spectral variable. A wildly discontinuous Borel function need not be approximated uniformly by choosing ever smaller ordinary intervals in its input.

For a continuous function on a compact real spectrum, ordinary spectral intervals do suffice: uniform continuity guarantees that its values vary little inside each sufficiently short interval.

## A concrete matrix calculation

Consider a diagonal matrix with eigenvalues minus two, zero, and three. Suppose we want to approximate its absolute-value operator.

Partition the spectrum into the singleton sets containing those three values. Choose the corresponding function values two, zero, and three. The resulting finite spectral sum is exactly the diagonal matrix with entries two, zero, and three.

Now replace the selected values by two point one, zero, and two point nine. The new operator differs from the absolute-value operator by a diagonal matrix whose nonzero entries are plus point one and minus point one. Its operator norm is point one.

The same calculation works when a spectral region has many dimensions. The error bound is controlled by the worst scalar approximation on a region, rather than by counting eigenvectors.

## Bounded functions can converge strongly without converging in norm

Operator-norm approximation is powerful, but it is not the only limit we need.

Let A be multiplication by t on L two of the interval from zero to one. For each positive integer n, let f n be the indicator of the open interval from zero to one over n.

For each fixed t in the interval, f n of t eventually becomes zero. The functions are uniformly bounded by one. Dominated convergence shows that for every fixed square-integrable vector x, the length of f n of A applied to x tends to zero.

So these operators converge strongly to zero.

But every f n of A still has operator norm one. We can choose a unit vector supported entirely inside the small interval where f n equals one. That choice depends on n.

Strong convergence fixes x first and then lets n increase. Operator-norm convergence allows the test vector to change with n. This is why the conclusions differ.

## Expanding spectral bands

We now allow A to be an unbounded self-adjoint operator. The word unbounded means that A is defined only on a specified dense domain, and no uniform constant controls the length of A x by the length of x over that domain.

For each nonnegative radius R, let P R be the spectral projection onto the closed interval from minus R to R.

The projections P R increase as R increases, because their spectral regions are nested. Their ranges are orthogonal spectral subspaces. These are called spectral cutoffs.

Fix any vector x in the Hilbert space, whether or not x lies in the domain of A. The squared length of x minus P R x is the scalar spectral mass of x outside that interval.

As R increases, those outside sets shrink to the empty set. The scalar spectral measure of x has finite total mass, equal to the squared length of x. Continuity of finite measures from above therefore makes the outside mass tend to zero.

We have proved that P R x tends to x for every fixed x. The cutoffs converge strongly to the identity.

We have not proved norm convergence, and in general it is false. Whenever P R is a proper orthogonal projection, the norm of the identity minus P R is one. A unit vector in its nonzero orthogonal complement witnesses that fact.

## Why a bounded band belongs to the operator domain

Here is the first payoff from the cutoff construction.

Take an arbitrary vector x and form y equal to P R x. Its scalar spectral measure is supported in the interval from minus R to R.

The integral of lambda squared against that measure is at most R squared times the squared length of y. In the unbounded spectral theorem, finiteness of that integral is exactly the condition for y to belong to the domain of A.

Therefore every cutoff vector lies in the domain of A, even if the original x does not.

Moreover, the length of A y is at most R times the length of y. A may be unbounded on its full domain, but its restriction to a fixed bounded spectral band is bounded.

The operator that sends x to A applied to P R x is therefore a bounded operator defined on the whole Hilbert space. It has spectral symbol lambda inside the band and zero outside.

This is the correct interpretation of truncating an unbounded operator. We are not claiming that A itself suddenly becomes bounded.

## Commutation and convergence in the graph norm

Because P R comes from the spectral measure of A, it commutes with A wherever applying A makes sense.

More precisely, if x is already in the domain of A, then P R x is in that domain, and A applied to P R x equals P R applied to A x.

We already know P R x tends to x. Apply the strong convergence theorem again, this time to the vector A x. It gives P R A x tending to A x. By commutation, A P R x tends to A x as well.

Thus cutoff vectors approximate every domain vector in both ordinary length and the length of its image under A.

The graph norm combines these two quantities: its square is the squared length of x plus the squared length of A x. We have proved convergence in this graph norm for vectors in the domain.

This is stronger than ordinary strong convergence, and it is the reason bounded spectral cutoffs can safely support proofs involving an unbounded operator.

## A diagonal example showing the domain obstruction

Take the Hilbert space of square-summable sequences. Let A multiply the n-th coordinate by n. Its domain consists of sequences for which the sum of n squared times the squared magnitude of the n-th coordinate is finite.

Consider the sequence whose n-th coordinate is one divided by n. That sequence is square-summable, since the sum of reciprocal squares converges. But it is not in the domain of A: multiplying by n produces a sequence of ones, which is not square-summable.

The radius-N cutoff keeps the first N coordinates and removes all later ones. These cutoff vectors converge in Hilbert-space norm to our original sequence.

Yet the length of A applied to the cutoff vector is the square root of N. It grows without bound. There is no vector A x to which those images could converge.

So strong approximation of x by domain vectors does not by itself imply graph convergence. For graph convergence, x must already belong to the domain.

## What finite rank does and does not mean

One final distinction will matter when we return to singular values.

A finite spectral partition contains finitely many projection terms, but those projections need not have finite rank. On L two of a continuum, a spectral interval ordinarily supports infinitely many independent vectors.

Likewise, an expanding cutoff P R need not be finite rank. Finite partitions, bounded spectral bands, and finite-rank approximations are three different ideas.

There is, however, a useful bridge. If K is compact and P R converges strongly to the identity, then P R K converges to K in operator norm. The reason is that a compact operator sends the unit ball to a set with compact closure. Uniformly bounded projections that converge on every fixed vector converge uniformly on that compact set.

Applying the same reasoning to the adjoint of K shows that K P R converges to K in norm too. Therefore P R K P R converges to K in operator norm.

Without compactness, that conclusion can fail. In particular, taking K equal to the identity would assert norm convergence of P R to the identity, which we have just disproved.

## The bridge to unbounded operator theory

We now have two precise approximation tools. Bounded Borel symbols can be approximated in operator norm by finite spectral sums. For an unbounded self-adjoint operator, bounded spectral cutoffs converge strongly to the identity and approximate domain vectors in graph norm.

The domain condition is not a technical footnote. It determines when spectral multiplication by lambda defines a genuine Hilbert-space vector.


<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let `E` be the projection-valued measure of a self-adjoint operator `A`, possibly unbounded, and write `P_R = E([-R,R])` for `R ≥ 0`. For any `x ∈ H`,

\[
\|x-P_Rx\|^2=\mu_x(\mathbb R\setminus[-R,R])\longrightarrow0.
\]

The bounded truncation `A_R = A P_R = \int_{[-R,R]}\lambda\,dE(\lambda)` is defined on all of `H` and has `\|A_R\|\le R`. Every `P_R x` is in `Dom(A)`; if `x∈Dom(A)`, then `A P_Rx=P_R Ax\to Ax`. In particular, `P_Rx → x` in the graph norm for each domain vector. For a bounded Borel `f`, uniformly approximating its values by finite simple functions gives operator-norm approximation of `f(A)`. None of these assertions makes `P_R` finite rank.

For a compact bounded operator `K`, strong convergence `P_R → I`, the uniform bound `\|P_R\|≤1`, and compactness give `\|P_RK P_R-K\|→0`; this compact-operator extension is a mathematical argument in the lecture rather than an assertion that the source declarations quoted below directly formalize it.

**Lean bridge (verbatim source declaration headers).**

`DavisKahan/SpectralTheory/SpectralCutoff.lean` — `spectraSpectralCutoff`:

```lean
@[expose] noncomputable def spectraSpectralCutoff
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) : H →L[ℂ] H :=
```

This is the bounded projection onto the closed spectral interval `[-τ, τ]` for a *partial linear map* `A`, not the restriction of an everywhere-defined bounded operator. The cutoff is meaningful even when `τ` is negative, though the narrated exhaustion uses nonnegative radii.

`DavisKahan/SpectralTheory/SpectralCutoff.lean` — `spectraSpectralCutoff_range_le_domain`:

```lean
theorem spectraSpectralCutoff_range_le_domain
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) :
    LinearMap.range (spectraSpectralCutoff A hA τ).toLinearMap ≤ A.domain := by
```

The entire range of the cutoff lies in `A.domain`; this is stronger than preservation of the domain when starting from a domain vector.

`DavisKahan/SpectralTheory/SpectralCutoff.lean` — `spectraSpectralCutoff_commutes_on_domain`:

```lean
theorem spectraSpectralCutoff_commutes_on_domain
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) (x : A.domain) :
    ∃ hx : spectraSpectralCutoff A hA τ (x : H) ∈ A.domain,
      A ⟨spectraSpectralCutoff A hA τ (x : H), hx⟩ =
        spectraSpectralCutoff A hA τ (A x) :=
```

The membership proof `hx` makes the left side a legal application of an unbounded operator. Its equality with the projected image `P_R(Ax)` gives graph-norm convergence in conjunction with the next theorem.

`DavisKahan/SpectralTheory/SpectralCutoff.lean` — `spectraSpectralCutoff_tendsto_identity`:

```lean
theorem spectraSpectralCutoff_tendsto_identity
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (x : H) :
    Tendsto (fun τ : ℝ => spectraSpectralCutoff A hA τ x)
      atTop (𝓝 x) :=
```

This is convergence in the norm topology of `H` **for each fixed `x`**. It does not assert operator-norm convergence of the cutoff family.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean` — `truncation_eq_on_specProjection`:

```lean
theorem truncation_eq_on_specProjection {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ∃ hy : specProjection hA B hB y ∈ A.domain,
      A ⟨specProjection hA B hB y, hy⟩ = truncation hA B hB hbnd y := by
```

The theorem identifies applying `A` to a bounded spectral band with a total bounded truncation operator, and explicitly carries the domain proof needed to type the expression.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean` — `norm_truncation_apply_le`:

```lean
theorem norm_truncation_apply_le {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ‖truncation hA B hB hbnd y‖ ≤ max 0 M * ‖y‖ :=
```

The bound on the truncated operator follows from the boundedness of its spectral set. In the closed interval case with `R≥0`, this is the claimed norm bound `R`.

**Real Hilbert spaces:** `DavisKahan/SpectralTheory/Real/SpectralCutoff.lean` supplies a separate real implementation by complexification and descent, including `realSpectralCutoff_tendsto_identity`. The statements displayed above use the complex Hilbert-space API. The `ForTauCeti` spectral-measure files belong to the body of mathematics developed within the DKPS program and subsequently reorganized/upstreamed, so their present import path does not imply separate mathematical origin.

**Scope:** These are source declaration headers, not complete proof bodies. The finite-simple-function approximation and compact-operator norm convergence are proved mathematically in the narration but are not claimed to be the direct statements of the quoted Lean theorems. No Lean compilation of new code is implied.
