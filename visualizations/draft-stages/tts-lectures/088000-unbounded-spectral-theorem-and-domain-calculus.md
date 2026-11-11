# 088000 — Unbounded spectral theorem and domain calculus

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `074000` integration and L two, `076000` projection-valued measures, `082000` spectral cutoffs, `087000` Cayley transforms. **Next:** `089000` reducing domains.

<!-- BEGIN SPOKEN LECTURE -->

# The unbounded spectral theorem: the formula and the allowable inputs

Imagine a diagonal matrix with entries one, two, three, and so on. Its action is easy to describe: multiply each coordinate by the corresponding diagonal entry. But on infinite square-summable sequences, we cannot do that for every input. The resulting sequence might fail to be square summable.

This is the central problem solved by the unbounded spectral theorem. It tells us how a self-adjoint operator acts, even when there is no eigenvector basis, and it tells us exactly which vectors belong to its domain.

We will first understand the theorem through an infinite diagonal example. Then we will replace individual eigenvalues with spectral regions and see how the same reasoning works for continuous spectrum.

## The diagonal picture

Let A multiply coordinate N of an ell-two sequence by N. The Hilbert space ell two consists of sequences whose squared magnitudes have a finite sum.

To apply A, we multiply each coordinate by its index. The output is in ell two exactly when the sum of N squared times the squared magnitude of the input coordinate is finite.

That condition can be described as a weighted sum over spectral values. Each coordinate carries a spectral value N, and the squared magnitude of that coordinate measures how much of the vector is sitting at that spectral value. The output length squared is the sum of spectral value squared times that coordinate's weight.

This is what the spectral theorem will generalize. Instead of always having a discrete list of eigenvalues, we may have spectral mass spread across intervals. Instead of adding the contributions, we integrate them. And the same weighted-square-integrability condition determines the domain.

## How a spectral projection measures a vector

Let A now be any self-adjoint operator on a complex Hilbert space, possibly unbounded.

Its spectral theorem supplies a projection for each Borel set of real numbers. A Borel set can be an interval, a countable union of intervals, or a set formed by the usual countable operations starting from open sets.

Call the projection associated with a spectral set B the projection onto B. Applying it to a vector extracts the component belonging to that spectral region.

In the diagonal example, projecting onto the interval from two to four keeps only coordinates two, three, and four. Projecting onto all even positive integers keeps just the even-numbered coordinates.

Now measure the squared length of the extracted component. For each vector x, this measurement gives a nonnegative number to every Borel set. These numbers form a finite measure, called the scalar spectral measure of x.

Its total mass is the squared length of x. You can think of it as a distribution of the vector's squared magnitude across the real spectral line. It is not necessarily a probability distribution because the vector might not have unit length.

For a diagonal operator, the measure consists of masses at eigenvalues. For continuous spectrum, the mass may be spread across intervals with no mass concentrated at any single point.

This lets us say what it means to apply a function of the operator.

## From a bounded function to an unbounded one

Suppose f is a bounded function of a real spectral value. We can define f of A by spectral calculus. In the diagonal example, it multiplies coordinate N by f of N. For a general self-adjoint operator, it multiplies the contribution in each spectral region by the corresponding function value.

A fundamental norm identity says that the squared length of f of A applied to x is the integral of the squared absolute value of f against the scalar spectral measure of x.

If f is bounded, this is at most the square of its largest magnitude times the squared length of x. So f of A is a bounded operator on the whole Hilbert space.

Now let f grow without bound. The same formula tells us what can go wrong: the integral of the squared magnitude of f might be infinite for some vectors.

The unbounded spectral calculus therefore defines the domain of f of A to be exactly those vectors for which this integral is finite.

For those vectors, the output can be constructed by truncating f to bounded functions, applying the bounded spectral calculus, and then taking a limit. The integrability condition ensures the truncated outputs are Cauchy in Hilbert-space norm.

Here is the essential point. The theorem provides the operator and its domain together. A formal symbol like f of A cannot, by itself, tell us whether a particular input is legal.

## Recover the original operator

To reconstruct A, choose the simplest unbounded function: the spectral variable itself. In the diagonal example, the function sends N to N. In a multiplication-operator example, it sends a real input t to t.

The domain condition becomes finiteness of the integral of the square of the spectral value against the scalar spectral measure.

The output norm squared equals that integral. And the graph norm squared adds the ordinary squared length of x, giving an integral of one plus the square of the spectral value.

That graph-norm identity tells us how strongly the domain condition weighs parts of a vector living far out in the spectrum. Spectral mass at large absolute values contributes much more to the graph norm than to the ordinary norm.

## A calculation that distinguishes three domains

Return to the diagonal operator with spectral values one, two, three, and so on.

First take the sequence whose N-th coordinate is one divided by N. It is square summable. But A would turn it into a sequence of ones, so it is outside the domain of A.

Next take the sequence whose N-th coordinate is one divided by N squared. Multiplying once by N gives the reciprocal sequence, which is square summable. So this new vector lies in the domain of A.

What about applying A a second time? The second multiplication produces a sequence of ones. That is not square summable. So our vector belongs to the domain of A, but not to the domain of A squared.

Finally, any sequence supported in finitely many coordinates belongs to the domain of every power of this diagonal operator. Repeated multiplication changes only finitely many entries.

These three cases show why we cannot infer that an input is legal for an operator just because it is a Hilbert-space vector, or infer that it is legal for A squared just because it is legal for A.

## Bounded cutoffs approximate the unbounded operator

There is a reliable way to approach A using bounded operators.

Choose a radius R and keep only spectral values between negative R and positive R. Call this spectral projection P R. The cutoff operator multiplies by the spectral variable inside that band and by zero outside. Its norm is at most R.

For an arbitrary Hilbert-space vector x, P R x approaches x as the radius grows. Why? The squared length of the discarded part is the spectral mass outside the band. That tail mass tends to zero because the total spectral measure of x is finite.

Even if x is outside the domain of A, its cutoff P R x always lies inside the domain. All its spectral mass is confined to a region where the multiplier is bounded.

Now suppose x actually belongs to the domain of A. Then not only do the cutoff inputs approach x, but their outputs under A also approach A x. The reason is that A applied to P R x equals P R applied to A x, and the cutoffs converge on every fixed Hilbert-space vector, including A x.

This is convergence in the graph norm. It gives us bounded pieces that approximate the whole unbounded operator on precisely the vectors where the operator is defined.

What if x is outside the domain? The cutoff inputs still converge. But the outputs cannot converge in Hilbert norm. If they did, closedness of A would force x into the domain, a contradiction.

Thus domain membership can be tested through convergence of the truncated outputs.

## Continuous spectrum changes the picture, not the rule

Consider the Hilbert space of square-integrable functions on the real line. Define A by multiplying a function at position t by the number t.

Its domain consists of functions for which the integral of t squared times the squared absolute value of the function is finite.

The spectral projection onto an interval simply keeps the function on that interval and sets it to zero elsewhere. The scalar spectral measure of a vector is the integral of its squared magnitude over the selected region.

This operator has no nonzero eigenvectors. An eigenfunction for a number lambda would need to vanish everywhere except at the single point t equal to lambda. A function concentrated on one point represents zero in this Hilbert space because the point has measure zero.

Nevertheless the spectrum is the entire real line. The spectral theorem describes it without constructing any eigenvector basis.

The formula for the domain remains the same kind of square-integrability test as in the diagonal example. Only the sum has become an integral.

## When an algebraic identity loses its domain

There is one final trap worth seeing with the diagonal operator.

Consider two scalar functions of the spectral value. Let g of N equal N, and let f of N equal one over N. Their product is one for every positive integer N.

The operator g of A is our unbounded diagonal multiplication operator. The operator f of A is bounded; it divides coordinate N by N.

Now compose them in that order: apply g of A first, then f of A. For every input in the domain of g of A, the two multiplications cancel and return the original vector.

But this composition is defined only on the domain of g of A, which is a proper subset of ell two. Meanwhile the spectral operator corresponding to the pointwise product f times g is the identity, defined on all of ell two.

The formulas agree wherever both are defined, but the operators are not equal because their domains differ.

That example captures the discipline of unbounded spectral calculus. Algebraic identities of scalar functions are useful, but operator equalities also require equal domains.

The unbounded spectral theorem gives us a complete model: a spectral distribution, a rule for multiplying it, and an integrability test specifying which input vectors are allowed. Together those three ingredients determine the operator.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a self-adjoint \(A\) with projection-valued measure \(E\), put \(\mu_x(B)=\|E(B)x\|^2\). The domain of a measurable spectral operator is \(D(f(A))=\{x:\int |f(\lambda)|^2\,d\mu_x(\lambda)<\infty\}\). In particular \(D(A)\) requires the finite second spectral moment, and \(\|Ax\|^2=\int\lambda^2\,d\mu_x\). The cutoff \(P_R=E([-R,R])\) maps all of \(H\) into \(D(A)\), and for \(x\in D(A)\) satisfies \(AP_Rx=P_RAx\to Ax\), while \(P_Rx\to x\).

### Domain-sensitive product example

For the maximal diagonal operator \(A=\operatorname{diag}(1,2,\ldots)\),
let \(g(\lambda)=\lambda\) and \(f(\lambda)=1/\lambda\) on
\(\sigma(A)=\{1,2,\ldots\}\). Then \(f(A)\) is bounded and
\[f(A)g(A)=I|_{D(A)},\qquad (fg)(A)=I|_{\ell^2}.\]
The actions agree on \(D(A)\), but the operators have different domains.
In general the composition domain is
\(\{x\in D(g(A)):g(A)x\in D(f(A))\}\), and the scalar product identity
alone does not imply equality with the maximal operator \((fg)(A)\).

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `specProjection_mem_domain`:

```lean
theorem specProjection_mem_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    specProjection hA B hB (x : H) ∈ A.domain := by
```

Spectral projections preserve the original operator domain.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `specProjection_apply_domain`:

```lean
theorem specProjection_apply_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    A ⟨specProjection hA B hB (x : H), specProjection_mem_domain hA B hB x⟩
      = specProjection hA B hB (A x) := by
```

Commutation with an unbounded operator is a typed equality using an explicit proof of domain membership.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean` — `tendsto_specProjection_Icc`:

```lean
theorem tendsto_specProjection_Icc (x : H) :
    Filter.Tendsto
      (fun τ : ℝ => specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x)
      Filter.atTop (nhds x) := by
```

The bounded spectral-band projections converge strongly, pointwise on each Hilbert vector.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean` — `truncation_eq_on_specProjection`:

```lean
theorem truncation_eq_on_specProjection {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ∃ hy : specProjection hA B hB y ∈ A.domain,
      A ⟨specProjection hA B hB y, hy⟩ = truncation hA B hB hbnd y := by
```

A bounded truncation agrees with the original operator on the selected bounded band.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean` — `norm_truncation_apply_le`:

```lean
theorem norm_truncation_apply_le {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ‖truncation hA B hB hbnd y‖ ≤ max 0 M * ‖y‖ :=
```

The bounded truncation norm is controlled by the spectral-band radius.

**Scope:** The spectral-moment domain characterization is taught from the spectral theorem; these excerpts formalize the projected-domain, commutation, convergence and bounded-band aspects. They do not assert that arbitrary unbounded products have equal domains. These excerpts are from the supplied source snapshot and are not new compiled Lean code. Reusable `ForTauCeti` constructions have explicit DKPS donor/origin notes; the current file namespace does not imply an external origin.
