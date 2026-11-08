# 072000 — Infinite-dimensional Hilbert examples

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `003000` completeness, `009000–015000` Hilbert operators, `025000–032000` finite spectral theory. **Next:** `073000` sigma-algebras and Borel sets.

<!-- BEGIN SPOKEN LECTURE -->

# A self-adjoint operator without eigenvectors

Our finite-dimensional spectral theorem diagonalized every self-adjoint matrix. We selected eigenvectors, built orthogonal projections, and then defined functions of the matrix by changing its eigenvalues.

In infinite dimensions, the same procedure can fail at its first step. A bounded self-adjoint operator can have no nonzero eigenvectors at all. We need to understand a concrete example before replacing matrices with spectral measures.

Today we will visit four models: square-summable sequences, square-integrable functions, multiplication by a coordinate, and the unilateral shift. Each one exposes a feature that finite matrices cannot show.

## The sequence Hilbert space

Start with an infinite list of complex numbers: x-zero, x-one, and so on. Retain only sequences whose squared absolute values add to a finite number. This is the space called ell two.

The inner product of two such sequences is the sum of the conjugate of one coordinate times the corresponding coordinate of the other. Cauchy–Schwarz guarantees convergence. The norm is the square root of the sum of squared absolute values.

The familiar coordinate vectors, with one entry equal to one and the rest zero, form an orthonormal basis. But a general vector is an infinite sum of these basis directions, converging in norm. Truncating after N coordinates gives approximations, and the squared error is exactly the tail of the convergent series.

To see completeness, imagine a Cauchy sequence of vectors in ell two. Each coordinate is Cauchy in the complex numbers, hence converges. An inequality for finite partial sums shows that the coordinatewise limit still has bounded squared energy. The same tail and Cauchy arguments then show convergence in ell two norm.

This space has the geometric structure of Euclidean space, but no finite list spans it.

## Square-integrable functions

Now consider functions on the interval from zero to one. Keep those for which the integral of squared absolute value is finite. Identify two functions if they differ only on a set of measure zero. We call the resulting space L two.

Why identify functions almost everywhere? Because the integral norm cannot detect a difference at a single point. If f and g disagree only at one position, their difference has norm zero. A normed space must regard any vector of norm zero as the zero vector.

The inner product is the integral of the conjugate of f times g. Again Cauchy–Schwarz controls it.

There is a useful comparison with ell two. In ell two we sum squared coordinates. In L two we integrate squared values over a continuum. Both are Hilbert spaces, and both have countable orthonormal bases in these standard examples. Yet the most natural operators on them can have very different spectral behavior.

For example, take the constant function one on the unit interval. Its L two norm is one. The coordinate function f of x equals x has squared norm equal to the integral of x squared from zero to one, which is one third. Its norm is therefore one over the square root of three.

## Multiplication by the coordinate

Define an operator M on L two by sending a function f to the function x times f of x. Its norm is at most one because the magnitude of x is at most one on the interval. In fact its operator norm equals one: choose unit functions supported very close to the right endpoint, where multiplication by x almost preserves their lengths.

M is self-adjoint. To check this, move the real scalar x between the two factors in the inner-product integral. This is the direct analogue of a real diagonal matrix.

Now ask whether M has an eigenvector. If M f equals lambda times f, then x times f of x equals lambda times f of x for almost every x. So f can be nonzero only where x equals lambda.

For each fixed lambda, that set is either empty or a single point. A single point has Lebesgue measure zero. Therefore f is the zero vector of L two. No nonzero eigenvector exists.

We have constructed a bounded self-adjoint operator on a nonzero Hilbert space with no eigenvectors. The finite eigenbasis proof cannot even begin.

## The spectrum still has content

Perhaps the operator has no spectrum at all? No. Its spectrum is the entire interval from zero to one.

First take a complex number lambda outside that interval. The function one divided by x minus lambda is bounded on the interval. Multiplication by this reciprocal gives a bounded inverse to M minus lambda times the identity. Such lambda lie outside the spectrum.

Now choose lambda inside the interval. Around lambda, take a tiny subinterval and a function supported there, normalized to have L two norm one. On that support, x is close to lambda. The norm of M f minus lambda f is therefore as small as the width of the subinterval.

So M minus lambda cannot have a bounded inverse. If it did, applying that inverse would force every unit vector to have its image bounded below by a positive constant. Our localized test functions contradict this.

At the endpoints, use one-sided small intervals. The same argument works. Hence the full closed interval is the spectrum, even though no spectral point is an eigenvalue.

These localized functions are approximate eigenvectors. Their supports shrink as their errors shrink, so they do not approach a nonzero eigenvector in L two norm.

## A diagonal model with infinitely many eigenvalues

Contrast M with a diagonal operator D on ell two. Let D multiply coordinate n by one divided by n plus one. Every coordinate vector is an eigenvector, and the corresponding eigenvalues approach zero.

Zero belongs to the spectrum because the unit coordinate vectors far out in the sequence have images with norms tending to zero. There is no bounded inverse for D. Yet zero is not an eigenvalue: no nonzero coordinate can be supported where the diagonal entry vanishes, since every entry is positive.

Here the spectrum consists of the listed positive eigenvalues together with their limit point zero. This example shows that even when an eigenbasis exists, the spectrum can contain a point that is not an eigenvalue.

The multiplication example goes further: none of the points in its interval spectrum are eigenvalues.

## The unilateral shift

A final example reminds us why self-adjointness matters. On ell two define the forward shift U by placing a zero at the beginning of a sequence and moving every entry one position to the right.

U preserves the norm exactly, so U adjoint times U equals the identity. But U is not onto: no vector in its range has a nonzero first coordinate. Therefore U times U adjoint is the projection onto the subspace with first coordinate zero, rather than the identity.

In finite dimensions, an isometry of a space into itself must be surjective. In infinite dimensions, this implication fails.

Its adjoint is the backward shift, which discards the first coordinate. The backward shift has genuine eigenvectors: if the magnitude of lambda is less than one, the sequence one, lambda, lambda squared, and so on is square-summable and is an eigenvector of the backward shift with eigenvalue lambda.

This distinction between a shift and its adjoint is impossible for a unitary operator and illustrates why we must not treat every norm-preserving map as unitary.

## What replaces the finite eigenbasis

The continuous multiplication model suggests the answer. For a measurable subset of the interval, define a projection that keeps the values of a function on that subset and sets it to zero elsewhere.

Two disjoint subsets give orthogonal projections. The projection for a union of disjoint subsets combines their contributions. Instead of one projection per eigenvalue, we have one projection for each sufficiently well-behaved set of spectral values.

For a finite diagonal matrix these projections simply select coordinate eigenspaces. For multiplication by x they select the support of a function according to the value of x, even though there are no eigenvectors.

We have not yet established what counts as a well-behaved set or how to sum projections over infinitely many pieces. These are the tools that allow a spectral theorem without an eigenvector basis.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

On \(L^2((0,1),dx)\), \((Mf)(x)=xf(x)\) is bounded and self-adjoint. Its eigen-equation \((x-\lambda)f(x)=0\) almost everywhere forces \(f=0\); nevertheless \(\sigma(M)=[0,1]\). The resolvent is multiplication by \((x-\lambda)^{-1}\) outside \([0,1]\), while normalized indicators on shrinking intervals show the failure of a bounded inverse inside it.

On \(\ell^2(\mathbb N)\), the unilateral shift \(U(x_0,x_1,\ldots)=(0,x_0,x_1,\ldots)\) satisfies \(U^*U=I\) but \(UU^*=I-P_{e_0}\).

**Lean bridge (verified source excerpts).**

`ForTauCeti/MeasureTheory/LpInfiniteDimensional.lean` — `not_finiteDimensional_lpTwo_unitIocMeasure` (exact source declaration header):

```lean
theorem not_finiteDimensional_lpTwo_unitIocMeasure :
    ¬ FiniteDimensional 𝕜 (Lp 𝕜 2 unitIocMeasure) := by
```

The repository proves this L-two space is infinite-dimensional by constructing disjoint positive-measure intervals, rather than assuming a function space must be infinite-dimensional.

`ForTauCeti/MeasureTheory/MulLpSpectrum.lean` — `ae_mem_spectrum_mulLp` (exact source declaration header):

```lean
theorem ae_mem_spectrum_mulLp : ∀ᵐ x ∂ρ, g x ∈ spectrum ℂ (mulLp ρ hg hgC) := by
```

For a bounded measurable complex multiplier on a sigma-finite measure space, the symbol takes values in the multiplication operator spectrum almost everywhere. This is part of the spectral analysis of multiplication models; the interval example is derived mathematically in the narrated lecture.
