# 074000 — Measures, integration and L2

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `003000` completeness; `009000–010000` inner products and Hilbert spaces; `072000–073000` function-space examples and measurable sets. **Next:** `075000` continuous functional calculus.

<!-- BEGIN SPOKEN LECTURE -->

# From measurable sets to a Hilbert space of functions

A sigma-algebra tells us which sets can be used in countable constructions. But it does not assign a size to those sets. To integrate functions, measure lengths and probabilities, or build a Hilbert space of square-integrable functions, we need a measure.

Today we will take the sequence from measurable sets to countably additive measures, from simple functions to integration, and from squared integrals to the complete Hilbert space L two. We will also see why three convergence theorems are needed for infinite-dimensional spectral theory.

## What a measure supplies

A measure assigns a number between zero and infinity, including possibly infinity, to each measurable set. The empty set has measure zero. If we have countably many pairwise disjoint measurable sets, the measure of their union equals the sum of their measures.

That last requirement is called countable additivity. It strengthens the familiar rule that two disjoint intervals have combined length equal to the sum of their lengths.

For Lebesgue measure on the real line, an interval receives its ordinary length. A single point has measure zero. Countable sets have measure zero because they are countable unions of zero-measure singletons.

A different example is the Dirac measure concentrated at a point a. A measurable set has measure one if it contains a, and zero otherwise. In this measure, a singleton can have positive measure. The same Borel set may therefore have very different significance under different measures.

These examples explain an earlier contrast. An interval endpoint is negligible for multiplication on Lebesgue L two, but a spectral atom at an eigenvalue need not be negligible.

## Three consequences of countable additivity

First comes monotonicity. If E is contained in F, split F into E and the part outside E. Since the second part has nonnegative measure, the measure of E is no larger than that of F.

Second comes continuity from below. If E-one is contained in E-two, then E-three, and so on, the measure of their union equals the limit of their measures. To prove this, divide the union into the disjoint increments appearing at each stage and use countable additivity.

Third comes continuity from above when the first set has finite measure. If the sets decrease, the measure of their intersection is the limit of their measures. This follows by applying continuity from below to the complements relative to the first set. The finite-measure assumption permits the needed subtraction.

Notice how all three statements convert set limits into numerical limits. We will want analogous rules for integrals and spectral projections.

## Integrating the simplest functions

Take a nonnegative simple function: it has finitely many values and can be written as a sum of positive constants multiplied by indicators of disjoint measurable sets.

Define its integral by multiplying each value by the measure of the corresponding set and adding. If a simple function equals three on a set of measure two and one on a disjoint set of measure five, its integral is six plus five, namely eleven.

For a general nonnegative measurable function, consider all nonnegative simple functions bounded above by it. Define the integral as the supremum of their integrals.

This definition extends familiar Riemann sums, but it is organized around measurable sets rather than fixed interval partitions. It also handles functions with infinitely many discontinuities and spaces that are not intervals at all.

A measurable real function that can have negative values is split into its positive and negative parts. We integrate them separately, requiring finite total absolute integral when we say the function is integrable. For complex functions, integrate real and imaginary parts.

## Why approximation works

Every nonnegative measurable function can be approximated from below by an increasing sequence of nonnegative simple functions.

Here is the construction idea. For each positive integer n, round function values downward to multiples of one over two to the n, and cap the values at n. This gives a finite-valued measurable approximation. As n grows, the grid becomes finer and the cap becomes larger. With a suitable choice of partitions, the approximations increase pointwise to the original function.

The monotone convergence theorem says that their integrals increase to the integral of the limit function. Its proof follows the construction of the integral as a supremum of simple integrals and the countable-additivity properties of the measure.

The theorem is stronger than a mere computational recipe. It permits interchange of an increasing limit and integration without assuming a uniform bound on the functions.

## Two more convergence principles

Fatou's lemma says that the integral of the pointwise lower limit of nonnegative measurable functions is no larger than the lower limit of their integrals. A convenient proof applies monotone convergence to the increasing sequence obtained by taking, at each stage, the infimum of the functions from that stage onward.

The dominated convergence theorem gives a different kind of limit interchange. Suppose functions converge almost everywhere to f, and their absolute values are all bounded by one common integrable function g. Then their integrals converge to the integral of f.

Why is domination necessary? Consider functions that equal n on an interval of length one over n, and zero elsewhere. Their integrals remain one. For every positive point, the functions eventually vanish. Thus they converge almost everywhere to zero, but the integrals do not converge to zero.

The mass is concentrating in a narrower region as its height rises. There is no single integrable dominating function for this entire sequence. Pointwise convergence alone cannot control integrals.

These convergence theorems will later justify passing from finite spectral sums and simple symbols to measurable functions of an operator.

## The L two norm

Define L two to consist of measurable complex functions whose squared absolute values have finite integral, identifying functions equal almost everywhere. The squared norm of f is the integral of squared absolute value.

For two such functions, define their inner product by integrating the complex conjugate of the first times the second. The integral exists by the Cauchy–Schwarz inequality for integrals: the absolute value of the inner product is bounded by the product of the two L two norms.

One way to prove that inequality is to integrate the nonnegative square of f minus a scalar multiple of g. Choose the scalar so the resulting quadratic expression is minimized. Its discriminant cannot be positive in the forbidden direction, giving Cauchy–Schwarz.

The parallelogram identity follows from expanding squared absolute values pointwise and integrating. Thus L two is an inner-product space.

## Why we identify functions almost everywhere

Consider the function that equals one at a single point of the unit interval and zero everywhere else. Under Lebesgue measure, the integral of its squared absolute value is zero. Without identifying almost-everywhere-equal functions, this nonzero function would have zero norm.

After taking equivalence classes, a vector in L two is not a particular pointwise formula. Its values on sets of measure zero are irrelevant. This distinction is especially important when defining a multiplication operator: changing its symbol on a null set produces the same operator on L two.

For the unit interval, the constant function one has norm one. The coordinate function x has norm one over square root of three. Their inner product is the integral of x, which is one half. Therefore the orthogonal projection of x onto the constants is the constant function one half.

We can verify this by taking the inner product of x minus one half with the constant one: the integral is zero.

## Completeness of L two

The most important analytic claim is that every Cauchy sequence in the L two norm converges to a vector of L two.

Here is a proof outline that shows where integration is needed. From a Cauchy sequence, choose a subsequence whose successive L two distances are smaller than one over two to the n. The sum of these distances is finite.

Use the integral triangle inequality to show that the series of absolute successive differences is integrable in an appropriate limit sense and finite almost everywhere. At almost every point, the selected subsequence therefore converges pointwise. Call its limit f.

Fatou's lemma and the Cauchy bounds show that f belongs to L two and that the subsequence converges to f in L two norm. Since the original sequence was Cauchy and has a convergent subsequence, the entire sequence converges to f.

This produces the completeness missing from a space of ordinary continuous functions with only an integral norm. L two is a Hilbert space.

## Infinite orthogonality from disjoint sets

Take pairwise disjoint measurable sets, each of finite positive measure. Divide each indicator by the square root of its measure. The resulting L two vectors have norm one. Their pairwise inner products vanish because the sets do not overlap.

If there are infinitely many such sets, we obtain an infinite orthonormal family. Hence L two cannot be finite-dimensional.

For the interval from zero to one, use the consecutive intervals from one over n plus two to one over n plus one. Each has positive finite length, and they are disjoint. This gives an explicit witness to infinite dimensionality in the Lean source.

## Returning to spectral theory

When a projection-valued measure assigns a projection to each Borel set, each vector will induce a scalar measure: the squared norm of its projected component. Integrals against that scalar measure will define norms of functions of the operator.

Everything we developed today supports that construction. Countable additivity controls disjoint spectral pieces. Simple functions provide initial approximations. Monotone and dominated convergence justify limits. L two and its completeness provide the ambient space in which spectral models live.

Next we will first finish a simpler problem: defining continuous functions of bounded self-adjoint operators. That construction uses only uniform approximation, but its limitations will motivate the fuller measure-based calculus.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a measure \(\mu\) on \((X,\Sigma)\), \(L^2(\mu)\) consists of equivalence classes of measurable functions with \(\int |f|^2\,d\mu<\infty\). The inner product is \(\langle f,g\rangle=\int\overline f g\,d\mu\). Disjoint, measurable sets \(E_n\) with \(0<\mu(E_n)<\infty\) yield orthonormal normalized indicators \(1_{E_n}/\sqrt{\mu(E_n)}\), proving infinite dimensionality.

The monotone convergence, Fatou, and dominated convergence theorems are mathematical background supplied by Mathlib's measure-theory infrastructure; the cited DKPS/TauCeti modules use those foundations rather than re-proving their general statements.

**Lean bridge (verified source excerpts).**

`ForTauCeti/MeasureTheory/LpInfiniteDimensional.lean` — `unitIocMeasure_Ioc` (exact source declaration header):

```lean
theorem unitIocMeasure_Ioc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    unitIocMeasure (Set.Ioc a b) = ENNReal.ofReal (b - a) := by
```

The interval measure computes the ordinary length for subintervals of the unit interval.

`ForTauCeti/MeasureTheory/LpInfiniteDimensional.lean` — `not_finiteDimensional_lpTwo_of_pairwise_disjoint` (exact source declaration header):

```lean
theorem not_finiteDimensional_lpTwo_of_pairwise_disjoint {α : Type*} [MeasurableSpace α]
    {mu : Measure α} (s : ℕ → Set α) (hmeas : ∀ n, MeasurableSet (s n))
    (hfin : ∀ n, mu (s n) ≠ ∞) (hzero : ∀ n, mu (s n) ≠ 0)
    (hdisj : ∀ i j : ℕ, i ≠ j → Disjoint (s i) (s j)) :
    ¬ FiniteDimensional 𝕜 (Lp 𝕜 2 mu) := by
```

The stronger result assumes measurable, finite-positive-mass, pairwise-disjoint sets and concludes that their L-two space is not finite dimensional.
