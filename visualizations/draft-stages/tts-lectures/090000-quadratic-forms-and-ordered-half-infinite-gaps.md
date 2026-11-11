# 090000 — Quadratic forms and ordered half-infinite gaps

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `033000` quadratic-form order, `065000` ordered separation, `074000` integration, `088000` unbounded spectral calculus, `089000` reducing domains. **Next:** `091000` Yosida approximation.

<!-- BEGIN SPOKEN LECTURE -->

# Comparing unbounded spectra through ordered gaps

Suppose two self-adjoint operators have spectra that are far apart. One operator has all its spectral values above a certain level. The other has all its spectral values below a lower level.

Can we measure the separation without listing eigenvalues, and without assuming that either operator is bounded?

Yes. The useful quantities are lower and upper bounds on quadratic forms. Once those bounds create an ordered gap, the spectral theorem lets us build bounded exponential operators and use them to solve an important operator equation.

Let's develop the argument from a concrete example.

## A gap between two infinite lists

Work on ell two, the Hilbert space of square-summable sequences. Define an operator A that multiplies coordinate N by N plus two. Its spectral values are three, four, five, and so on. They have a lowest value, three, but no upper bound.

On a second copy of ell two, define an operator B that multiplies coordinate N by negative N. Its spectral values are negative one, negative two, negative three, and so on. They have a highest value, negative one, but no lower bound.

These are both unbounded self-adjoint operators, defined on their appropriate weighted square-summability domains.

Every spectral value of A is at least three. Every spectral value of B is at most negative one. The nearest the two spectra can come is a distance of four.

More importantly, all of B lies below all of A. We call this an ordered spectral gap. It has direction, not just a minimum distance.

That extra order will let us construct an inverse using decaying exponentials.

## Translate spectral location into a quadratic-form inequality

For a self-adjoint operator A and an allowed input x, the inner product of A x with x is a real number. It is the quadratic form, or energy pairing, of A at x.

Return to the diagonal operator with eigenvalues three, four, five, and so on. Its quadratic form is the sum of each eigenvalue times the squared magnitude of the corresponding coordinate.

Every eigenvalue in that sum is at least three. Therefore the whole sum is at least three times the squared length of x.

That proves a lower quadratic-form bound. The operator may amplify some directions by arbitrarily large factors, but its quadratic form never drops below three times squared length.

For B, every spectral value is at most negative one. Its quadratic form is therefore at most negative one times squared length. This is an upper form bound.

The general statements have the same shape. An operator is bounded below by a number a in quadratic-form sense if its energy pairing is at least a times squared length for every vector in its domain. It is bounded above by b if the corresponding inequality points the other way.

These are one-sided bounds. They do not assert a finite operator norm.

## Why the bounds survive continuous spectrum

Our diagonal proof used a sum over eigenvalues. But a self-adjoint operator need not possess an eigenvector basis.

The spectral theorem replaces that sum with an integral. For each vector x there is a positive scalar spectral measure describing how its squared magnitude is distributed across the real spectral line.

The quadratic form of A is the integral of the spectral value against that measure, provided x belongs to the domain of A.

Suppose the spectrum of A lies entirely at or above a. Every spectral value that contributes to the integral is then at least a. Subtract a inside the integral. The integrand is nonnegative, so the integral is nonnegative.

We conclude that the quadratic form of A at x is at least a times the squared length of x.

The same argument with reversed inequalities proves an upper bound when the spectrum lies at or below b.

For self-adjoint operators, the converse also holds: a lower quadratic-form bound excludes spectrum below that level, and an upper bound excludes spectrum above it. The argument can be seen by testing the inequality on spectral vectors supported in a region where it would otherwise fail.

This is why quadratic-form inequalities are a practical way to state spectral location even for continuous and unbounded spectra.

## The form can have a larger domain

There is a technical distinction worth building into the picture.

When A is unbounded, the expression involving A x requires x to belong to the domain of A. But if A is positive, we can also define an energy form by applying the positive square root of A and taking the squared length of the result.

That second expression has a possibly larger domain: the domain of the square root.

For the diagonal operator with eigenvalues N, the square-root energy of a sequence is the sum of N times the squared magnitude of coordinate N. The full operator domain instead requires the sum with N squared to converge.

Choose coordinates equal to one divided by N to the power three halves. The sum with one factor of N converges, but the sum with N squared diverges.

This vector has finite square-root energy even though A cannot be applied to it as a Hilbert-space vector.

So a quadratic-form inequality may extend to more vectors than an operator identity. That extension is useful, but we must not insert A x into an equation for a vector that lies only in the form domain.

For an operator bounded below by a, the corresponding nonnegative form is built from the square root of A minus a times the identity, together with the scalar lower-bound term.

## What ordered separation adds

Now let A act on one Hilbert space and B on another. Suppose A has a lower form bound a and B has an upper form bound b, with a strictly greater than b.

Define delta to be a minus b. It is positive.

Every spectral value of A lies above every spectral value of B, with separation at least delta. This is the ordered-gap hypothesis.

Compare this with merely saying that the spectra are disjoint. Disjoint spectral sets need not be separated by a positive distance. Even if they are separated by a positive distance, their pieces may alternate along the line. There may be no single level with all of one spectrum above it and all of the other below it.

An ordered gap gives a uniform direction. That direction determines which exponentials decay together.

## Exponentials of unbounded operators can be bounded

If A is bounded below by a, look at the scalar function that sends a spectral value lambda to the exponential of negative t times lambda, for a nonnegative time t.

Although lambda can grow without bound, this exponential function is bounded on the spectrum of A. Its largest possible magnitude is no more than the exponential of negative a times t.

The spectral calculus therefore defines a bounded operator called the exponential of negative t A.

Similarly, because B is bounded above by b, the spectral calculus defines the exponential of positive t B. Its norm is at most the exponential of b times t.

Return to our diagonal example. On coordinate N, the first exponential multiplies by the exponential of negative t times N plus two. The second multiplies by the exponential of negative t times N. Both decrease as t increases.

Now insert any bounded operator C between them. We can form the composition: first apply the exponential of t B, then C, then the exponential of negative t A.

The operator norm of this composition is at most the norm of C times the product of the two exponential bounds. That product simplifies to the exponential of negative delta times t.

So the entire composition decays at least as fast as an exponential whose rate is the spectral gap.

Notice that each exponential separately need not decay. If a is negative, the first upper bound may grow. If b is positive, the second may grow. What is guaranteed to decay is their product, because a is strictly greater than b.

## A scalar equation suggests the operator formula

Consider the elementary equation: three times an unknown number, minus that unknown number times negative one, equals a prescribed number c.

The left side is four times the unknown. The answer is c divided by four. The denominator is exactly our ordered gap.

There is another way to express that division. Multiply c by the exponential of negative four times t, then integrate from time zero to infinity. The result is c divided by four.

This integral suggests how to solve a matrix or operator equation where multiplication occurs on both sides.

The equation is called a Sylvester equation. We seek an operator X such that A applied to X, minus X applied to B, equals a given bounded operator C.

When A and B are unbounded, this is an equation on a specified domain, not a formula that can be applied to arbitrary vectors without checking. In particular, X must carry the domain of B into the domain of A for the expression to make sense.

The natural candidate for X is obtained by integrating the composition we just bounded: the exponential of negative t A, followed around C by the exponential of t B, from time zero to infinity.

For each fixed input vector, the integrand is a continuous Hilbert-space-valued function, and its norm has the exponential upper bound we proved. The integral therefore defines a bounded operator X. Its norm is at most the norm of C divided by delta.

The gap has turned into an inverse bound.

To see why the integral solves the equation, consider differentiating the integrand. Formally, its derivative is negative A applied to the integrand plus the integrand followed by B. Integrating that derivative from zero to infinity gives zero at infinity minus C at time zero.

For unbounded operators, we must justify the differentiation and show that X really sends allowable inputs for B into the domain of A. Here is the mechanism.

Choose a vector in the domain of B. Instead of integrating immediately from zero to infinity, first integrate from a small positive time epsilon to a large finite time T. At positive times, the exponential of negative t A smooths enough that applying A is legal. We can differentiate the integrand and integrate the resulting identity on that finite interval.

The identity expresses A applied to the truncated integral in terms of three legal pieces: the integrand at epsilon, the integrand at T, and the truncated integral applied to B of our input vector.

As epsilon approaches zero, the first piece approaches C applied to the vector. As T grows, the second piece vanishes because of the exponential gap bound. The third piece approaches X applied to B of the vector.

Both the truncated inputs and their images under A now converge. Because a self-adjoint operator is closed, the limit X of our original input belongs to the domain of A, and A X minus X B equals C on the domain of B.

So the formal integration argument becomes a genuine operator identity, with the required domain preservation proved along the way.

## What the gap estimate tells us

The important quantitative result is simple. If the spectrum of A lies above a, the spectrum of B lies below b, and a exceeds b by delta, then the ordered-gap construction gives a bounded Sylvester solution with norm no greater than the norm of C divided by delta.

In the scalar example, the estimate is exact. The unknown is c divided by four, and the gap is four.

The larger the gap, the smaller the possible response to a fixed forcing term C. That is the mechanism behind many spectral subspace perturbation estimates: separation in the spectrum turns into control of an operator that measures how the subspaces interact.

The main ingredients are now connected. Quadratic forms describe one-sided spectral bounds. Self-adjoint functional calculus gives bounded exponentials of unbounded operators. Ordered separation makes their product decay. Integrating that product produces the inverse estimate, with the operator domains handled explicitly.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

If \(A\) is self-adjoint and \(\sigma(A)\subset[a,\infty)\), then \(\langle Ax,x\rangle\ge a\|x\|^2\) for \(x\in D(A)\). For \(B\) with \(\sigma(B)\subset(-\infty,b]\) and \(a>b\), the gap is \(\delta=a-b>0\). The spectral calculus yields \(\|e^{-tA}\|\le e^{-at}\), \(\|e^{tB}\|\le e^{bt}\), and \(\|e^{-tA}Ce^{tB}\|\le e^{-\delta t}\|C\|\) for \(t\ge0\). The quadratic form of a semibounded operator has a closed form-domain extension defined by its shifted square root; this is distinct from the domain of the operator itself.

### Ordered-gap Sylvester integral

Let \(A\) be self-adjoint on \(H_A\) with \(A\ge aI\) in form sense,
and let \(B\) be self-adjoint on \(H_B\) with \(B\le bI\), where
\(\delta=a-b>0\). For bounded \(C:H_B\to H_A\), define the
strong (vectorwise) operator integral
\[Xx=\int_0^\infty e^{-tA}Ce^{tB}x\,dt.\]
The semigroup bound yields \(\|X\|\le\|C\|/\delta\). With the
appropriate domain argument, \(X(D(B))\subseteq D(A)\) and
\(AXx-XBx=Cx\) for \(x\in D(B)\). In the scalar example
\(A=3\), \(B=-1\), the formula gives \(X=C/4\).

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean` — `SemiboundedBelow`:

```lean
def SemiboundedBelow (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜
```

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralFormBounds.lean` — `le_re_inner_of_specProjection_Iio_eq_zero`:

```lean
theorem le_re_inner_of_specProjection_Iio_eq_zero {c : ℝ}
    (hz : specProjection hA (Set.Iio c) measurableSet_Iio = 0) (x : A.domain) :
    c * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re := by
```

`DavisKahan/SpectralTheory/OrderedHalfLine.lean` — `semiboundedBelow_of_spectrum_subset_Ici`:

```lean
theorem semiboundedBelow_of_spectrum_subset_Ici
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {c : ℝ}
    (hσ : Complex.ofReal ⁻¹' _root_.LinearPMap.spectrum A ⊆
        Set.Ici c) :
    TauCeti.LinearPMap.SemiboundedBelow A c := by
```

`DavisKahan/SpectralTheory/OrderedHalfLine.lean` — `semiboundedAbove_of_spectrum_subset_Iic`:

```lean
theorem semiboundedAbove_of_spectrum_subset_Iic
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {c : ℝ}
    (hσ : Complex.ofReal ⁻¹' _root_.LinearPMap.spectrum A ⊆
        Set.Iic c) :
    TauCeti.LinearPMap.SemiboundedAbove A c := by
```


**Type and hypothesis map.** `SemiboundedBelow A c` is the assertion that every `x : A.domain` satisfies a lower bound for the real part of its energy pairing. `Set.Ici c` is the closed half-line from `c` upward; `Set.Iic c` is the opposite closed half-line. The spectral-containment theorems convert these set hypotheses into the domain-restricted inequalities, without assuming a finite upper or lower operator norm. The square-root form-domain discussion is mathematical background rather than a statement of these particular Lean declarations.

**Scope:** The referenced Lean declarations connect spectral half-line containment to form inequalities and express spectral form bounds. They should not be mistaken for a theorem asserting boundedness of either unbounded generator, nor for the complete unbounded semigroup estimate, which is developed later. Source snippets come from the supplied DKPS snapshot; no Lean compilation was performed for this lecture.
