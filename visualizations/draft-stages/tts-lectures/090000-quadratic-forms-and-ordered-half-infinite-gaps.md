# 090000 — Quadratic forms and ordered half-infinite gaps

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `033000` quadratic-form order, `065000` ordered separation, `074000` integration, `088000` unbounded spectral calculus, `089000` reducing domains. **Next:** `091000` Yosida approximation.

<!-- BEGIN SPOKEN LECTURE -->

# Spectral order without a largest eigenvalue

A bounded self-adjoint matrix has a smallest and a largest eigenvalue. We used those extremes to compare operators through quadratic forms. But many operators appearing in analysis are unbounded. A self-adjoint operator can have a lower spectral bound without having any upper bound at all.

That is enough for an important branch of Davis–Kahan theory. We will derive form inequalities from the spectral theorem and use them to recognize ordered gaps between two operators, even when their spectra extend indefinitely in opposite directions.

## What a quadratic form measures

For a self-adjoint operator A and a vector x in its domain, consider the real number obtained by taking the inner product of A x with x. Call this the quadratic form of A at x.

If A is bounded, the form exists for every x. If A is unbounded, its initial expression is defined only on D of A.

Suppose A is bounded below by a real number a. This means that for every x in D of A, the form is at least a times the squared length of x.

Geometrically, all directions have energy at least a per unit squared length. The statement says nothing about how large the energy can become.

Consider the diagonal operator on ell two that multiplies coordinate N by N plus two. Its spectral values begin at three and increase without limit. It satisfies the lower form bound with a equal to three, even though its operator norm is not finite.

Likewise an operator may be bounded above by b without being bounded below. The diagonal operator with eigenvalues negative N has upper bound negative one and extends indefinitely downward.

## Deriving the form inequality from a spectral half-line

Let A be self-adjoint, and suppose its spectrum lies in the half-line beginning at a and extending to positive infinity.

For a legal vector x, the spectral theorem represents its quadratic form as the integral of lambda against the scalar spectral measure of x. Every lambda receiving spectral mass is at least a.

Subtract a inside the integral. Since lambda minus a is nonnegative on the spectral support, its integral is nonnegative. Therefore the form of A at x is at least a times the squared norm of x.

This proves the lower form inequality. The upper inequality follows in exactly the same way when the spectrum lies below b.

We can also see the argument by finite cutoffs. Restrict the spectral integral to a bounded interval, where multiplication by lambda is bounded. Prove the inequality there, then expand the interval. For a vector in D of A, cutoff vectors and their images converge in Hilbert norm, allowing the inner products to converge.

This proof matters because it does not rely on an eigenbasis. It works for operators whose spectrum is entirely continuous.

## The larger form domain

For a positive self-adjoint operator A, there is a second quadratic-form viewpoint that extends beyond D of A. Its positive square root has its own domain, D of the square root of A.

On that domain define the form by the squared norm of the square root applied to x. For x in D of A, this equals the inner product of A x with x. But the square-root domain can be larger.

Return to the diagonal operator with eigenvalues N. If the N-th coordinate of x is N to the power negative three halves, then the weighted sum with one factor of N converges. Therefore x belongs to the square-root domain. The weighted sum with N squared diverges, so x does not belong to D of A.

This difference is why unbounded form estimates can be meaningful on more vectors than the original operator equation. It is also why an identity stated only at the level of quadratic forms cannot automatically be substituted into an equation involving A x.

For an operator bounded below by a, apply the positive square-root construction to A minus a times the identity. The form becomes a times the squared norm plus a nonnegative term. The lower bound is then built into the definition.

## An ordered gap between two operators

Now let A act on one Hilbert space and B on another. Suppose A has lower form bound a, and B has upper form bound b, with a strictly greater than b.

Define delta as a minus b. It is positive. Every spectral value of A lies at least a, and every spectral value of B lies at most b. Their separation is therefore at least delta, and the ordering is fixed: all of B lies below all of A.

For example, let A have diagonal eigenvalues N plus two, and let B have diagonal eigenvalues negative N, with both indices beginning at one. The smallest value of A is three. The largest value of B is negative one. The gap is four, even though neither operator is bounded in both directions.

An ordered gap gives more information than merely having disjoint spectra. The two spectra cannot interlace. This stronger geometry will lead to a particularly simple Sylvester estimate.

It is not enough to say that the sets have no common spectral values. Two closed sets can be disjoint but approach arbitrarily close together, so the distance between them is zero. And even a positive pairwise distance may fail to produce a single separating cut if the sets lie on alternating sides of each other.

For the integral solution we will use a common threshold between the spectra.

## Exponential semigroups from the spectral theorem

If A is bounded below by a, then for nonnegative t the function lambda mapped to the exponential of negative t times lambda is bounded on the spectrum. The spectral calculus defines a bounded operator which we call the exponential of negative t A.

Its operator norm is at most the exponential of negative t times a. This is true even when A itself is unbounded.

Similarly, if B is bounded above by b, the exponential of t B is bounded for nonnegative t, with norm at most the exponential of t times b.

Take any bounded map C between the Hilbert spaces. The operator obtained by composing these two exponentials with C has norm at most the product of the three norms.

The result is at most the norm of C times the exponential of negative delta times t. Since delta is positive, this bound decays exponentially as t grows.

Integrating that scalar majorant from zero to infinity gives one divided by delta. Thus an integral built from these semigroups has a chance to produce a bounded Sylvester inverse with a constant exactly one over the ordered gap.

Notice a subtle point. The exponential of negative t A may grow with t if a is negative. The exponential of t B may also grow if b is positive. Their product still decays whenever a minus b is positive. Only the difference matters.

## Reading the hypotheses correctly

The lower form inequality belongs to A and its domain. The upper form inequality belongs to B and its domain. Their Hilbert spaces need not have equal dimensions, and they need not be the same space.

The gap condition concerns the operator parts after any spectral restriction has been made. If we replace A by a restriction to a reducing spectral subspace, we must verify that its actual spectral support still lies above a.

Likewise, if we compress an operator onto an arbitrary trial subspace, the resulting matrix may be bounded and self-adjoint but need not be a reducing restriction of the original unbounded operator. Those are different constructions.

For now we have established the form inequalities and a positive ordered gap that will control its inverse.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

If \(A\) is self-adjoint and \(\sigma(A)\subset[a,\infty)\), then \(\langle Ax,x\rangle\ge a\|x\|^2\) for \(x\in D(A)\). For \(B\) with \(\sigma(B)\subset(-\infty,b]\) and \(a>b\), the gap is \(\delta=a-b>0\). The spectral calculus yields \(\|e^{-tA}\|\le e^{-at}\), \(\|e^{tB}\|\le e^{bt}\), and \(\|e^{-tA}Ce^{tB}\|\le e^{-\delta t}\|C\|\) for \(t\ge0\). The quadratic form of a semibounded operator has a closed form-domain extension defined by its shifted square root; this is distinct from the domain of the operator itself.

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
