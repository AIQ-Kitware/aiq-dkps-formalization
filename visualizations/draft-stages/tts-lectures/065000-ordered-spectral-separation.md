# 065000 — Ordered spectral separation

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `031000` ordered versus distance gaps; `039000–040000` exponentials; `063000–064000` Sylvester solutions. **Next:** unitary and semigroup representations.

<!-- BEGIN SPOKEN LECTURE -->

# A spectral gap that makes the solution decay

We now know that different eigenvalues make the Sylvester equation invertible. But knowing an inverse exists does not tell us how large that inverse is. Today a stronger hypothesis will give a particularly clean result.

Suppose A and B are self-adjoint, and every spectral value of A lies at least delta above every spectral value of B, where delta is positive. This is ordered spectral separation. Under that hypothesis, the solution of A X minus X B equals C can be written as an integral of decaying exponentials, and its operator norm is at most the norm of C divided by delta.

The constant one in that bound will come directly from integrating a decaying scalar exponential.

## What ordered separation says

Imagine the real number line. Put the spectrum of B entirely to the left. Leave an empty interval of positive length delta. Then put the spectrum of A to the right.

For example, B may have eigenvalues zero and one, while A has eigenvalues three and five. The smallest difference between an eigenvalue of A and an eigenvalue of B is two. So we can take delta equal to two.

The condition is stronger than the assertion that the spectra do not overlap. If A has eigenvalues negative three and positive three, while B has eigenvalue zero, the spectra are separated by distance three, but A lies on both sides of B. The ordered condition fails.

Why should order make a difference? Because it gives the spectral differences a consistent sign. We can represent the reciprocal of every positive difference by the same convergent integral.

## The scalar integral behind the proof

Take real numbers a and b with a greater than b. Consider the scalar function of time that is the exponential of negative t times a minus b.

As time increases, this function decays. Integrating from zero to infinity gives one divided by a minus b.

We can prove it without quoting an integral table. The derivative of the exponential of negative t times the difference is negative that difference times the same exponential. Divide by the difference and evaluate the antiderivative between zero and a large time T. The upper endpoint goes to zero, leaving the reciprocal.

This is exactly the denominator we encountered in the diagonal Sylvester formula. Instead of dividing each matrix entry separately, we will build an operator-valued integral that performs all of those divisions simultaneously.

## Two exponentials, one Sylvester solution

Let A act on an output Hilbert space and B act on an input Hilbert space. Both are bounded and self-adjoint. Let C map the input space to the output space.

For nonnegative time t, form the operator obtained by applying the exponential of negative t A, then C, then the exponential of positive t B. Call this the integrand.

If A and B are diagonal, the coefficient between eigenvalues a and b is the original coefficient of C times the exponential of negative t times a minus b. Integrating that coefficient gives the coefficient of C divided by a minus b.

Thus the integral recreates the entrywise solution from the previous lecture. But it has two advantages. It does not require a preferred basis, and the norm of each factor can be bounded using the spectral order.

## Find a common spectral cut

Because the spectra are compact in the bounded self-adjoint setting, there is a real number c such that all spectral values of B are at most c, while all spectral values of A are at least c plus delta.

For our example, take c equal to one. B lies at or below one. A lies at or above three. Since delta is two, the required difference is exact.

For nonnegative time, the norm of the exponential of negative t A is at most the exponential of negative t times c plus delta. That is because the spectrum of the exponential consists of the exponentials of the original spectral values, and the largest such value corresponds to the smallest eigenvalue of A.

Similarly, the norm of the exponential of positive t B is at most the exponential of t times c.

Multiply the two bounds. The factors involving c cancel. What remains is the exponential of negative delta times t.

Using the product estimate for operator norms, the norm of our integrand is at most the exponential of negative delta times t, multiplied by the norm of C.

This is the central estimate. The same spectral gap that appears in the denominator of the solution controls the rate of decay of the integrand.

## Integrate the norm bound

Since delta is positive, the exponential of negative delta times t is integrable over nonnegative times. Its integral is one over delta.

The norm of an operator-valued integral is at most the integral of the operator norms. Therefore the norm of the proposed solution is at most the norm of C divided by delta.

This statement is independent of the dimension. Nothing in the decay estimate counts eigenvectors or matrix entries. It works on infinite-dimensional Hilbert spaces as long as A and B are bounded self-adjoint operators and the ordered separation holds.

We also obtain convergence of the integral. The scalar exponential provides an integrable dominating function. In a complete normed space of bounded operators, the integral therefore defines a bounded operator.

## Verify the equation by differentiation

We should not trust an integral formula merely because it works on diagonal matrices. Let us prove that it solves the operator equation.

Call the integrand F of t. Differentiate the exponential on the left. This contributes negative A times F. Differentiate the exponential on the right. This contributes F times B. The generators commute with their own exponentials, so the derivative is negative A F plus F B.

Equivalently, A F minus F B equals negative the derivative of F.

Now integrate both sides over time from zero to a large T. The Sylvester operator can pass through the integral because composition by bounded operators is continuous and linear. We obtain A X at time T minus X at time T B equal to F at zero minus F at T.

At time zero, both exponentials are identities, so F at zero is C. As T tends to infinity, the norm of F at T goes to zero by our exponential decay bound. The equation therefore becomes A X minus X B equals C.

This proves existence. For uniqueness, suppose a second solution exists. Their difference solves the homogeneous equation. Repeat the same orbit argument with C equal to zero. The orbit is constant because its derivative vanishes, but the decay estimate forces that constant to be zero. Hence the two solutions coincide.

## A numerical check

Return to A diagonal with entries three and five and B diagonal with entries zero and one. Let C be the two-by-two matrix whose entries are all one.

Every coefficient of the solution is the corresponding coefficient of C divided by its spectral difference.

The first row is one third and one half. The second row is one fifth and one fourth. We can check the first row: multiplying by A gives one and three halves; multiplying on the right by B gives zero and one half; subtraction yields one and one.

The second row works the same way: five times one fifth is one, and five times one fourth minus one fourth is one.

The smallest gap is two, so our general conclusion is that the operator norm of X is at most half the operator norm of C. We do not need to compute the singular values of X to know that bound.

## Sharpness and reversed order

The constant one is optimal. Take one-dimensional spaces. Let A multiply by delta, B multiply by zero, and C multiply by one. Then X multiplies by one over delta, so the bound is an equality.

If the order is reversed, with A entirely below B, we can exchange the direction of time and the sign of the formula, or apply the result after swapping A and B. The same norm estimate holds. What matters is consistent ordering, not which operator is above.

Finally, be careful about hypotheses. The exact decay proof used self-adjoint functional calculus and a common ordered cut. Mere nonoverlap of spectral sets does not provide the same semigroup estimate.

Reconstruct the scalar integral first, then the two exponential bounds, then the derivative identity. Those three steps give the existence, uniqueness, and constant-one estimate. In the next lecture we will replace decay by oscillation and see what remains when the spectral sets are separated but interlaced.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

If \(A=A^*\), \(B=B^*\), and \(\inf\sigma(A)-\sup\sigma(B)\ge\delta>0\), then
\[
X=\int_0^\infty e^{-tA}Ce^{tB}\,dt,\qquad AX-XB=C,
\qquad \|X\|\le \frac{\|C\|}{\delta}.
\]
Indeed, choosing \(c\) with \(\sigma(B)\subset(-\infty,c]\) and \(\sigma(A)\subset[c+\delta,\infty)\),
\[
\|e^{-tA}Ce^{tB}\|\le e^{-\delta t}\|C\|.
\]
The formula is a Bochner integral in the bounded-operator Banach space; it extends to compatible operator ideals under the ideal norm estimates.

**Lean bridge (verbatim source excerpts).**

`DavisKahan/InfiniteDimensional/Sylvester/OrderedSemigroup.lean` — `orderedSemigroup_integrand_bound`:

```lean
theorem orderedSemigroup_integrand_bound
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (C : E →L[ℂ] F) :
    ∀ t ≥ 0,
      ‖semigroup (-A) t ∘L C ∘L semigroup B t‖ ≤
        Real.exp (-d * t) * ‖C‖ := by
```

Here `OrderedSpectraSeparated B ⊤ A ⊤ d` orders the right-block spectrum below the left-block spectrum. The conclusion is the exponential envelope in operator norm.

`DavisKahan/InfiniteDimensional/Sylvester/OrderedSemigroup.lean` — `orderedSylvester_reconstruction`:

```lean
theorem orderedSylvester_reconstruction
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    {X C : E →L[ℂ] F}
    (hEq : A ∘L X - X ∘L B = C) :
    X = ∫ t : ℝ, Set.indicator (Set.Ici 0)
      (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) t := by
```

This proves the integral formula for an **already given** solution under bounded self-adjoint operators. The spoken derivation separately shows existence and uniqueness by differentiating the candidate integral and the homogeneous orbit.

