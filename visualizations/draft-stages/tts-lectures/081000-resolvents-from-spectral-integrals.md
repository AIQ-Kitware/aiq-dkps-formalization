# 081000 - Resolvents from spectral integrals

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `008000` resolvents, `031000` spectral separation, `075000-080000` spectral calculus and measurable restriction. **Next:** `082000` spectral approximation by cutoffs.

<!-- BEGIN SPOKEN LECTURE -->

# Resolvents from spectral integrals

For a diagonal matrix, taking an inverse is a coordinate-by-coordinate calculation. If a diagonal entry is three and we subtract a shift of one, the corresponding entry of the inverse is one half. Each coordinate is handled by taking the reciprocal of its shifted multiplier.

But many self-adjoint operators do not have a basis of eigenvectors. Some have continuous spectrum, where no individual eigenvector represents a spectral value. How can the same idea of taking reciprocals still work?

The spectral theorem provides an answer. It lets us treat a self-adjoint operator as multiplication by a spectral coordinate, even when that coordinate ranges continuously. A resolvent is then obtained by taking reciprocals inside a spectral integral.

This viewpoint explains three things: how the resolvent is constructed, why its norm measures the distance to the spectrum, and how a resolvent can reveal the distribution of spectral mass.

Throughout this recording, A is a bounded self-adjoint operator on a nonzero complex Hilbert space. Its spectrum is a nonempty compact set of real numbers. We use the convention that the resolvent at z is the inverse of A minus z times the identity.

## Start where the answer is visible

Take a diagonal matrix with entries negative two and three. Choose z equal to i, the imaginary unit.

Subtract i times the identity. The two diagonal entries become negative two minus i, and three minus i. Each is nonzero, so the resolvent exists. Its entries are their reciprocals.

The magnitudes of these reciprocal entries are one divided by the square root of five, and one divided by the square root of ten. The first is larger, so the norm of the resolvent is one over the square root of five.

Now look at the spectrum. It consists of the points negative two and three on the real axis. The point i is distance square root of five from negative two, and distance square root of ten from three.

So the resolvent norm is the reciprocal of the distance to the nearest spectral value.

The calculation suggests a general rule: if an operator behaves like multiplication by a number lambda, then A minus z behaves like multiplication by lambda minus z, and its inverse behaves like division by lambda minus z.

What we need is a replacement for the list of diagonal entries when the spectrum contains a continuum.

## Replace diagonal entries by spectral slices

Consider the Hilbert space of square-integrable functions on the interval from zero to one. Define A by multiplying a function by its input coordinate. At a point t, the output is t times the function's value there.

This operator is bounded and self-adjoint. Its spectrum is the whole interval from zero to one. There is no nonzero square-integrable eigenfunction concentrated at a single value of t, because one point has measure zero.

Nevertheless, we can isolate a band of spectral values. For example, we can keep the part of a function supported where t lies between one quarter and one half, and set the rest to zero.

That operation is an orthogonal projection. It is exactly the spectral projection associated with that interval.

For a general self-adjoint operator, a projection-valued measure plays the same role. To every suitable set of real spectral values it assigns an orthogonal projection onto the part of the Hilbert space carried by those values.

A spectral integral combines these projections, weighting each spectral slice by a scalar function of its spectral value. In the multiplication example, the construction simply multiplies the function at t by the chosen scalar function evaluated at t.

The spectral theorem says that A itself is obtained by weighting its spectral slices by lambda. More generally, a bounded continuous function g on the spectrum defines an operator called g of A. Products of scalar functions become products of operators, and the constant-one function becomes the identity.

That product rule is what makes inversion possible.

## Taking the reciprocal

Choose a complex number z outside the spectrum. On the spectrum, the scalar function that divides one by lambda minus z never has a zero denominator.

Because the spectrum is compact, the reciprocal function is bounded and continuous there. We can therefore form its operator through the spectral calculus.

Now multiply the reciprocal function by lambda minus z. The product equals one at every spectral value. The functional calculus carries that scalar identity into an operator identity.

So the operator formed from the reciprocal function undoes A minus z times the identity, in either composition order. It is the resolvent.

In the language of spectral integrals, the resolvent is the integral of the reciprocal of lambda minus z against the projection-valued spectral measure.

This is precisely the same calculation as inverting a diagonal matrix, except that the diagonal entries have been replaced by a continuum of spectral values and a corresponding family of projections.

Return to the multiplication operator on square-integrable functions. Its resolvent at z divides a function's value at t by t minus z. If z lies outside the interval from zero to one, the denominator stays a positive distance from zero and this division is bounded.

No eigenvectors were required to perform that calculation.

## Why distance gives the norm

Let d be the distance from z to the spectrum. Because z lies outside the compact spectrum, d is positive.

Every spectral denominator, lambda minus z, has absolute value at least d. Its reciprocal has absolute value at most one over d. Therefore the resolvent norm is at most one over d.

Why is the estimate exact?

There is at least one spectral value nearest z, because the spectrum is compact. In a neighborhood of that value, the reciprocal multiplier is as large as we wish, up to the maximum one over d. The spectral theorem guarantees nonzero spectral content in every neighborhood of a spectral point. We can choose unit vectors concentrated in such a neighborhood to obtain outputs arbitrarily close to that maximum size.

Thus the norm is at least one over d as well. We have equality: for a bounded self-adjoint operator, resolvent norm equals one divided by distance to spectrum.

This equality extends to normal operators, for which the spectral calculus is still governed by scalar multiplication. It can fail for nonnormal operators, whose inverse may grow substantially even away from eigenvalues.

The formula also explains what happens near an isolated spectral point. In our diagonal matrix, move z toward negative two along a vertical line in the complex plane. If z is negative two plus i times eta, with eta positive, the nearest spectral distance is eta. The resolvent norm is one over eta. It becomes large as eta approaches zero.

## Where do approximate eigenvectors come from?

The spectral-integral picture gives a way to understand why a spectral point need not be an eigenvalue.

Take a real number c in the spectrum. Every narrow interval around c has a nonzero spectral projection. Choose a unit vector supported in that spectral slice.

When we apply A minus c times the identity, every multiplier on that slice has absolute value no larger than the width of the interval. The output norm is therefore at most that width.

As we shrink the interval, we obtain unit vectors for which A minus c times the identity produces arbitrarily small outputs. These are approximate eigenvectors.

If the shifted operator had a bounded inverse, it could not shrink unit vectors arbitrarily close to zero. So c belongs to the spectrum whether or not an exact eigenvector exists.

The multiplication operator on square-integrable functions gives a picture you can keep in mind: concentrate a normalized function on a narrower and narrower interval around c. Multiplication by t then acts more and more like multiplication by c.

## A scalar resolvent can reveal a measure

Now fix one vector x in the Hilbert space. The spectral projections tell us how much of x lies in each spectral band. That information defines a positive scalar measure, often called the spectral measure of x.

If x is a normalized eigenvector with eigenvalue c, all of its spectral mass sits at c. For the multiplication operator, a general square-integrable function spreads its spectral mass across the interval, weighted by the square of its magnitude.

Take the inner product of x with the resolvent applied to x. The result is a complex number. In the spectral calculus it equals the integral of one divided by lambda minus z against the spectral measure of x.

This scalar function of z is a Cauchy transform, also called a Stieltjes transform with the present sign convention.

To see why it is informative, take z with real part u and positive imaginary part eta. The imaginary part of the reciprocal of lambda minus u minus i eta equals eta divided by the sum of the square of lambda minus u and eta squared.

That expression is nonnegative. It is largest when lambda is near u, and becomes more concentrated near u as eta decreases. The imaginary part of our scalar resolvent is the integral of this concentrated kernel against the spectral measure.

The kernel has total area pi when integrated along the real line in u. Consequently, if we integrate the imaginary part of the scalar resolvent over a real interval, divide by pi, and let eta approach zero, we recover the spectral measure of that interval, provided its endpoints carry no atoms. Other endpoint cases have the corresponding half-weight corrections.

So the resolvent does more than report where the spectrum is. Its behavior near the real axis contains information about how a vector's spectral mass is distributed.

## Compare two nearby shifts

The same reciprocal picture explains an important algebraic identity. Subtract the reciprocal of lambda minus w from the reciprocal of lambda minus z. The numerator is z minus w, and the denominator is the product of the two shifted factors.

Apply the functional calculus. The resolvent at z minus the resolvent at w equals z minus w times the product of those two resolvents.

This resolvent identity controls how the inverse changes as the shift moves. Wherever both shifts remain a positive distance from the spectrum, their resolvents stay bounded and close shifts give close resolvents.

The dependence on z is in fact complex analytic away from the spectrum. That additional structure underlies contour formulas for isolated spectral projections.

## A glimpse of the unbounded case

One might expect an unbounded self-adjoint operator to have only unbounded inverses. The spectral integral shows why that expectation is false.

For a nonreal shift z, every real lambda is at least the absolute value of the imaginary part of z away from z. Therefore the reciprocal of lambda minus z is bounded, even if lambda ranges across the entire real line.

An unbounded operator requires a proper domain, and we must still establish that the inverse maps into that domain. The reciprocal formula supplies the right candidate, and the spectral theorem provides the domain argument.

The same picture survives: the resolvent is a bounded operator obtained by taking reciprocals of shifted spectral multipliers.

## The central connection

For a diagonal matrix, inversion means taking a reciprocal at each eigenvalue. For a general self-adjoint operator, spectral integration replaces the diagonal coordinates. The reciprocal becomes a function on the spectrum, and the spectral calculus turns that function into the resolvent.

From this one construction we obtain the exact inverse-distance norm formula, approximate eigenvectors near spectral points, and a scalar transform that reveals spectral mass.

For a final check, imagine moving the point z vertically toward the spectrum of the matrix with entries negative two and three. Explain why the inverse grows like one over the height above negative two. Then ask how the same idea works when the eigenvalues have been replaced by every number in an interval. The spectral integral is the answer.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

With `A = A*` bounded and `z` in the complex resolvent set, `R_A(z) = (A - z I)^(-1) = integral (lambda - z)^(-1) dE(lambda)`, and `||R_A(z)|| = 1 / dist(z,spectrum(A))` on a nonzero Hilbert space. For a scalar spectral measure `mu_x`, `<x,R_A(z)x> = integral (lambda-z)^(-1) d mu_x(lambda)`. For \(z=u+i\eta\) with \(\eta>0\), the imaginary part of the scalar transform has kernel \(\eta/((\lambda-u)^2+\eta^2)\); integrating over an interval and dividing by \(\pi\) recovers its measure in the \(\eta\to0^+\) limit when the endpoints have zero mass. The source formalizes inverse-distance *upper bounds* for bounded self-adjoint resolvents and resolvent identities; the full equality and scalar-transform interpretation here are derived mathematically, not attributed to those specific theorem headers.

**Lean bridge (verbatim source declaration headers).**

`DavisKahan/SpectralTheory/ResolventOperator.lean` - `resolvent_identity`:

```lean
theorem resolvent_identity
    (A : E →L[𝕜] E) {z w : 𝕜}
    (hz : InResolventSet A z) (hw : InResolventSet A w) :
    resolventOperator A z - resolventOperator A w =
      (z - w) • (resolventOperator A z ∘L resolventOperator A w) :=
```

This module defines its bounded resolvent as the inverse of `A - z I`; the displayed identity uses that sign convention.

`DavisKahan/SpectralTheory/ResolventOperator.lean` - `complex_inResolventSet_and_norm_resolvent_le_inv_distance`:

```lean
theorem complex_inResolventSet_and_norm_resolvent_le_inv_distance
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (z : ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ lam ∈ realSpectrum A, delta ≤ ‖z - (lam : ℂ)‖) :
    InResolventSet A z ∧ ‖resolventOperator A z‖ ≤ delta⁻¹ :=
```

For symmetric bounded complex operators, a positive lower bound `delta` on spectral distance yields resolvent-set membership and the norm upper bound `delta^-1`.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` - `spectralPVM_resolvent_formula`:

```lean
theorem spectralPVM_resolvent_formula (hzr : z ∈ resolventSet A) (ξ : H) :
    ⟪ξ, resolvent A z ξ⟫_ℂ
      = ∫ s, (z - (s : ℂ))⁻¹ ∂((spectralPVM hA).diag ξ) :=
```

This theorem concerns an unbounded self-adjoint operator and uses the separate convention `resolvent A z = (z I - A)^-1`, so its integrand is `(z-lambda)^-1`, the negative of the bounded resolvent convention used in this lecture. Do not identify the two without a minus sign.

**Scope:** The excerpts are declaration headers, not complete proof bodies. Their enclosing modules supply scalar types, normality/self-adjointness assumptions, and typeclass instances. The prose derives the mathematical statements and does not claim that all of the pedagogical arguments have separate local Lean theorems.
