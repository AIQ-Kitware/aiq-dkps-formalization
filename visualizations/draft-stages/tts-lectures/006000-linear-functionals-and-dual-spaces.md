# Linear functionals and dual spaces

<!-- BEGIN SPOKEN LECTURE -->

A linear functional maps vectors to scalars while preserving addition and scalar multiplication. Instead of producing another vector, it returns one number. Continuous linear functionals let us measure vectors using the language of linear maps.

This might sound like a small change, but it gives us a new way to study a space. Instead of asking what an operator does to every vector, we can ask what can be detected by numerical measurements of those vectors. Many operator proofs eventually reduce an abstract claim to inequalities about real or complex numbers. Linear functionals are one of the main ways to make that reduction.

## Measuring a vector with a number

In the plane, consider the rule that takes a vector, doubles its horizontal coordinate, and subtracts its vertical coordinate. The output is one number. The rule is linear: it preserves sums and scaling.

Geometrically, imagine moving along a line where twice the horizontal coordinate minus the vertical coordinate stays constant. Every point on that line receives the same measurement. The functional does not remember the whole vector; it extracts one particular feature.

Any linear functional on an ordinary finite-dimensional real vector space can be described by a row of coefficients once we choose coordinates. For a vector with three coordinates, one functional might return the first coordinate plus twice the second minus four times the third. This is the usual dot-product formula with a fixed row of numbers.

But the functional, like any other linear map, exists independently of that coordinate description. And we can apply the same idea to spaces whose vectors are entire functions.

## Two function-space examples

Let E be the space of continuous real-valued functions on the interval from zero to one, with the maximum norm. A vector in E is a whole function.

The first functional evaluates a function at one half. It returns the height of the function at the midpoint of the interval. This rule is linear, because evaluating a sum gives the sum of the evaluations, and evaluating a scalar multiple pulls out the scalar.

It is also bounded. The absolute value of a function at the midpoint cannot exceed the largest absolute value of the function anywhere on the interval. So the evaluation functional has norm at most one. The constant function whose value is one everywhere shows that the norm is exactly one.

The second functional takes a function and integrates it from zero to one. Integration is linear. The absolute value of the integral is no greater than the integral of the absolute value, which is at most the maximum norm times the length of the interval. Here the interval has length one. Again, the functional norm is at most one, and the constant function one shows equality.

These two functionals extract quite different information. One samples a point; the other averages over the interval. Nevertheless, both obey the same boundedness estimate, and the same theory applies to both.

## Why boundedness matters again

We will call a bounded linear functional a continuous linear functional. For any linear map between normed spaces, continuity is equivalent to the existence of a constant bounding its output norm by that constant times the input norm.

To see why we must retain that qualification, return to the space of polynomials on the interval from zero to one, still with the maximum norm. Define a functional that takes a polynomial and reports its derivative at zero.

It is linear. But is it bounded? Consider the polynomial obtained by taking one minus x to the power n. Its maximum absolute value on our interval is one. Its derivative at zero is negative n, whose absolute value grows without bound.

So this perfectly well-defined linear functional is not continuous in the maximum norm. We cannot estimate its output by one fixed multiple of its input norm.

This example explains why the continuous dual is the right collection for analysis. When inputs are known only approximately in norm, a continuous functional gives a controlled approximation to its numerical measurement.

## Building the dual space

The continuous dual of E is the set of all continuous linear functionals from E to the scalar field. For real spaces the outputs are real numbers; for complex spaces they are complex numbers. We can add functionals, scale them, and define their operator norm exactly as before.

The dual norm is the greatest absolute output obtainable from an input of norm at most one. Equivalently, it is the smallest constant that controls the output's absolute value by that constant times the input norm.

For a finite-dimensional real Euclidean space, a functional is represented by a fixed coefficient vector. Cauchy–Schwarz says that the absolute dot product with an input is at most the coefficient vector's Euclidean length times the input's length. Taking the input parallel to the coefficient vector achieves equality, unless the coefficient vector is zero. Thus the dual norm is exactly the Euclidean norm of those coefficients.

This is a useful model, but do not assume every dual space comes with a coordinate vector of the same sort. We have not yet introduced the inner-product structure needed to identify a functional with a vector. That identification, in Hilbert spaces, is the Riesz representation theorem, and it deserves its own proof later.

Here is another structural fact. The continuous dual of any normed space is complete, even if the original space is not. To see the mechanism, take a Cauchy sequence of functionals in the dual norm. At each fixed input, their values form a Cauchy sequence of scalars, which has a limit. Those limits define a linear functional. The dual-norm Cauchy bound passes to the limit and shows that the new functional is bounded, and that the original sequence converges to it in dual norm. This is the same construction we used to prove completeness of bounded operator spaces, with the scalar field as the output space.

## Extending a measurement

Suppose a linear functional is known only on a subspace. Can we extend it to the whole space without allowing its norm to increase?

The Hahn–Banach theorem says yes, over the real numbers, for a bounded linear functional on a subspace of a real normed space. There is a complex version as well. The statement may sound technical, so let's unpack the difficulty.

Imagine the functional is currently defined on a line inside the plane. We know what it measures along that line. To extend it to the plane, we must decide what number it assigns to one new direction. Once that number is fixed, linearity determines the value on every combination of the old line and the new direction.

But we cannot choose that number arbitrarily if we want to preserve the same bound. Every vector formed by combining an old vector with the new direction imposes an upper or lower restriction on the unknown value. The proof needs to show those restrictions are compatible.

Here is the crucial step in words. Assume the old functional never exceeds the norm of its input. Pick a vector v outside the old subspace and call the value we want to assign to v, a. For any old vector m, the rule for the extended functional says the value on m plus v must be the old value at m plus a. To stay below the norm, a must be no greater than the norm of m plus v, minus the old value at m.

Now perform the same check using m minus v. It produces a lower bound on a: the old value at m, minus the norm of m minus v. The new value a must satisfy all such lower bounds and all such upper bounds at once.

Why is that possible? Compare any one lower bound with any one upper bound. Add the corresponding old vectors. Linearity of the old functional gives its value on that sum. Its assumed norm bound and the triangle inequality show that this lower bound cannot exceed that upper bound. Therefore the largest allowed lower threshold is no greater than the smallest allowed upper threshold. Choose a between them.

We have extended the functional by one direction without losing the norm bound. For a finite-dimensional space, repeat this step finitely many times to extend from a subspace to the whole space.

For a general infinite-dimensional space, infinitely many extension steps require an additional maximal-extension argument, usually formulated using Zorn's lemma. We have just proved the essential one-direction mechanism; a fully detailed treatment of that maximality principle belongs in our later foundational proof work. We should not confuse this argument with a complete proof of the infinite-dimensional theorem.

## Why this tool will return

Hahn–Banach allows us to extend numerical measurements from a subspace while controlling their norm. One consequence is that bounded linear functionals can distinguish a nonzero vector from zero. Another is that, for a continuous seminorm, we can sometimes select a functional that exactly witnesses the size of a particular vector.

That witness is useful in the formalized operator theory. For example, a later argument bounds the size of an operator-valued integral under a Ky Fan gauge. A well-chosen functional turns the gauge estimate into a scalar integral estimate, where ordinary inequalities can finish the job. The necessary extension step is precisely the kind of operation Hahn–Banach supplies.

For now, the reconstruction questions are simpler. Can you prove the midpoint evaluation functional has norm one? Can you explain why differentiation at a point fails to be bounded on our polynomial space? And can you derive the upper and lower restrictions that allow a functional to be extended by one new direction?

We have learned that a dual space is a space of controlled numerical measurements, not merely a list of row vectors. This gives us a second perspective on a normed space: through the points it contains, and through the bounded linear functionals that observe those points.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

The continuous dual is \(E^*=\mathcal B(E,\mathbb K)\), where \(\mathbb K\in\{\mathbb R,\mathbb C\}\) is the scalar field. For \(\varphi\in E^*\), \(\|\varphi\|=\sup_{\|x\|\le1}|\varphi(x)|\). Every continuous dual is Banach. Real Hahn–Banach (norm form): if \(M\subseteq E\) is a linear subspace and \(f:M\to\mathbb R\) is bounded and linear, there is a bounded linear \(F:E\to\mathbb R\) extending \(f\) with \(\|F\|=\|f\|\). The spoken lecture develops the one-dimensional extension argument and does **not** present the infinite-dimensional maximal-extension argument as completed.

**Lean bridge.** In `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFanBochner.lean`, the DKPS development applies a Hahn–Banach extension theorem in the proof of a Bochner-integral inequality:

```lean
  obtain ⟨g, hgext, hgle⟩ :=
    Module.Dual.exists_extension_of_le_seminorm (Submodule.span 𝕜 {v}) g₀ hg₀
  have hφbound : ∀ x, ‖g x‖ ≤ C * ‖x‖ := fun x => (hgle x).trans (hC x)
  set φ : X →L[𝕜] 𝕜 := g.mkContinuous C hφbound with hφ_def
```

`Module.Dual` expresses the algebraic linear functional; `exists_extension_of_le_seminorm` extends one while retaining a seminorm bound. `mkContinuous` promotes the resulting bounded functional to a continuous linear map, here with target the scalar field. The `p` of the surrounding theorem is a Ky Fan gauge; that later construction is not needed to understand the extension mechanism.

**Provenance and validation.** The application is from the DKPS `ForTauCeti` source snapshot (2026-11-07), with a provenance header identifying earlier DKPS donor material. The general Hahn–Banach extension result is imported from Mathlib. This excerpt was verified as source text, not compiled as a new Lean file.
