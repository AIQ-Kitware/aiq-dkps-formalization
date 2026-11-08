# 075000 — Continuous functional calculus and C-star identities

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `025000–026000` finite self-adjoint spectral theorem; `032000–035000` finite functional calculus and square roots; `072000–074000` infinite-dimensional Hilbert and measure foundations. **Next:** `076000` projection-valued measures.

<!-- BEGIN SPOKEN LECTURE -->

# Defining a function of an operator without diagonalizing it

Suppose A is a bounded self-adjoint operator on an infinite-dimensional Hilbert space. In finite dimensions, we could diagonalize A and apply a function to its eigenvalues. But multiplication by the coordinate on square-integrable functions over the unit interval has continuous spectrum and no nonzero eigenvectors at all.

We still want to make sense of A squared, the exponential of A, the square root of a positive A, and eventually the indicator of a spectral interval. Polynomial approximation provides the continuous functional calculus for bounded self-adjoint operators.

The central idea is to begin with expressions we already know how to evaluate, then use operator-norm limits. A special norm identity, called the C-star identity, ensures the construction is stable.

## Polynomial functions of an operator

For a polynomial p, there is no ambiguity about p of A. Replace the scalar variable by A, replace the constant one by the identity operator, and use operator composition for multiplication.

For example, if p of x equals x squared minus three x plus two, then p of A equals A composed with A, minus three times A, plus two times the identity.

Polynomial evaluation respects addition and multiplication. The product of two polynomial expressions becomes the product of their operator values because every power of the same operator commutes with every other power.

If A is self-adjoint, the adjoint of p of A corresponds to conjugating the polynomial coefficients. In particular, a real-coefficient polynomial gives another self-adjoint operator.

The challenge is to assign an operator to a continuous function that is not a polynomial, and to prove that different approximating polynomials lead to the same result.

## The spectrum as the correct domain

A bounded self-adjoint operator has a nonempty compact spectrum contained in the real line, apart from the trivial zero-dimensional edge case. Call this compact set K.

Our continuous function f need only be defined on K. We do not need to choose an arbitrary extension to the whole real line.

Why is K enough? Polynomials evaluated at A cannot distinguish two scalar polynomials that agree on the spectrum. The precise statement comes from the spectral norm formula: for a polynomial p and self-adjoint A, the operator norm of p of A is the maximum of the absolute value of p over K.

We can derive the key estimate through the C-star identity, then the spectral radius of a normal operator. For normal operators, spectral radius equals operator norm. Polynomial evaluation preserves spectral values, so the spectral radius of p of A is the largest absolute value of p on K.

This equality is far stronger than a bound obtained by summing the magnitudes of polynomial coefficients. It says the operator-norm size of p of A is controlled exactly by the size of the scalar function on the spectrum.

## The C-star identity

For any bounded operator T on a Hilbert space, its adjoint times itself is positive. Consider its operator norm. By the definition of an adjoint, the squared length of T applied to x equals the inner product of T adjoint T applied to x with x.

This gives the inequality that the norm of T squared is at most the norm of T adjoint T. The reverse inequality follows from submultiplicativity: the norm of T adjoint T is at most the product of the norms of T adjoint and T, which are equal.

Thus the norm of T adjoint T equals the square of the norm of T.

This is the C-star identity. It ties multiplication, adjoints, and norms together. Ordinary normed algebras need not satisfy it, so it is a structural property of bounded operators on Hilbert space and of more general C-star algebras.

For a normal operator N, the identity helps show that its norm equals its spectral radius. Repeatedly apply the identity to powers of N and combine it with the spectral radius formula. That argument supplies the exact norm equality needed for functional calculus.

## From polynomials to continuous functions

A classical approximation theorem says that on a compact subset of the real line, every continuous complex-valued function can be uniformly approximated by complex polynomials. One route is to extend the function to a compact interval, approximate its real and imaginary parts there, and restrict back to K.

Choose polynomials p-one, p-two, and so forth that converge uniformly to f on K.

The spectral norm formula says the operator norm of p-n of A minus p-m of A equals the maximum of the absolute value of p-n minus p-m on K. Since our polynomial sequence is uniformly Cauchy, the corresponding operator sequence is Cauchy in operator norm.

Bounded operators on a Hilbert space form a complete normed algebra. Thus the operators p-n of A converge in operator norm to a bounded operator. Define this limit to be f of A.

If we chose a different approximating polynomial sequence, the same norm formula applied to the difference shows that both operator limits agree. So the definition is independent of the approximation.

## Algebraic laws survive the limit

Because operator addition, multiplication, scalar multiplication, and adjoints are continuous in operator norm, their polynomial identities pass to continuous functions.

Consequently, the function constantly equal to one gives the identity operator. The function x gives A. Addition and multiplication of functions become addition and composition of their operator values. Complex conjugation of the symbol becomes taking the adjoint.

This collection of properties makes functional calculus a unital star-algebra homomorphism from the continuous functions on K into the bounded operators.

It is also isometric: the operator norm of f of A equals the supremum of the absolute value of f on K. Prove this by taking the operator-norm limit of the exact polynomial norm formula.

In particular, if two continuous functions agree on K, they produce the same operator. And if their operator values agree, the isometry says the two functions must agree on K.

## Spectral mapping and invertibility

What is the spectrum of f of A? It is exactly the set of values f takes on K.

Here is the mechanism. If a complex number z is not attained by f on K, the function one divided by f minus z is continuous on K. Functional calculus turns it into a bounded inverse for f of A minus z times the identity.

Conversely, suppose z equals f of lambda for some lambda in K. Since A is self-adjoint, a spectral point lambda admits unit approximate eigenvectors: vectors whose images under A minus lambda approach zero. To see why, if A minus lambda were bounded below, it would have closed range; self-adjointness would make that range dense, hence all of the space, producing a bounded inverse and contradicting lambda in the spectrum.

For a polynomial p, factor p of x minus p of lambda by x minus lambda. Therefore the same unit vectors approximately satisfy p of A times the vector equals p of lambda times the vector. Uniformly approximate f by polynomials and use the operator-norm estimate to pass to f. The images under f of A minus z then tend to zero, so that operator cannot be boundedly invertible. Thus z lies in its spectrum.

This result is the spectral mapping theorem. It generalizes the elementary finite statement that applying f to a diagonal matrix applies f to each diagonal eigenvalue.

The argument uses the full spectrum, not merely the list of eigenvalues. That distinction is indispensable for the multiplication operator whose spectrum is an interval but whose eigenvalue list is empty.

## Positivity and square roots

A self-adjoint operator A is positive if its quadratic form is nonnegative on every vector. Equivalently, its spectrum lies in the nonnegative real numbers.

If a continuous real function f is nonnegative on K, functional calculus gives a positive operator f of A. One way to see this is to take the continuous square root of f. Its functional-calculus value B satisfies B adjoint B equals f of A. Such an operator has nonnegative quadratic form.

For positive A, choose the function square root of x on K. Its value is the positive square root of A. This is the infinite-dimensional extension of our finite spectral construction, and the uniqueness argument uses positivity and commutation properties of functional calculus.

As a check, take the multiplication operator M on L two of the unit interval. The operator square root of M multiplies a function by the scalar square root of x. Squaring that operator returns multiplication by x, just as expected.

## Uniform approximation has a boundary

Can we now construct the projection selecting values of A below one half? Its scalar symbol is the indicator of the interval below one half. On a spectrum containing points on both sides of that threshold and accumulating at the threshold, this indicator is discontinuous.

A uniform limit of continuous functions is continuous. Therefore no uniformly convergent polynomial sequence on that spectrum can represent this indicator.

There may be ways to approximate the indicator pointwise or in an integrated sense. But those are different modes of convergence. In the multiplication model, continuous approximations can converge strongly as operators even when they cannot converge in operator norm.

This is the passage from continuous functional calculus to Borel functional calculus. We need measures and projection-valued measures to integrate bounded measurable symbols and control strong limits.

## The bridge to spectral measures

Continuous functional calculus already lets us express a bounded self-adjoint operator as a function of its spectrum, even when there are no eigenvectors. It gives exact norm control, multiplication, adjoints, positivity, and spectral mapping.

The next step is to replace continuous scalar functions by bounded Borel functions. Indicators then become spectral projections. We will prove how those projections add over countably many disjoint sets and why their convergence is strong rather than uniformly in operator norm.

We are now ready to reconstruct the infinite-dimensional spectral theorem in the language appropriate to actual spectral subspaces.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a bounded self-adjoint \(A\) on a complex Hilbert space, with real compact spectrum \(K=\sigma(A)\subset\mathbb R\), continuous functional calculus is a unital \(*\)-homomorphism
\[
C(K,\mathbb C)\longrightarrow\mathcal B(H),\qquad f\mapsto f(A),
\]
with \(\|f(A)\|=\sup_{\lambda\in K}|f(\lambda)|\), \(\sigma(f(A))=f(K)\), and \(\overline f(A)=f(A)^*\). For nonnegative \(f\), \(f(A)\ge0\).

The source's `realSpectrumCfcHom` transports Mathlib's existing continuous \(*\)-algebra calculus to symbols on the real spectrum. The construction in this lecture is a mathematical derivation, not a claim that the repository re-proves the general Stone–Weierstrass or C-star identity libraries.

**Lean bridge (verified source excerpts).**

`ForTauCeti/Analysis/CStarAlgebra/RealSpectrumFunctionalCalculus.lean` — `realSpectrumCfcHom` (exact source declaration header):

```lean
noncomputable def realSpectrumCfcHom {a : A} (ha : IsSelfAdjoint a) :
    C(spectrum ℝ a, ℂ) →⋆ₐ[ℂ] A :=
```

The definition transports Mathlib continuous functional calculus from the complex spectrum to complex-valued continuous symbols on the real spectrum of a self-adjoint element.

`ForTauCeti/Analysis/CStarAlgebra/RealSpectrumFunctionalCalculus.lean` — `realSpectrumCfcHom_map_spectrum` (exact source declaration header):

```lean
theorem realSpectrumCfcHom_map_spectrum {a : A} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℂ)) :
    spectrum ℂ (realSpectrumCfcHom ha f) = Set.range f := by
```

This is the spectral mapping theorem for the transported complex-valued calculus.

`ForTauCeti/Analysis/CStarAlgebra/RealSpectrumFunctionalCalculus.lean` — `continuous_realSpectrumCfcHom` (exact source declaration header):

```lean
theorem continuous_realSpectrumCfcHom {a : A} (ha : IsSelfAdjoint a) :
    Continuous (realSpectrumCfcHom ha) :=
```

This confirms continuity of the transported calculus, obtained from the existing continuous calculus.
