# 032000 — Coordinate-free finite functional calculus

**Draft status:** audio-first mathematical lecture. **Prerequisites:** finite spectral theorem, polynomial functions, spectral projections, and self-adjoint matrices. **Next:** quadratic-form order and positive operators.

<!-- BEGIN SPOKEN LECTURE -->

# What does it mean to apply a function to a matrix?

We know how to square a matrix. We multiply it by itself. We know how to form a polynomial in a matrix: take combinations of its powers and the identity.

But what could the square root of a matrix mean? Or the exponential? Or even a function that is one on some eigenvalues and zero on others?

It would be easy to misunderstand the phrase “apply a function to a matrix” as applying that function separately to every entry. Generally, that is *not* what we mean. The correct construction is about what the matrix does as an operator, and the spectral theorem supplies the key.

## Start with one eigenvector

Suppose A has an eigenvector v with eigenvalue three. Applying A to v multiplies it by three. Applying A twice multiplies it by nine. Applying A three times multiplies it by twenty-seven.

Now take a polynomial, say the function that maps a number t to t squared plus one. The operator A squared plus the identity sends v to ten times v, because three squared plus one is ten.

For every eigenvector, the polynomial expression acts by evaluating the polynomial at its eigenvalue.

This is our clue. Rather than calculating a function entry by entry, we should ask what it does to each eigenspace.

## From eigenvectors to spectral projections

The finite spectral theorem tells us that a self-adjoint operator has mutually orthogonal eigenspaces whose direct sum is the whole space. Let the distinct eigenvalues be the numbers in a finite set, and let each eigenvalue have its orthogonal spectral projection.

We can recover A by multiplying each spectral projection by its eigenvalue and adding the results.

Now suppose f is a real-valued function defined on those eigenvalues. Define f of A in the same way, except replace each eigenvalue by its value under f.

If a vector belongs to the eigenspace for three, f of A multiplies it by f of three. If a vector lies in several eigenspaces at once, split it into its perpendicular components, apply the relevant multipliers, and reassemble it.

This definition does not depend on which eigenvectors we choose to describe an eigenspace. It depends only on the operator and its spectral projections. That's what makes it coordinate-free.

## A concrete two-dimensional calculation

Consider the symmetric matrix with two on both diagonal entries and one in each off-diagonal entry. You can think of it as taking a vector, doubling its coordinates, and adding the other coordinate to each one.

Its eigenvector in the direction one, one has eigenvalue three. Its eigenvector in the direction one, negative one has eigenvalue one.

Take the function f of t equals t squared. Our definition says f of A multiplies the first eigendirection by nine and the second by one.

If we instead multiply the original matrix by itself, we get a matrix with five on the diagonal and four off the diagonal. Check what that matrix does to the same two directions: it multiplies one, one by nine and one, negative one by one.

The two descriptions agree. Spectral functional calculus extends the polynomial calculation we already understand; it does not replace it with an unrelated rule.

What about the reciprocal function, one divided by t? Both eigenvalues are nonzero, so we can divide each eigenvalue. The resulting operator is A inverse. In our example, its matrix is one third times the matrix with two on the diagonal and negative one off the diagonal.

Again, this is not the entrywise reciprocal. The off-diagonal entries of the original matrix were positive one, but the off-diagonal entries of the inverse are negative one third.

## Why the algebra works

Let's prove some of the main rules, rather than taking them as convenient notation.

Suppose f and g are two real-valued functions on the spectrum. Consider an eigenvector of A with eigenvalue lambda.

The operator f of A acts on that vector by f of lambda. The operator g of A acts by g of lambda. So their sum acts by f of lambda plus g of lambda. That is exactly how the function f plus g acts on lambda. Therefore the sum of the two operators equals the operator associated with f plus g.

Similarly, applying g of A and then f of A multiplies the same eigendirection by g of lambda and then f of lambda. The result is the product of those two numbers. That is why f of A times g of A equals the operator associated with the product function f times g.

These equalities hold on every eigenspace. Since the eigenspaces span the space, the operator equalities hold everywhere.

We can also read off the eigenvalues of f of A. They are the values f takes on the eigenvalues of A, with possible collisions: two different eigenvalues of A can become the *same* eigenvalue of f of A.

For example, if A has eigenvalues negative two and two, squaring sends both to four. Then A squared can equal four times the identity, even though A was not itself a scalar multiple of the identity.

That last example shows how applying a function can lose information. Knowing f of A may not let us recover A.

## Can any function be represented by a polynomial?

In finite dimensions, for self-adjoint A, yes—*as far as its action on A is concerned*.

Suppose A has three distinct eigenvalues. We can build a polynomial that equals any requested set of three values at those three points. The standard construction makes one polynomial for each eigenvalue. It equals one at that chosen eigenvalue and zero at the other two. A weighted sum of those polynomials then matches any requested function values on the spectrum.

These are called Lagrange interpolation polynomials. Notice that the function does not need to be a polynomial everywhere on the real line. We only require agreement on the finite list of eigenvalues.

As a result, every finite-dimensional self-adjoint functional calculus can be expressed by a polynomial in A. That proves, in particular, that f of A commutes with A.

It also gives another way to understand the spectral projectors for a self-adjoint matrix. Choose a function that takes value one on selected eigenvalues and zero on the others. Its operator is precisely the spectral projection onto the selected eigenspaces.

For finite spectra, it does not matter if this selection function jumps abruptly between zero and one on the real line: we can interpolate its values exactly at the finitely many relevant points.

## Where continuity enters later

Infinite-dimensional operators bring a new difficulty. The spectrum may contain infinitely many points or an entire interval. We can no longer assume a polynomial can match an arbitrary function at every spectral point.

For a bounded self-adjoint operator, one route begins by approximating a *continuous* real-valued function uniformly by polynomials on an interval containing the spectrum. The operator norm then lets us pass from the polynomial expressions to a limiting operator. We will prove the relevant approximation and convergence statements when we build continuous functional calculus in detail.

Functions with jumps, such as the indicator of a spectral interval, need additional machinery in that setting. This is why projection-valued measures and Borel functional calculus will eventually appear in our course.

For now, the finite construction is complete and fully justified by the finite spectral theorem.

## A function can reveal a property of the operator

Suppose every eigenvalue of A is nonnegative. Then f of A is nonnegative in the spectral sense whenever f is nonnegative on the spectrum, because its multipliers on each eigenspace are nonnegative.

This is the key that will allow us to build positive square roots. To take a square root of a positive operator, we will take the nonnegative square root of each eigenvalue and reassemble the operator through the spectral projections.

But before we do that, we need to explain rigorously what it means for an operator itself to be positive.

For a final reconstruction exercise, take a symmetric two-by-two matrix with eigenvalues one and three. Describe the action of its square, inverse, and spectral projector onto the three-eigenspace without writing the original matrix entries. Then prove the multiplication rule for functions of A by testing it on an arbitrary eigenbasis.

If you can do that, you understand why functional calculus is a property of the operator rather than of its chosen coordinates.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For finite-dimensional self-adjoint \(A=\sum_{\lambda\in\sigma(A)}\lambda P_\lambda\) over \(\mathbb R\) or \(\mathbb C\), where each distinct eigenvalue has its full eigenspace projector, define

\[
f(A)=\sum_{\lambda\in\sigma(A)} f(\lambda)P_\lambda.
\]

If \(f,g\) are real-valued on the spectrum, then \((f+g)(A)=f(A)+g(A)\), \((fg)(A)=f(A)g(A)\), and \(f(A)\) is self-adjoint. An arbitrary finite assignment of real function values to distinct eigenvalues equals the values of some real polynomial on those points (Lagrange interpolation). For \(f(t)=1/t\) on a spectrum avoiding zero, \(f(A)=A^{-1}\). For \(f=\mathbf 1_S\) on the finite spectrum, \(f(A)=P_A(S)\).

**Lean bridge.** The DKPS staging module `ForTauCeti/Analysis/InnerProductSpace/SelfAdjointFunctionalCalculus.lean` builds on the accepted finite symmetric calculus. This is an exact existing declaration signature and proof:

```lean
theorem cfc_congr_operator {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (h : T = S) (f : ℝ → ℝ) :
    LinearMap.IsSymmetric.cfc hT f = LinearMap.IsSymmetric.cfc hS f := by
  subst h
  rfl
```

`T.IsSymmetric` is the proof of symmetry of the finite operator; `cfc` produces the operator represented by applying the real-valued function to the spectrum. The theorem states that the resulting operator depends on the underlying operator rather than on the particular witness of symmetry. It does **not**, by itself, prove all algebraic laws; those are provided by the accepted calculus imported into this module and are mathematically derived in the spoken lesson.

The finite matrix threshold selector from `ForTauCeti/Analysis/Matrix/SpectralProjection.lean` uses the same construction with an indicator function:

```lean
noncomputable def spectralProjectionIci (c : ℝ) (A : Matrix (Fin n) (Fin n) 𝕜)
    (_hA : A.IsHermitian) : Matrix (Fin n) (Fin n) 𝕜 :=
  cfc (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) A
```

`Set.Ici c` includes its lower endpoint; the indicator is one on the selected set and zero elsewhere. This excerpt is from the finite matrix API and should not be mistaken for a claim that the infinite-dimensional Borel calculus has already been developed.

**Reconstruction:** Prove \((fg)(A)=f(A)g(A)\) from \(P_\lambda P_\mu=0\) for \(\lambda\ne\mu\) and \(P_\lambda^2=P_\lambda\). Construct an interpolating polynomial for two distinct eigenvalues, and explain why multiplicity requires selecting the entire eigenspace.
